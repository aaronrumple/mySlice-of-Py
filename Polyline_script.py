# -*- coding: utf-8 -*-
"""
Polyine Curve Builder - Combined Open/Closed Fit/Spline Curve Tool
Production pyRevit / IronPython 2.7 script

Purpose:
    Combines these four previous tools into one command:
        - Pline Open Fit Curve
        - Pline Closed Fit Curve
        - Pline Open Spline Curve
        - Pline Closed Spline Curve

What it does:
    1. Uses the current selection, or prompts for model/detail curve elements.
    2. Orders the selected curves into one connected chain.
    3. Automatically detects whether that chain is open or closed.
    4. Shows one standard WPF dialog for:
        - Model Lines or Detail Lines output
        - Fit Curve or Spline Curve construction
    5. Creates editable Revit curve output where Revit/Dynamo allows it.

Notes:
    - Fit Curve no longer calls Dynamo ProtoGeometry NurbsCurve.ByPoints,
      avoiding protected-memory crashes seen when ProtoGeometry is hosted
      directly from pyRevit IronPython.
    - Fit Curve first tries to use AutoCAD Core Console to run the real
      PEDIT Fit engine on a temporary polyline, then reads the resulting
      curve-fit vertices and bulges back into editable Revit Arc/Line pieces.
    - If AutoCAD Core Console is not available or fails, Fit Curve falls back
      to the native G1 biarc approximation so the command still runs.
    - Spline Curve uses the ordered vertices as control points. Open spline output
      uses native Revit NurbSpline.CreateCurve. Closed spline output uses Dynamo
      NurbsCurve.ByControlPoints(..., closeCurve=True) and splits the result at 0.5,
      matching the previous closed Dynamo workflow.
    - Original selected curves are not deleted.

Author: Aaron Rumple, AIA
Compatible target: Revit 2022-2027, pyRevit IronPython 2.7
Version: 5.14.0
"""

from __future__ import print_function

import os
import sys
import traceback
import math
import tempfile
import time
import shutil

import clr

clr.AddReference("RevitAPI")
clr.AddReference("RevitAPIUI")
clr.AddReference("PresentationFramework")
clr.AddReference("PresentationCore")
clr.AddReference("WindowsBase")
clr.AddReference("System.Xml")

from Autodesk.Revit.DB import Arc
from Autodesk.Revit.DB import CurveElement
from Autodesk.Revit.DB import DetailCurve
from Autodesk.Revit.DB import FailureProcessingResult
from Autodesk.Revit.DB import FailureSeverity
from Autodesk.Revit.DB import IFailuresPreprocessor
from Autodesk.Revit.DB import Line
from Autodesk.Revit.DB import ModelCurve
from Autodesk.Revit.DB import NurbSpline
from Autodesk.Revit.DB import Plane
from Autodesk.Revit.DB import SketchPlane
from Autodesk.Revit.DB import Transaction
from Autodesk.Revit.DB import TransactionGroup
from Autodesk.Revit.DB import ViewType
from Autodesk.Revit.DB import XYZ
from Autodesk.Revit.Exceptions import OperationCanceledException
from Autodesk.Revit.UI.Selection import ISelectionFilter
from Autodesk.Revit.UI.Selection import ObjectType

from System import Array
from System import Double
from System.IO import StringReader
from System.Xml import XmlReader
from System.Windows.Markup import XamlReader
from System.Collections.Generic import List

from pyrevit import forms
from pyrevit import script


# -----------------------------------------------------------------------------
# Configuration
# -----------------------------------------------------------------------------

TOOL_NAME = "Polyline Curve Builder"
VERSION = "5.14.0"
AUTHOR = "Aaron Rumple, AIA"

JOIN_TOLERANCE_FT = 0.001
CLOSED_CHAIN_TOLERANCE_FT = 0.001
SPLIT_NORMALIZED_PARAMETER = 0.5
NURBS_DEGREE = 3
MIN_OUTPUT_CURVE_LENGTH_FT = 0.003
SUPPRESS_TRANSACTION_WARNINGS = True

OUTPUT_MODEL_LINES = "Model Lines"
OUTPUT_DETAIL_LINES = "Detail Lines"
METHOD_FIT_CURVE = "Fit Curve"
METHOD_SPLINE_CURVE = "Spline Curve"
CHAIN_OPEN = "Open"
CHAIN_CLOSED = "Closed"

AUTOCAD_CORE_CONSOLE_TIMEOUT_SECONDS = 60
AUTOCAD_CORE_CONSOLE_ENV_NAMES = ("ACCORECONSOLE_EXE", "AUTOCAD_CORE_CONSOLE")
AUTOCAD_CURVE_FIT_RESULT_NAME = "pyrevit_acad_curve_fit_result.txt"
AUTOCAD_CURVE_FIT_INPUT_NAME = "pyrevit_acad_curve_fit_input.dxf"
AUTOCAD_CURVE_FIT_SCRIPT_NAME = "pyrevit_acad_curve_fit.scr"
AUTOCAD_CURVE_FIT_LISP_NAME = "pyrevit_acad_curve_fit.lsp"
AUTOCAD_CURVE_FIT_BATCH_NAME = "pyrevit_acad_curve_fit_run.bat"
AUTOCAD_CURVE_FIT_LOG_NAME = "pyrevit_acad_curve_fit_lisp_log.txt"
AUTOCAD_CURVE_FIT_STDOUT_NAME = "pyrevit_acad_curve_fit_accore_stdout.txt"
AUTOCAD_CURVE_FIT_STDERR_NAME = "pyrevit_acad_curve_fit_accore_stderr.txt"
BULGE_ARC_TOLERANCE = 1.0e-10


# -----------------------------------------------------------------------------
# pyRevit globals
# -----------------------------------------------------------------------------

uidoc = __revit__.ActiveUIDocument
uiapp = __revit__
app = uiapp.Application
if app and hasattr(app, "ShortCurveTolerance"):
    try:
        MIN_OUTPUT_CURVE_LENGTH_FT = max(MIN_OUTPUT_CURVE_LENGTH_FT, app.ShortCurveTolerance)
    except Exception:
        pass

doc = uidoc.Document
output = script.get_output()
logger = script.get_logger()


# -----------------------------------------------------------------------------
# Exceptions and failure processing
# -----------------------------------------------------------------------------

class UserCancelled(Exception):
    pass


class ScriptValidationError(Exception):
    pass


class WarningSwallower(IFailuresPreprocessor):
    def __init__(self):
        self.error_messages = []

    def PreprocessFailures(self, failures_accessor):
        has_error = False
        try:
            messages = failures_accessor.GetFailureMessages()
            for message in messages:
                try:
                    severity = message.GetSeverity()
                except Exception:
                    severity = None

                if severity == FailureSeverity.Warning:
                    try:
                        failures_accessor.DeleteWarning(message)
                    except Exception:
                        pass
                elif severity == FailureSeverity.Error:
                    has_error = True
                    try:
                        self.error_messages.append(message.GetDescriptionText())
                    except Exception:
                        self.error_messages.append("Revit reported an error during curve creation.")
        except Exception:
            pass

        if has_error:
            # Prevent the modal Revit failure dialog. The transaction code checks
            # for rollback and reports the problem in pyRevit output instead.
            return FailureProcessingResult.ProceedWithRollBack

        return FailureProcessingResult.Continue


# -----------------------------------------------------------------------------
# Dynamo bridge
# -----------------------------------------------------------------------------

DSPoint = None
DSCurve = None
DSNurbsCurve = None
_DYNAMO_LOADED = False
_DYNAMO_LOAD_MESSAGE = ""


def _add_path(path_value):
    if path_value and os.path.isdir(path_value) and path_value not in sys.path:
        sys.path.append(path_value)


def _candidate_dynamo_dirs():
    """Return likely Dynamo for Revit assembly folders for the active Revit."""
    candidates = []
    version = ""
    try:
        version = str(app.VersionNumber)
    except Exception:
        version = ""

    program_files = os.environ.get("ProgramFiles", r"C:\Program Files")
    program_files_x86 = os.environ.get("ProgramFiles(x86)", r"C:\Program Files (x86)")
    program_data = os.environ.get("ProgramData", r"C:\ProgramData")

    revit_roots = []
    if version:
        revit_roots.append(os.path.join(program_files, "Autodesk", "Revit {0}".format(version)))
        revit_roots.append(os.path.join(program_files_x86, "Autodesk", "Revit {0}".format(version)))

    for revit_root in revit_roots:
        dfr = os.path.join(revit_root, "AddIns", "DynamoForRevit")
        candidates.append(dfr)
        candidates.append(os.path.join(dfr, "Revit"))
        candidates.append(os.path.join(dfr, "DynamoCore"))
        candidates.append(os.path.join(dfr, "DynamoCore", "bin"))
        candidates.append(os.path.join(dfr, "DynamoCore", "2"))
        candidates.append(os.path.join(dfr, "DynamoCore", "3"))

    if version:
        dfr_program_data = os.path.join(program_data, "Autodesk", "Revit", "Addins", version, "DynamoForRevit")
        candidates.append(dfr_program_data)
        candidates.append(os.path.join(dfr_program_data, "Revit"))
        candidates.append(os.path.join(dfr_program_data, "DynamoCore"))
        candidates.append(os.path.join(dfr_program_data, "DynamoCore", "bin"))

    candidates.append(os.path.join(program_files, "Dynamo", "Dynamo Revit"))
    candidates.append(os.path.join(program_files, "Dynamo", "Dynamo Core"))
    candidates.append(os.path.join(program_files_x86, "Dynamo", "Dynamo Revit"))
    candidates.append(os.path.join(program_files_x86, "Dynamo", "Dynamo Core"))

    expanded = []
    for candidate in candidates:
        expanded.append(candidate)
        try:
            if os.path.isdir(candidate):
                for name in os.listdir(candidate):
                    child = os.path.join(candidate, name)
                    if os.path.isdir(child):
                        expanded.append(child)
        except Exception:
            pass

    seen = set()
    final_dirs = []
    for path_value in expanded:
        key = path_value.lower()
        if key not in seen:
            seen.add(key)
            final_dirs.append(path_value)
    return final_dirs


def _find_assembly_file(file_name, search_dirs):
    for folder in search_dirs:
        try:
            path_value = os.path.join(folder, file_name)
            if os.path.isfile(path_value):
                return path_value
        except Exception:
            pass
    return None


def _add_reference(name, file_name, search_dirs):
    try:
        clr.AddReference(name)
        return
    except Exception:
        pass

    assembly_path = _find_assembly_file(file_name, search_dirs)
    if assembly_path:
        clr.AddReferenceToFileAndPath(assembly_path)
        return

    raise ScriptValidationError(
        "Could not load Dynamo assembly {0}. Make sure Dynamo for Revit is installed for this Revit version.".format(file_name)
    )


def load_dynamo_bridge():
    """Load ProtoGeometry and RevitNodes for Dynamo-compatible NURBS creation."""
    global DSPoint
    global DSCurve
    global DSNurbsCurve
    global _DYNAMO_LOADED
    global _DYNAMO_LOAD_MESSAGE

    if _DYNAMO_LOADED:
        return

    search_dirs = _candidate_dynamo_dirs()
    for path_value in search_dirs:
        _add_path(path_value)

    try:
        _add_reference("ProtoGeometry", "ProtoGeometry.dll", search_dirs)
        _add_reference("RevitNodes", "RevitNodes.dll", search_dirs)

        import Revit
        clr.ImportExtensions(Revit.GeometryConversion)

        from Autodesk.DesignScript.Geometry import Point as _DSPoint
        from Autodesk.DesignScript.Geometry import Curve as _DSCurve
        from Autodesk.DesignScript.Geometry import NurbsCurve as _DSNurbsCurve

        DSPoint = _DSPoint
        DSCurve = _DSCurve
        DSNurbsCurve = _DSNurbsCurve

        _DYNAMO_LOADED = True
        _DYNAMO_LOAD_MESSAGE = "Loaded ProtoGeometry and RevitNodes."
    except ScriptValidationError:
        raise
    except Exception as ex:
        raise ScriptValidationError(
            "Could not initialize Dynamo geometry conversion. {0}".format(ex)
        )


def dispose_ds(value):
    """Dispose DesignScript geometry objects to avoid holding Dynamo geometry."""
    if value is None:
        return
    try:
        if isinstance(value, (list, tuple)):
            for item in value:
                dispose_ds(item)
            return
    except Exception:
        pass
    try:
        for item in value:
            dispose_ds(item)
        return
    except Exception:
        pass
    try:
        value.Dispose()
    except Exception:
        pass


def make_ds_point_direct(xyz):
    try:
        return DSPoint.ByCoordinates(float(xyz.X), float(xyz.Y), float(xyz.Z))
    except Exception as ex:
        raise ScriptValidationError("Could not create a Dynamo point from a Revit XYZ. {0}".format(ex))


def make_designscript_points(xyz_points, prefer_revitnodes_conversion):
    """Convert XYZ points to DesignScript points.

    Fit Curve uses direct coordinates, matching the previous fitted-curve scripts.
    Closed control-point spline may prefer RevitNodes conversion, matching the
    previous closed spline script. If that conversion fails for any point, fall
    back to direct coordinates for the entire point set so units are not mixed.
    """
    load_dynamo_bridge()

    if prefer_revitnodes_conversion:
        converted = []
        try:
            for point in xyz_points:
                converted.append(point.ToPoint())
            return converted, True
        except Exception:
            dispose_ds(converted)

    ds_points = []
    for point in xyz_points:
        ds_points.append(make_ds_point_direct(point))

    return ds_points, False


def make_ds_point_array(ds_points):
    try:
        return Array[DSPoint](ds_points)
    except Exception:
        return ds_points


def make_double_array(values):
    try:
        return Array[Double](values)
    except Exception:
        return values


def flatten_any(value):
    result = []
    if value is None:
        return result
    try:
        if DSCurve is not None and isinstance(value, DSCurve):
            return [value]
    except Exception:
        pass
    try:
        for item in value:
            result.extend(flatten_any(item))
        return result
    except Exception:
        return [value]


def ds_curve_to_revit_curve(ds_curve, prefer_converted_units):
    """Convert a DesignScript curve to DB.Curve with safe overload fallbacks."""
    errors = []
    if prefer_converted_units:
        overloads = ((), (True,), (False,))
    else:
        overloads = ((), (False,), (True,))

    for args in overloads:
        try:
            return ds_curve.ToRevitType(*args)
        except Exception as ex:
            errors.append(str(ex))

    raise ScriptValidationError(
        "Could not convert the Dynamo NURBS curve back to Revit curve geometry. {0}".format(" | ".join(errors))
    )


def force_revit_nurb_spline(revit_curve):
    """Return a DB.NurbSpline where possible so Revit creates editable spline elements."""
    if revit_curve is None:
        raise ScriptValidationError("The converted Revit curve was null.")

    try:
        type_name = revit_curve.GetType().Name
    except Exception:
        type_name = "Unknown"

    if type_name == "NurbSpline":
        return revit_curve

    if type_name == "HermiteSpline":
        try:
            nurb_curve = NurbSpline.CreateCurve(revit_curve)
            try:
                if nurb_curve.GetType().Name != "NurbSpline":
                    raise ScriptValidationError(
                        "HermiteSpline conversion returned {0}, not NurbSpline.".format(nurb_curve.GetType().Name)
                    )
            except ScriptValidationError:
                raise
            except Exception:
                pass
            return nurb_curve
        except ScriptValidationError:
            raise
        except Exception as ex:
            raise ScriptValidationError(
                "Could not convert Dynamo/Revit HermiteSpline to editable Revit NurbSpline. {0}".format(ex)
            )

    # Lines are valid only for tiny degenerate control splines; Fit Curve should not return these.
    if type_name == "Line":
        return revit_curve

    raise ScriptValidationError(
        "Dynamo curve conversion returned {0}. Expected NurbSpline or HermiteSpline.".format(type_name)
    )


# -----------------------------------------------------------------------------
# WPF option dialog
# -----------------------------------------------------------------------------

def ask_output_options(detected_chain_type, endpoint_gap, source_count):
    xaml = r"""
<Window xmlns="http://schemas.microsoft.com/winfx/2006/xaml/presentation"
        Title="Polyline Curve Builder"
        Height="445"
        MinHeight="445"
        Width="430"
        MinWidth="430"
        WindowStartupLocation="CenterScreen"
        ResizeMode="NoResize"
        ShowInTaskbar="False">
    <Grid Margin="14">
        <Grid.RowDefinitions>
            <RowDefinition Height="Auto"/>
            <RowDefinition Height="Auto"/>
            <RowDefinition Height="Auto"/>
            <RowDefinition Height="Auto"/>
            <RowDefinition Height="Auto"/>
        </Grid.RowDefinitions>

        <Border Grid.Row="0" BorderBrush="#FF777777" BorderThickness="1" CornerRadius="3" Padding="8" Margin="0,0,0,10">
            <StackPanel>
                <TextBlock Name="txtDetected" FontWeight="Bold" Text="Detected chain: Open"/>
                <TextBlock Name="txtGap" Margin="0,3,0,0" Text="Endpoint gap: 0.000000 ft"/>
                <TextBlock Name="txtSource" Margin="0,3,0,0" Text="Source curves: 0"/>
            </StackPanel>
        </Border>

        <GroupBox Grid.Row="1" Header="Output Type" Margin="0,0,0,10">
            <StackPanel Margin="8">
                <RadioButton Name="rbModel" Content="Model Lines" IsChecked="True" Margin="0,2,0,7"/>
                <RadioButton Name="rbDetail" Content="Detail Lines" Margin="0,2,0,0"/>
            </StackPanel>
        </GroupBox>

        <GroupBox Grid.Row="2" Header="Curve Type" Margin="0,0,0,10">
            <StackPanel Margin="8">
                <RadioButton Name="rbFit" Content="Fit Curve  - AutoCAD PEDIT Fit tangent arcs" IsChecked="True" Margin="0,2,0,7"/>
                <RadioButton Name="rbSpline" Content="Spline Curve  - ordered vertices are control points" Margin="0,2,0,0"/>
            </StackPanel>
        </GroupBox>

        <Border Grid.Row="3" Padding="2" Margin="0,0,0,12">
            <StackPanel>
                <TextBlock Text="Open/closed detection is automatic from the ordered chain endpoints."
                           TextWrapping="Wrap"
                           Foreground="#FF555555"/>
                <TextBlock Text="Closed output is split only where needed for Revit-compatible editable spline pieces."
                           TextWrapping="Wrap"
                           Foreground="#FF555555"
                           Margin="0,4,0,0"/>
            </StackPanel>
        </Border>

        <Border Grid.Row="4" BorderBrush="#FFCCCCCC" BorderThickness="0,1,0,0" Padding="0,12,0,0">
            <StackPanel Orientation="Horizontal" HorizontalAlignment="Right">
                <Button Name="btnOK" Content="OK" Width="86" Height="26" Margin="0,0,8,0" IsDefault="True"/>
                <Button Name="btnCancel" Content="Cancel" Width="86" Height="26" IsCancel="True"/>
            </StackPanel>
        </Border>
    </Grid>
</Window>
"""

    reader = None
    xml_reader = None
    try:
        reader = StringReader(xaml)
        xml_reader = XmlReader.Create(reader)
        window = XamlReader.Load(xml_reader)

        rb_model = window.FindName("rbModel")
        rb_fit = window.FindName("rbFit")
        txt_detected = window.FindName("txtDetected")
        txt_gap = window.FindName("txtGap")
        txt_source = window.FindName("txtSource")
        btn_ok = window.FindName("btnOK")
        btn_cancel = window.FindName("btnCancel")

        txt_detected.Text = "Detected chain: {0}".format(detected_chain_type)
        txt_gap.Text = "Endpoint gap: {0:.6f} ft".format(endpoint_gap)
        txt_source.Text = "Source curves: {0}".format(source_count)

        def on_ok(sender, args):
            window.DialogResult = True

        def on_cancel(sender, args):
            window.DialogResult = False

        btn_ok.Click += on_ok
        btn_cancel.Click += on_cancel

        result = window.ShowDialog()
        if result:
            output_mode = OUTPUT_MODEL_LINES if rb_model.IsChecked else OUTPUT_DETAIL_LINES
            curve_method = METHOD_FIT_CURVE if rb_fit.IsChecked else METHOD_SPLINE_CURVE
            return output_mode, curve_method

        raise UserCancelled("Curve builder options cancelled.")
    except UserCancelled:
        raise
    except Exception as ex:
        raise ScriptValidationError("Could not show the curve builder option dialog. {0}".format(ex))
    finally:
        try:
            if xml_reader:
                xml_reader.Close()
        except Exception:
            pass
        try:
            if reader:
                reader.Close()
        except Exception:
            pass


# -----------------------------------------------------------------------------
# Selection helpers
# -----------------------------------------------------------------------------

class CurveSelectionFilter(ISelectionFilter):
    def AllowElement(self, element):
        return isinstance(element, CurveElement)

    def AllowReference(self, reference, point):
        return False


def collect_selected_curve_elements(document, active_uidoc):
    model_curves = []
    detail_curves = []
    skipped_ids = []

    selected_ids = list(active_uidoc.Selection.GetElementIds())

    if not selected_ids:
        try:
            picked_refs = active_uidoc.Selection.PickObjects(
                ObjectType.Element,
                CurveSelectionFilter(),
                "Select connected model lines or detail lines, then click Finish"
            )
            selected_ids = [ref.ElementId for ref in picked_refs]
        except OperationCanceledException:
            raise UserCancelled("Selection cancelled.")

    for element_id in selected_ids:
        element = document.GetElement(element_id)
        if isinstance(element, ModelCurve):
            model_curves.append(element)
        elif isinstance(element, DetailCurve):
            detail_curves.append(element)
        else:
            skipped_ids.append(element_id)

    return model_curves, detail_curves, skipped_ids


def get_element_link(element_id):
    try:
        return output.linkify(element_id)
    except Exception:
        try:
            return str(element_id.IntegerValue)
        except Exception:
            return str(element_id)


def safe_type_name(element):
    try:
        return element.GetType().Name
    except Exception:
        return "Unavailable"


def snapshot_source_report_rows(source_elements):
    rows = []
    for source in source_elements:
        try:
            element_id = source.Id
        except Exception:
            element_id = None
        try:
            length_text = "{0:.6f}".format(curve_length(source.GeometryCurve))
        except Exception:
            length_text = "Unavailable"
        rows.append([get_element_link(element_id), safe_type_name(source), length_text])
    return rows


def snapshot_created_report_rows(created_elements):
    rows = []
    for created in created_elements:
        try:
            element_id = created.Id
        except Exception:
            element_id = None
        rows.append([get_element_link(element_id), safe_type_name(created)])
    return rows


# -----------------------------------------------------------------------------
# General geometry helpers
# -----------------------------------------------------------------------------

def xyz_distance(point_a, point_b):
    return point_a.DistanceTo(point_b)


def xyz_is_close(point_a, point_b, tolerance):
    return xyz_distance(point_a, point_b) <= tolerance


def curve_length(curve):
    try:
        return float(curve.Length)
    except Exception:
        return 0.0


def get_curve_start(curve):
    return curve.GetEndPoint(0)


def get_curve_end(curve):
    return curve.GetEndPoint(1)


def curve_reversed(curve):
    try:
        return curve.CreateReversed()
    except Exception:
        raise ScriptValidationError("One selected curve type could not be reversed.")


def get_curve_clone(curve_element):
    try:
        return curve_element.GeometryCurve.Clone()
    except Exception:
        raise ScriptValidationError(
            "Could not read geometry from curve element {0}.".format(curve_element.Id.IntegerValue)
        )


def remove_consecutive_duplicate_points(points, tolerance):
    cleaned = []
    for point in points:
        if not cleaned:
            cleaned.append(point)
        elif not xyz_is_close(cleaned[-1], point, tolerance):
            cleaned.append(point)
    return cleaned


def remove_closing_duplicate_point(points, tolerance):
    if len(points) > 2 and xyz_is_close(points[0], points[-1], tolerance):
        return points[:-1]
    return points


def count_unique_points(points, tolerance):
    unique_points = []
    for point in points:
        duplicate = False
        for existing in unique_points:
            if xyz_is_close(point, existing, tolerance):
                duplicate = True
                break
        if not duplicate:
            unique_points.append(point)
    return len(unique_points)


def make_xyz_list(points):
    point_list = List[XYZ]()
    for point in points:
        point_list.Add(point)
    return point_list


def make_double_list(values):
    value_list = List[Double]()
    for value in values:
        value_list.Add(float(value))
    return value_list


# -----------------------------------------------------------------------------
# Plane helpers
# -----------------------------------------------------------------------------

def get_sketch_plane_for_model_curves(model_curves):
    for curve_element in model_curves:
        try:
            sketch_plane = curve_element.SketchPlane
            if sketch_plane is not None:
                return sketch_plane
        except Exception:
            pass
    return None


def get_plane_from_sketch_plane(sketch_plane):
    if sketch_plane is None:
        return None
    try:
        return sketch_plane.GetPlane()
    except Exception:
        raise ScriptValidationError("Could not read the model curve sketch plane.")


def get_active_view_plane(active_view):
    if active_view is None:
        raise ScriptValidationError("No active view was available for model curve creation.")
    try:
        if active_view.ViewType == ViewType.DraftingView:
            raise ScriptValidationError(
                "Model Lines cannot be created from a Drafting View. Choose Detail Lines, "
                "or run the command from a model view with a valid work plane."
            )
    except ScriptValidationError:
        raise
    except Exception:
        pass
    try:
        return Plane.CreateByNormalAndOrigin(active_view.ViewDirection, active_view.Origin)
    except Exception as ex:
        raise ScriptValidationError(
            "Could not determine a model-space plane from the active view. {0}".format(ex)
        )


def get_model_output_sketch_plane_info(source_model_curves, active_view):
    sketch_plane = get_sketch_plane_for_model_curves(source_model_curves)
    if sketch_plane is not None:
        return sketch_plane, get_plane_from_sketch_plane(sketch_plane)
    return None, get_active_view_plane(active_view)


def get_or_create_sketch_plane(document, sketch_plane, plane):
    if sketch_plane is not None:
        return sketch_plane
    if plane is None:
        raise ScriptValidationError("No valid plane was found for model curve creation.")
    try:
        return SketchPlane.Create(document, plane)
    except Exception as ex:
        raise ScriptValidationError("Could not create a sketch plane for model lines. {0}".format(ex))


def point_plane_distance(point, plane):
    vector = XYZ(
        point.X - plane.Origin.X,
        point.Y - plane.Origin.Y,
        point.Z - plane.Origin.Z
    )
    return abs(vector.DotProduct(plane.Normal))


def validate_points_on_plane(points, plane, tolerance):
    if plane is None:
        raise ScriptValidationError("No valid plane was found for model curve creation.")

    max_distance = 0.0
    for point in points:
        distance = point_plane_distance(point, plane)
        if distance > max_distance:
            max_distance = distance

    if max_distance > tolerance:
        raise ScriptValidationError(
            "The selected curves are not coplanar with the model-line output plane. "
            "Maximum point-to-plane distance: {0:.6f} ft.".format(max_distance)
        )


def get_preferred_line_style(curve_elements):
    for curve_element in curve_elements:
        try:
            style = curve_element.LineStyle
            if style is not None:
                return style
        except Exception:
            pass
    return None


# -----------------------------------------------------------------------------
# Chain ordering and detection
# -----------------------------------------------------------------------------

def build_curve_items(curve_elements):
    items = []
    for curve_element in curve_elements:
        curve = get_curve_clone(curve_element)
        if curve_length(curve) <= MIN_OUTPUT_CURVE_LENGTH_FT:
            raise ScriptValidationError(
                "Selected curve {0} is too short to process safely.".format(curve_element.Id.IntegerValue)
            )
        items.append({
            "element": curve_element,
            "curve": curve
        })
    return items


def best_connection_to_chain(chain, item):
    front_start = get_curve_start(chain[0]["curve"])
    back_end = get_curve_end(chain[-1]["curve"])
    curve = item["curve"]
    start = get_curve_start(curve)
    end = get_curve_end(curve)

    candidates = []
    candidates.append({"mode": "append", "reverse": False, "distance": xyz_distance(back_end, start)})
    candidates.append({"mode": "append", "reverse": True, "distance": xyz_distance(back_end, end)})
    candidates.append({"mode": "prepend", "reverse": False, "distance": xyz_distance(front_start, end)})
    candidates.append({"mode": "prepend", "reverse": True, "distance": xyz_distance(front_start, start)})
    candidates.sort(key=lambda candidate: candidate["distance"])
    return candidates[0]


def order_curves_into_single_chain(curve_elements, join_tolerance):
    items = build_curve_items(curve_elements)

    if not items:
        raise ScriptValidationError("Select at least one model/detail curve.")

    remaining = list(items)
    chain = [remaining.pop(0)]

    while remaining:
        best_index = None
        best_candidate = None

        for index, item in enumerate(remaining):
            candidate = best_connection_to_chain(chain, item)
            if best_candidate is None or candidate["distance"] < best_candidate["distance"]:
                best_index = index
                best_candidate = candidate

        if best_candidate is None or best_candidate["distance"] > join_tolerance:
            gap = -1.0
            if best_candidate is not None:
                gap = best_candidate["distance"]
            raise ScriptValidationError(
                "Selected curves do not form one continuous chain within the join "
                "tolerance of {0:.6f} ft. Nearest open gap found: {1:.6f} ft.".format(
                    join_tolerance,
                    gap
                )
            )

        item = remaining.pop(best_index)
        if best_candidate["reverse"]:
            item = {
                "element": item["element"],
                "curve": curve_reversed(item["curve"])
            }

        if best_candidate["mode"] == "append":
            chain.append(item)
        else:
            chain.insert(0, item)

    return chain


def get_chain_vertex_points(chain, tolerance):
    if not chain:
        raise ScriptValidationError("No ordered curve chain was available.")

    points = [get_curve_start(chain[0]["curve"])]
    for item in chain:
        points.append(get_curve_end(item["curve"]))

    return remove_consecutive_duplicate_points(points, tolerance)


def detect_chain_type(chain, tolerance):
    points = get_chain_vertex_points(chain, tolerance)
    if len(points) < 2:
        raise ScriptValidationError("The selected chain does not contain enough vertices.")
    endpoint_gap = xyz_distance(points[0], points[-1])
    detected = CHAIN_CLOSED if endpoint_gap <= tolerance else CHAIN_OPEN
    return detected, endpoint_gap, points


# -----------------------------------------------------------------------------
# Fit Curve creation: AutoCAD-style smooth tangent circular arcs (G1 biarcs)
# -----------------------------------------------------------------------------

# The earlier v5.5 fit path created practical two-arc pieces, but the internal
# join point was only an averaged handle point. That could create visible kinks
# and "endpoint-to-endpoint" looking arcs. This version uses a true biarc solve:
# each interval between two fit vertices is represented by two circular arcs that
# share a common tangent at the internal matching point.
#
# Math basis: Ryan Juckett, "Biarc Interpolation". The implementation below is
# rewritten for Revit XYZ/Arc creation and IronPython 2.7.

ARC_FIT_EPSILON = 1.0e-9
ARC_FIT_DOT_EPSILON = 1.0e-7
ARC_FIT_MAX_LENGTH_FACTOR = 25.0


def xyz_add(point_a, point_b):
    return XYZ(point_a.X + point_b.X, point_a.Y + point_b.Y, point_a.Z + point_b.Z)


def xyz_subtract(point_a, point_b):
    return XYZ(point_a.X - point_b.X, point_a.Y - point_b.Y, point_a.Z - point_b.Z)


def xyz_scale(vector, factor):
    return XYZ(vector.X * float(factor), vector.Y * float(factor), vector.Z * float(factor))


def xyz_dot(vector_a, vector_b):
    return vector_a.DotProduct(vector_b)


def xyz_cross(vector_a, vector_b):
    return vector_a.CrossProduct(vector_b)


def xyz_length_vector(vector):
    return math.sqrt((vector.X * vector.X) + (vector.Y * vector.Y) + (vector.Z * vector.Z))


def xyz_unit(vector):
    length = xyz_length_vector(vector)
    if length <= ARC_FIT_EPSILON:
        return None
    return xyz_scale(vector, 1.0 / length)


def xyz_negate(vector):
    return XYZ(-vector.X, -vector.Y, -vector.Z)


def xyz_midpoint(point_a, point_b):
    return xyz_scale(xyz_add(point_a, point_b), 0.5)


def xyz_clamp(value, low_value, high_value):
    if value < low_value:
        return low_value
    if value > high_value:
        return high_value
    return value


def sign_nonzero(value):
    return -1.0 if value < 0.0 else 1.0


def remove_all_duplicate_points(points, tolerance):
    """Remove duplicate vertices anywhere in the list while preserving order."""
    cleaned = []
    for point in points:
        duplicate = False
        for existing in cleaned:
            if xyz_is_close(point, existing, tolerance):
                duplicate = True
                break
        if not duplicate:
            cleaned.append(point)
    return cleaned


def get_fit_plane_normal(points):
    """Find a stable normal from the selected points."""
    count = len(points)
    best_normal = None
    best_length = 0.0

    for i in range(count):
        for j in range(i + 1, count):
            v1 = xyz_subtract(points[j], points[i])
            for k in range(j + 1, count):
                v2 = xyz_subtract(points[k], points[i])
                cross = xyz_cross(v1, v2)
                length = xyz_length_vector(cross)
                if length > best_length:
                    best_length = length
                    best_normal = cross

    if best_normal is None or best_length <= ARC_FIT_EPSILON:
        # Degenerate or nearly straight selection. Use the project XY normal.
        return XYZ(0.0, 0.0, 1.0)

    return xyz_unit(best_normal)


def project_vector_to_plane(vector, normal):
    dot_value = xyz_dot(vector, normal)
    projected = xyz_subtract(vector, xyz_scale(normal, dot_value))
    return xyz_unit(projected)


def get_segment_unit(points_for_curve, index_a, index_b):
    return xyz_unit(xyz_subtract(points_for_curve[index_b], points_for_curve[index_a]))


def make_vertex_tangents(points_for_curve, is_closed, normal):
    """Create AutoCAD-like vertex tangents from adjacent segment directions.

    The previous version used next_point - previous_point, which gives long
    segments too much influence. PEDIT-style fit behavior is closer to the
    angular bisector of the incoming and outgoing segment directions, so this
    uses normalized adjacent directions before averaging them.
    """
    tangents = []
    count = len(points_for_curve)

    for index in range(count):
        incoming = None
        outgoing = None

        if is_closed:
            prev_index = (index - 1) % count
            next_index = (index + 1) % count
            incoming = get_segment_unit(points_for_curve, prev_index, index)
            outgoing = get_segment_unit(points_for_curve, index, next_index)
        else:
            if index == 0:
                outgoing = get_segment_unit(points_for_curve, 0, 1)
            elif index == count - 1:
                incoming = get_segment_unit(points_for_curve, count - 2, count - 1)
            else:
                incoming = get_segment_unit(points_for_curve, index - 1, index)
                outgoing = get_segment_unit(points_for_curve, index, index + 1)

        if incoming is not None and outgoing is not None:
            tangent = xyz_unit(xyz_add(incoming, outgoing))
            if tangent is None:
                # 180-degree reversal. Keep the forward direction rather than
                # producing a zero tangent.
                tangent = outgoing
        elif outgoing is not None:
            tangent = outgoing
        elif incoming is not None:
            tangent = incoming
        else:
            tangent = None

        if tangent is not None:
            tangent = project_vector_to_plane(tangent, normal)

        if tangent is None:
            raise ScriptValidationError("Could not calculate a stable tangent for one fit vertex.")

        tangents.append(tangent)

    return tangents


def stabilize_segment_tangent(tangent, chord_unit):
    """Prevent biarcs from looping backward across a chord.

    A real CAD fit can create broad arcs, but a tangent pointing opposite the
    local chord usually indicates a noisy or very sharp vertex. Blending toward
    the chord avoids the large blue loop-back artifacts seen in the v5.5 output.
    """
    if tangent is None or chord_unit is None:
        return chord_unit

    dot_value = xyz_dot(tangent, chord_unit)
    if dot_value < -0.10:
        return chord_unit
    if dot_value < 0.05:
        blended = xyz_unit(xyz_add(tangent, xyz_scale(chord_unit, 0.75)))
        if blended is not None:
            return blended

    return tangent


def compute_arc_data_from_endpoint(point, tangent, point_to_mid):
    """Return circular arc data from an endpoint tangent to a matching point.

    The returned data is intentionally generic. It can represent either a true
    circular arc or a line fallback when the radius is effectively infinite.
    """
    normal = xyz_cross(point_to_mid, tangent)
    perp_axis = xyz_cross(tangent, normal)
    denominator = 2.0 * xyz_dot(perp_axis, point_to_mid)

    if abs(denominator) <= ARC_FIT_EPSILON:
        return {
            "is_line": True,
            "center": xyz_add(point, xyz_scale(point_to_mid, 0.5)),
            "radius": 0.0,
            "angle": 0.0
        }

    center_distance = xyz_dot(point_to_mid, point_to_mid) / denominator
    center = xyz_add(point, xyz_scale(perp_axis, center_distance))
    perp_axis_length = xyz_length_vector(perp_axis)
    radius = abs(center_distance * perp_axis_length)

    if radius <= MIN_OUTPUT_CURVE_LENGTH_FT:
        return {
            "is_line": True,
            "center": xyz_add(point, xyz_scale(point_to_mid, 0.5)),
            "radius": 0.0,
            "angle": 0.0
        }

    inv_radius = 1.0 / radius
    center_to_endpoint = xyz_scale(xyz_subtract(point, center), inv_radius)
    center_to_midpoint = xyz_scale(xyz_add(xyz_subtract(point, center), point_to_mid), inv_radius)
    dot_value = xyz_clamp(xyz_dot(center_to_endpoint, center_to_midpoint), -1.0, 1.0)
    twist = xyz_dot(perp_axis, point_to_mid)
    angle = math.acos(dot_value) * sign_nonzero(twist)

    return {
        "is_line": False,
        "center": center,
        "radius": radius,
        "angle": angle
    }


def point_on_arc_data(center, axis1, axis2, angle):
    return xyz_add(
        xyz_add(center, xyz_scale(axis1, math.cos(angle))),
        xyz_scale(axis2, math.sin(angle))
    )


def make_arc_or_line_from_three_points(start_point, end_point, mid_point):
    if xyz_distance(start_point, end_point) <= MIN_OUTPUT_CURVE_LENGTH_FT:
        return None

    if (xyz_distance(start_point, mid_point) <= MIN_OUTPUT_CURVE_LENGTH_FT or
            xyz_distance(mid_point, end_point) <= MIN_OUTPUT_CURVE_LENGTH_FT):
        try:
            return Line.CreateBound(start_point, end_point)
        except Exception:
            return None

    try:
        return Arc.Create(start_point, end_point, mid_point)
    except Exception:
        try:
            return Line.CreateBound(start_point, end_point)
        except Exception:
            return None


def arc_piece_is_usable(curve, chord_length):
    if curve is None:
        return False
    length = curve_length(curve)
    if length <= MIN_OUTPUT_CURVE_LENGTH_FT:
        return False
    # Extremely long arcs are usually loop-back artifacts. Fall back to a line
    # for that local piece instead of creating a visibly wrong curve.
    if chord_length > MIN_OUTPUT_CURVE_LENGTH_FT and length > chord_length * ARC_FIT_MAX_LENGTH_FACTOR:
        return False
    return True


def create_arc_piece_from_biarc_data(start_point, end_point, center, radius, angle, axis1, axis2):
    chord_length = xyz_distance(start_point, end_point)
    if chord_length <= MIN_OUTPUT_CURVE_LENGTH_FT:
        return None
    if radius <= MIN_OUTPUT_CURVE_LENGTH_FT or abs(angle) <= ARC_FIT_EPSILON:
        try:
            return Line.CreateBound(start_point, end_point)
        except Exception:
            return None

    mid_point = point_on_arc_data(center, axis1, axis2, angle * 0.5)
    curve = make_arc_or_line_from_three_points(start_point, end_point, mid_point)
    if arc_piece_is_usable(curve, chord_length):
        return curve

    try:
        return Line.CreateBound(start_point, end_point)
    except Exception:
        return None


def create_equal_tangent_perpendicular_biarc(start_point, end_point, tangent):
    """Special case: equal tangents perpendicular to the chord.

    The stable solution is two semicircles meeting at the chord midpoint.
    """
    v = xyz_subtract(end_point, start_point)
    v_dot_v = xyz_dot(v, v)
    v_length = math.sqrt(v_dot_v)
    if v_length <= MIN_OUTPUT_CURVE_LENGTH_FT:
        return []

    mid_point = xyz_midpoint(start_point, end_point)
    radius = v_length * 0.25
    quarter = xyz_scale(v, 0.25)
    center1 = xyz_add(start_point, quarter)
    center2 = xyz_subtract(end_point, quarter)
    normal = xyz_cross(v, tangent)
    perp_axis = xyz_cross(normal, v)
    axis2 = xyz_unit(perp_axis)
    if axis2 is None:
        return []
    axis2 = xyz_scale(axis2, radius)

    axis1_a = xyz_negate(quarter)
    axis1_b = quarter

    curve1 = create_arc_piece_from_biarc_data(
        start_point,
        mid_point,
        center1,
        radius,
        math.pi,
        axis1_a,
        axis2
    )
    curve2 = create_arc_piece_from_biarc_data(
        mid_point,
        end_point,
        center2,
        radius,
        math.pi,
        axis1_b,
        xyz_negate(axis2)
    )

    pieces = []
    for curve in (curve1, curve2):
        if curve is not None and curve_length(curve) > MIN_OUTPUT_CURVE_LENGTH_FT:
            pieces.append(curve)
    return pieces


def create_smooth_biarc_between_vertices(start_point, end_point, start_tangent, end_tangent, normal):
    """Create two G1-continuous circular arcs between two fit vertices."""
    chord = xyz_subtract(end_point, start_point)
    chord_length = xyz_length_vector(chord)
    if chord_length <= MIN_OUTPUT_CURVE_LENGTH_FT:
        return []

    chord_unit = xyz_unit(chord)
    start_tangent = stabilize_segment_tangent(project_vector_to_plane(start_tangent, normal), chord_unit)
    end_tangent = stabilize_segment_tangent(project_vector_to_plane(end_tangent, normal), chord_unit)

    if start_tangent is None or end_tangent is None:
        try:
            return [Line.CreateBound(start_point, end_point)]
        except Exception:
            return []

    # Juckett biarc solve for equal tangent distances.
    t_sum = xyz_add(start_tangent, end_tangent)
    v_dot_v = xyz_dot(chord, chord)
    v_dot_t = xyz_dot(chord, t_sum)
    t1_dot_t2 = xyz_dot(start_tangent, end_tangent)
    denominator = 2.0 * (1.0 - t1_dot_t2)

    if denominator < ARC_FIT_DOT_EPSILON:
        v_dot_t2 = xyz_dot(chord, end_tangent)
        if abs(v_dot_t2) < ARC_FIT_DOT_EPSILON:
            return create_equal_tangent_perpendicular_biarc(start_point, end_point, end_tangent)
        distance_value = v_dot_v / (4.0 * v_dot_t2)
    else:
        discriminant = (v_dot_t * v_dot_t) + (denominator * v_dot_v)
        if discriminant < 0.0:
            discriminant = 0.0
        distance_value = (-v_dot_t + math.sqrt(discriminant)) / denominator

    if abs(distance_value) > chord_length * 1000.0:
        try:
            return [Line.CreateBound(start_point, end_point)]
        except Exception:
            return []

    mid_point = xyz_scale(
        xyz_add(
            xyz_add(start_point, end_point),
            xyz_scale(xyz_subtract(start_tangent, end_tangent), distance_value)
        ),
        0.5
    )

    if (xyz_distance(start_point, mid_point) <= MIN_OUTPUT_CURVE_LENGTH_FT or
            xyz_distance(mid_point, end_point) <= MIN_OUTPUT_CURVE_LENGTH_FT):
        try:
            return [Line.CreateBound(start_point, end_point)]
        except Exception:
            return []

    point_to_mid_1 = xyz_subtract(mid_point, start_point)
    point_to_mid_2 = xyz_subtract(mid_point, end_point)

    arc1_data = compute_arc_data_from_endpoint(start_point, start_tangent, point_to_mid_1)
    arc2_data = compute_arc_data_from_endpoint(end_point, end_tangent, point_to_mid_2)

    if distance_value < 0.0:
        two_pi = math.pi * 2.0
        if not arc1_data.get("is_line"):
            arc1_data["angle"] = sign_nonzero(arc1_data["angle"]) * two_pi - arc1_data["angle"]
        if not arc2_data.get("is_line"):
            arc2_data["angle"] = sign_nonzero(arc2_data["angle"]) * two_pi - arc2_data["angle"]

    pieces = []

    # First arc: start_point -> mid_point.
    if arc1_data.get("is_line"):
        try:
            curve1 = Line.CreateBound(start_point, mid_point)
        except Exception:
            curve1 = None
    else:
        radius1 = arc1_data["radius"]
        center1 = arc1_data["center"]
        axis1 = xyz_subtract(start_point, center1)
        axis2 = xyz_scale(start_tangent, radius1)
        curve1 = create_arc_piece_from_biarc_data(
            start_point,
            mid_point,
            center1,
            radius1,
            arc1_data["angle"],
            axis1,
            axis2
        )

    # Second arc: mid_point -> end_point. Axis definition follows Juckett's
    # second-arc interpolation convention.
    if arc2_data.get("is_line"):
        try:
            curve2 = Line.CreateBound(mid_point, end_point)
        except Exception:
            curve2 = None
    else:
        radius2 = arc2_data["radius"]
        center2 = arc2_data["center"]
        axis1 = xyz_subtract(end_point, center2)
        axis2 = xyz_scale(end_tangent, -radius2)
        curve2 = create_arc_piece_from_biarc_data(
            mid_point,
            end_point,
            center2,
            radius2,
            arc2_data["angle"],
            axis1,
            axis2
        )

    for curve in (curve1, curve2):
        if curve is not None and curve_length(curve) > MIN_OUTPUT_CURVE_LENGTH_FT:
            pieces.append(curve)

    if not pieces:
        try:
            pieces.append(Line.CreateBound(start_point, end_point))
        except Exception:
            pass

    return pieces


def create_arc_fit_curve_pieces_from_points(points_for_curve, is_closed):
    """Create AutoCAD-style smooth tangent circular arc-fit pieces."""
    normal = get_fit_plane_normal(points_for_curve)
    tangents = make_vertex_tangents(points_for_curve, is_closed, normal)

    pieces = []
    count = len(points_for_curve)
    segment_count = count if is_closed else count - 1

    for index in range(segment_count):
        start_index = index
        end_index = (index + 1) % count
        start_point = points_for_curve[start_index]
        end_point = points_for_curve[end_index]
        start_tangent = tangents[start_index]
        end_tangent = tangents[end_index]

        segment_pieces = create_smooth_biarc_between_vertices(
            start_point,
            end_point,
            start_tangent,
            end_tangent,
            normal
        )
        for curve in segment_pieces:
            if curve_length(curve) > MIN_OUTPUT_CURVE_LENGTH_FT:
                pieces.append(curve)

    if not pieces:
        raise ScriptValidationError("No usable AutoCAD-style smooth tangent arc Fit Curve pieces were produced.")

    return pieces


# -----------------------------------------------------------------------------
# AutoCAD PEDIT Fit bridge
# -----------------------------------------------------------------------------

def get_first_distinct_segment(points):
    if len(points) < 2:
        return None
    first_point = points[0]
    for point in points[1:]:
        vector = xyz_subtract(point, first_point)
        if xyz_length_vector(vector) > MIN_OUTPUT_CURVE_LENGTH_FT:
            return vector
    return None


def get_local_2d_basis(points):
    """Return origin, x-axis, y-axis, and normal for a stable 2D AutoCAD fit plane."""
    origin = points[0]
    normal = get_fit_plane_normal(points)
    seed = get_first_distinct_segment(points)
    if seed is None:
        raise ScriptValidationError("Could not determine a local AutoCAD fit basis from the selected points.")

    x_axis = project_vector_to_plane(seed, normal)
    if x_axis is None:
        raise ScriptValidationError("Could not determine a local AutoCAD fit X axis from the selected points.")

    y_axis = xyz_cross(normal, x_axis)
    y_axis = xyz_unit(y_axis)
    if y_axis is None:
        raise ScriptValidationError("Could not determine a local AutoCAD fit Y axis from the selected points.")

    return origin, x_axis, y_axis, normal


def point_to_local_2d(point, origin, x_axis, y_axis):
    vector = xyz_subtract(point, origin)
    return xyz_dot(vector, x_axis), xyz_dot(vector, y_axis)


def point_from_local_2d(x_value, y_value, origin, x_axis, y_axis):
    return xyz_add(
        origin,
        xyz_add(
            xyz_scale(x_axis, float(x_value)),
            xyz_scale(y_axis, float(y_value))
        )
    )


def format_dxf_float(value):
    text = "{0:.15f}".format(float(value))
    text = text.rstrip("0").rstrip(".")
    if text == "-0":
        text = "0"
    if text == "":
        text = "0"
    return text


def write_autocad_input_dxf(path_value, local_points, is_closed):
    '''Write a blank R12 DXF. AutoLISP creates the polyline after Core Console opens.'''
    lines = []
    lines.extend(["0", "SECTION", "2", "HEADER", "9", "$ACADVER", "1", "AC1009"])
    lines.extend(["9", "$PLINETYPE", "70", "0"])
    lines.extend(["0", "ENDSEC"])
    lines.extend(["0", "SECTION", "2", "ENTITIES", "0", "ENDSEC", "0", "EOF", ""])

    with open(path_value, "w") as dxf_file:
        dxf_file.write("\n".join(lines))


def to_lisp_path(path_value):
    return path_value.replace("\\", "/")


def lisp_string(path_value):
    return to_lisp_path(path_value).replace('"', '\\"')


def lisp_number(value):
    text = "{0:.15f}".format(float(value))
    text = text.rstrip("0").rstrip(".")
    if text in ("", "-0"):
        text = "0"
    return text


def make_lisp_point_list(local_points):
    items = []
    for x_value, y_value in local_points:
        items.append("({0} {1})".format(lisp_number(x_value), lisp_number(y_value)))
    return "'({0})".format(" ".join(items))



def write_autocad_curve_fit_lisp(path_value, result_path, log_path, local_points, is_closed):
    result_lisp_path = lisp_string(result_path)
    log_lisp_path = lisp_string(log_path)
    lisp_points = make_lisp_point_list(local_points)
    closed_flag = 1 if is_closed else 0
    lisp = r'''
(setq *py_points* __POINT_LIST__)
(setq *py_closed_flag* __CLOSED_FLAG__)
(setq *py_entity_handle* nil)
(defun _py_rtos (v)
  (rtos (if (numberp v) v 0.0) 2 16)
)
(defun _py_log (msg / f)
  (setq f (open "__LOG_PATH__" "a"))
  (if f
    (progn
      (write-line msg f)
      (close f)
    )
  )
  (princ)
)
(defun _py_write_error (msg / f)
  (_py_log (strcat "ERROR: " msg))
  (setq f (open "__RESULT_PATH__" "w"))
  (if f
    (progn
      (write-line (strcat "ERROR," msg) f)
      (close f)
    )
  )
  (princ)
)
(defun _py_safesetvar (name value / old result)
  (setq result (vl-catch-all-apply 'getvar (list name)))
  (if (not (vl-catch-all-error-p result))
    (progn
      (setq old result)
      (vl-catch-all-apply 'setvar (list name value))
    )
  )
  old
)
(defun _py_entity_type (e / ed typ)
  (if e
    (progn
      (setq ed (entget e))
      (setq typ (cdr (assoc 0 ed)))
      (if typ typ "UNKNOWN")
    )
    "nil"
  )
)
(defun _py_lw_vertex_count (ed / item count)
  (setq count 0)
  (foreach item ed
    (if (= (car item) 10)
      (setq count (+ count 1))
    )
  )
  count
)
(defun _py_old_vertex_count (e / v edv typ count)
  (setq count 0)
  (setq v (entnext e))
  (while v
    (setq edv (entget v))
    (setq typ (cdr (assoc 0 edv)))
    (if (= typ "SEQEND")
      (setq v nil)
      (progn
        (if (= typ "VERTEX")
          (setq count (+ count 1))
        )
        (setq v (entnext v))
      )
    )
  )
  count
)
(defun _py_poly_vertex_count (e / ed typ)
  (if e
    (progn
      (setq ed (entget e))
      (setq typ (cdr (assoc 0 ed)))
      (cond
        ((= typ "POLYLINE") (_py_old_vertex_count e))
        ((= typ "LWPOLYLINE") (_py_lw_vertex_count ed))
        (T 0)
      )
    )
    0
  )
)
(defun _py_find_best_polyline ( / ss i e best bestcount count)
  (setq best nil)
  (setq bestcount 0)
  (setq ss (ssget "X" '((0 . "POLYLINE,LWPOLYLINE"))))
  (if ss
    (progn
      (setq i 0)
      (while (< i (sslength ss))
        (setq e (ssname ss i))
        (setq count (_py_poly_vertex_count e))
        (if (> count bestcount)
          (progn
            (setq best e)
            (setq bestcount count)
          )
        )
        (setq i (+ i 1))
      )
    )
  )
  (_py_log (strcat "Best polyline vertex count found: " (itoa bestcount)))
  best
)
(defun _py_make_lwpolyline_data (pts closed / data p flag)
  (setq flag (if (= closed 1) 1 0))
  (setq data
    (list
      (cons 0 "LWPOLYLINE")
      (cons 100 "AcDbEntity")
      (cons 8 "0")
      (cons 100 "AcDbPolyline")
      (cons 90 (length pts))
      (cons 70 flag)
      (cons 38 0.0)
      (cons 39 0.0)
    )
  )
  (foreach p pts
    (setq data
      (append
        data
        (list
          (cons 10 (list (car p) (cadr p)))
          (cons 40 0.0)
          (cons 41 0.0)
          (cons 42 0.0)
        )
      )
    )
  )
  data
)
(defun _py_make_lwpolyline (pts closed / e ed h)
  (_py_log (strcat "Creating LWPOLYLINE with entmakex. Closed flag: " (itoa (if (= closed 1) 1 0))))
  (setq e (entmakex (_py_make_lwpolyline_data pts closed)))
  (if e
    (progn
      (setq ed (entget e))
      (setq h (cdr (assoc 5 ed)))
      (setq *py_entity_handle* h)
      (_py_log (strcat "Created entity type: " (_py_entity_type e)))
      (_py_log (strcat "Created handle: " (if h h "nil")))
      (_py_log (strcat "Created vertex count: " (itoa (_py_poly_vertex_count e))))
    )
    (_py_log "ERROR: entmakex returned nil")
  )
  e
)
(defun _py_write_vertex_line (f x y bulge flag)
  (write-line
    (strcat
      "VERTEX,"
      (_py_rtos x) ","
      (_py_rtos y) ","
      (_py_rtos bulge) ","
      (itoa (if flag flag 0))
    )
    f
  )
)
(defun _py_write_old_polyline_vertices (e f / v edv typ pt bulge flag count)
  (setq count 0)
  (setq v (entnext e))
  (while v
    (setq edv (entget v))
    (setq typ (cdr (assoc 0 edv)))
    (if (= typ "SEQEND")
      (setq v nil)
      (progn
        (if (= typ "VERTEX")
          (progn
            (setq pt (cdr (assoc 10 edv)))
            (setq bulge (cdr (assoc 42 edv)))
            (setq flag (cdr (assoc 70 edv)))
            (if pt
              (progn
                (_py_write_vertex_line f (car pt) (cadr pt) (if bulge bulge 0.0) (if flag flag 0))
                (setq count (+ count 1))
              )
            )
          )
        )
        (setq v (entnext v))
      )
    )
  )
  count
)
(defun _py_write_lwpolyline_vertices (ed f / item pt bulge flag count)
  (setq pt nil)
  (setq bulge 0.0)
  (setq flag 0)
  (setq count 0)
  (foreach item ed
    (cond
      ((= (car item) 10)
        (if pt
          (progn
            (_py_write_vertex_line f (car pt) (cadr pt) bulge flag)
            (setq count (+ count 1))
          )
        )
        (setq pt (cdr item))
        (setq bulge 0.0)
        (setq flag 0)
      )
      ((= (car item) 42)
        (setq bulge (cdr item))
      )
    )
  )
  (if pt
    (progn
      (_py_write_vertex_line f (car pt) (cadr pt) bulge flag)
      (setq count (+ count 1))
    )
  )
  count
)
(defun _py_write_curve_result (e / ed typ f polyflag vertexcount)
  (setq ed (entget e))
  (setq typ (cdr (assoc 0 ed)))
  (setq polyflag (cdr (assoc 70 ed)))
  (_py_log (strcat "Writing result for entity type: " typ))
  (_py_log (strcat "Result poly flag: " (itoa (if polyflag polyflag 0))))
  (setq f (open "__RESULT_PATH__" "w"))
  (if (not f)
    (_py_write_error "Could not open result file")
    (progn
      (write-line "OK" f)
      (write-line (strcat "POLYTYPE," typ) f)
      (write-line (strcat "POLYFLAG," (itoa (if polyflag polyflag 0))) f)
      (cond
        ((= typ "POLYLINE")
          (setq vertexcount (_py_write_old_polyline_vertices e f))
        )
        ((= typ "LWPOLYLINE")
          (setq vertexcount (_py_write_lwpolyline_vertices ed f))
        )
        (T
          (setq vertexcount 0)
        )
      )
      (close f)
      (_py_log (strcat "Result vertex count: " (itoa vertexcount)))
      (if (< vertexcount 2)
        (_py_write_error "PEDIT Fit produced fewer than two vertices")
      )
    )
  )
  (princ)
)
(defun _py_restore_vars (old_filedia old_cmdecho old_plinetype old_peditaccept)
  (if old_filedia (vl-catch-all-apply 'setvar (list "FILEDIA" old_filedia)))
  (if old_cmdecho (vl-catch-all-apply 'setvar (list "CMDECHO" old_cmdecho)))
  (if old_plinetype (vl-catch-all-apply 'setvar (list "PLINETYPE" old_plinetype)))
  (if old_peditaccept (vl-catch-all-apply 'setvar (list "PEDITACCEPT" old_peditaccept)))
  (princ)
)
(defun _py_curve_fit_main ( / e byhandle pedit_result old_cmdecho old_filedia old_plinetype old_peditaccept beforecount aftercount)
  (_py_log "START curve fit main AutoCAD PEDIT Fit")
  (setq old_filedia (_py_safesetvar "FILEDIA" 0))
  (setq old_cmdecho (_py_safesetvar "CMDECHO" 0))
  (setq old_plinetype (_py_safesetvar "PLINETYPE" 0))
  (setq old_peditaccept (_py_safesetvar "PEDITACCEPT" 1))
  (_py_log (strcat "Point count: " (itoa (length *py_points*))))
  (setq e (_py_make_lwpolyline *py_points* *py_closed_flag*))
  (if (not e)
    (_py_write_error "Could not create LWPOLYLINE before PEDIT")
    (progn
      (setq beforecount (_py_poly_vertex_count e))
      (_py_log (strcat "Before PEDIT type: " (_py_entity_type e)))
      (_py_log (strcat "Before PEDIT vertex count: " (itoa beforecount)))
      (_py_log "About to run command-s: PEDIT <entity> Fit <exit>")
      (setq pedit_result (vl-catch-all-apply 'command-s (list "_.PEDIT" e "_Fit" "")))
      (if (vl-catch-all-error-p pedit_result)
        (_py_write_error (strcat "PEDIT command-s failed: " (vl-catch-all-error-message pedit_result)))
        (progn
          (_py_log "PEDIT command-s returned")
          (setq byhandle nil)
          (if *py_entity_handle*
            (setq byhandle (handent *py_entity_handle*))
          )
          (if byhandle
            (progn
              (_py_log (strcat "Found entity by original handle after PEDIT: " (_py_entity_type byhandle)))
              (setq e byhandle)
            )
            (progn
              (_py_log "Original handle not found after PEDIT; searching all polylines.")
              (setq e (_py_find_best_polyline))
            )
          )
          (if (not e)
            (_py_write_error "No POLYLINE or LWPOLYLINE found after PEDIT")
            (progn
              (setq aftercount (_py_poly_vertex_count e))
              (_py_log (strcat "After PEDIT type: " (_py_entity_type e)))
              (_py_log (strcat "After PEDIT vertex count: " (itoa aftercount)))
              (_py_write_curve_result e)
            )
          )
        )
      )
    )
  )
  (_py_restore_vars old_filedia old_cmdecho old_plinetype old_peditaccept)
  (_py_log "END curve fit main v5.14")
  (princ)
)
'''
    lisp = lisp.replace("__POINT_LIST__", lisp_points)
    lisp = lisp.replace("__CLOSED_FLAG__", str(closed_flag))
    lisp = lisp.replace("__RESULT_PATH__", result_lisp_path)
    lisp = lisp.replace("__LOG_PATH__", log_lisp_path)
    with open(path_value, "w") as lisp_file:
        lisp_file.write(lisp)

def write_autocad_curve_fit_script(path_value, lisp_path):
    lisp_lisp_path = lisp_string(lisp_path)
    script_lines = [
        '(setvar "FILEDIA" 0)',
        '(setvar "CMDECHO" 0)',
        '(setvar "SECURELOAD" 0)',
        '(setvar "PEDITACCEPT" 1)',
        '(setvar "PLINETYPE" 0)',
        '(load "{0}")'.format(lisp_lisp_path),
        '(_py_curve_fit_main)',
        '_.QUIT',
        '_N',
        ''
    ]
    with open(path_value, "w") as script_file:
        script_file.write("\r\n".join(script_lines))

def write_accoreconsole_batch(path_value, accoreconsole, input_dxf_path, script_path):
    lines = [
        '@echo off',
        '"{0}" /i "{1}" /s "{2}" /l en-US'.format(accoreconsole, input_dxf_path, script_path),
        'exit /b %ERRORLEVEL%',
        ''
    ]
    with open(path_value, "w") as batch_file:
        batch_file.write("\r\n".join(lines))


def build_accoreconsole_failure_message(message, exit_code, temp_root, stdout_path, stderr_path, lisp_log_path, result_path):
    """Return a compact production error message.

    Full AutoCAD/Lisp trace files are intentionally not printed in production.
    They are kept only long enough to decide whether the command should use the
    AutoCAD result or fall back to the native biarc engine.
    """
    if exit_code is None:
        return message
    return "{0} Exit code: {1}".format(message, exit_code)


def compact_error_message(exception_obj):
    """Return the first useful line of an exception for production logs."""
    try:
        text_value = str(exception_obj)
    except Exception:
        return "Unavailable error detail."
    for line in text_value.splitlines():
        line = line.strip()
        if line:
            return line
    return "Unavailable error detail."


def delete_folder_safely(folder_path):
    """Best-effort cleanup for temporary AutoCAD bridge files."""
    if not folder_path or not os.path.isdir(folder_path):
        return
    try:
        shutil.rmtree(folder_path, ignore_errors=True)
    except Exception:
        pass

def find_accoreconsole_exe():
    for env_name in AUTOCAD_CORE_CONSOLE_ENV_NAMES:
        env_value = os.environ.get(env_name, "")
        if env_value and os.path.isfile(env_value):
            return env_value

    program_files = os.environ.get("ProgramFiles", r"C:\Program Files")
    program_files_x86 = os.environ.get("ProgramFiles(x86)", r"C:\Program Files (x86)")
    roots = [
        os.path.join(program_files, "Autodesk"),
        os.path.join(program_files_x86, "Autodesk")
    ]

    direct_names = []
    for year in range(2027, 2009, -1):
        direct_names.append("AutoCAD {0}".format(year))
        direct_names.append("AutoCAD LT {0}".format(year))

    candidates = []
    for root in roots:
        for name in direct_names:
            candidates.append(os.path.join(root, name, "accoreconsole.exe"))
        try:
            if os.path.isdir(root):
                for child in os.listdir(root):
                    if child.lower().startswith("autocad"):
                        candidates.append(os.path.join(root, child, "accoreconsole.exe"))
        except Exception:
            pass

    seen = set()
    for candidate in candidates:
        key = candidate.lower()
        if key in seen:
            continue
        seen.add(key)
        if os.path.isfile(candidate):
            return candidate

    return None



def wait_for_text_file(path_value, timeout_seconds):
    """Wait briefly for Core Console/Lisp file output to flush to disk."""
    end_time = time.time() + float(timeout_seconds)
    while time.time() < end_time:
        try:
            if path_value and os.path.isfile(path_value) and os.path.getsize(path_value) > 0:
                return True
        except Exception:
            pass
        time.sleep(0.20)
    try:
        return path_value and os.path.isfile(path_value) and os.path.getsize(path_value) > 0
    except Exception:
        return False


def wait_for_stable_result_file(path_value, timeout_seconds):
    """Return True when the AutoCAD result file exists and its size has stopped changing.

    Core Console sometimes writes a complete result but then keeps running. This
    helper lets pyRevit continue as soon as the result file is stable, rather than
    waiting for the overall Core Console timeout.
    """
    end_time = time.time() + float(timeout_seconds)
    last_size = -1
    stable_count = 0
    while time.time() < end_time:
        try:
            if path_value and os.path.isfile(path_value):
                size = os.path.getsize(path_value)
                if size > 0:
                    if size == last_size:
                        stable_count += 1
                    else:
                        stable_count = 0
                        last_size = size
                    if stable_count >= 2:
                        return True
        except Exception:
            pass
        time.sleep(0.25)
    try:
        return path_value and os.path.isfile(path_value) and os.path.getsize(path_value) > 0
    except Exception:
        return False


def kill_process_tree_safely(process):
    """Kill cmd.exe and its child accoreconsole.exe when Core Console hangs after writing results."""
    if process is None:
        return
    process_id = None
    try:
        process_id = process.Id
    except Exception:
        process_id = None

    if process_id is not None:
        try:
            os.system('taskkill /PID {0} /T /F > nul 2> nul'.format(process_id))
            return
        except Exception:
            pass

    try:
        process.Kill()
    except Exception:
        pass

def run_accoreconsole(input_dxf_path, script_path, result_path, stdout_path, stderr_path, batch_path, lisp_log_path, temp_root):
    accoreconsole = find_accoreconsole_exe()
    if not accoreconsole:
        raise ScriptValidationError("AutoCAD Core Console was not found.")

    try:
        from System.Diagnostics import Process
        from System.Diagnostics import ProcessStartInfo
    except Exception as ex:
        raise ScriptValidationError("Could not load .NET process helpers for AutoCAD Core Console. {0}".format(ex))

    write_accoreconsole_batch(batch_path, accoreconsole, input_dxf_path, script_path)

    process_start = ProcessStartInfo()
    process_start.FileName = "cmd.exe"
    process_start.Arguments = '/d /c call "{0}" > "{1}" 2> "{2}"'.format(batch_path, stdout_path, stderr_path)
    process_start.UseShellExecute = False
    process_start.CreateNoWindow = True

    process = Process()
    process.StartInfo = process_start

    result_captured_early = False
    exit_code = None

    try:
        if not process.Start():
            raise ScriptValidationError("AutoCAD Core Console did not start.")

        end_time = time.time() + float(AUTOCAD_CORE_CONSOLE_TIMEOUT_SECONDS)
        while time.time() < end_time:
            try:
                if process.HasExited:
                    break
            except Exception:
                pass

            if wait_for_stable_result_file(result_path, 0.75):
                result_captured_early = True
                # Let the AutoLISP log and stdout flush, then stop Core Console.
                time.sleep(0.50)
                kill_process_tree_safely(process)
                logger.info("AutoCAD Core Console result captured; stopping Core Console.")
                break

            time.sleep(0.25)

        try:
            if process.HasExited and not result_captured_early:
                exit_code = process.ExitCode
        except Exception:
            exit_code = None

        if not result_captured_early:
            try:
                still_running = not process.HasExited
            except Exception:
                still_running = False
            if still_running:
                kill_process_tree_safely(process)
                raise ScriptValidationError(
                    build_accoreconsole_failure_message(
                        "AutoCAD Core Console timed out after {0} seconds before writing a curve-fit result file.".format(AUTOCAD_CORE_CONSOLE_TIMEOUT_SECONDS),
                        "timeout",
                        temp_root,
                        stdout_path,
                        stderr_path,
                        lisp_log_path,
                        result_path
                    )
                )

    except ScriptValidationError:
        raise
    except Exception as ex:
        raise ScriptValidationError("AutoCAD Core Console failed. {0}".format(ex))

    if not wait_for_stable_result_file(result_path, 2.0):
        raise ScriptValidationError(
            build_accoreconsole_failure_message(
                "AutoCAD Core Console did not produce a curve-fit result file.",
                exit_code,
                temp_root,
                stdout_path,
                stderr_path,
                lisp_log_path,
                result_path
            )
        )

    if exit_code not in (0, None):
        logger.warning(
            build_accoreconsole_failure_message(
                "AutoCAD Core Console returned a non-zero exit code but did produce a result file.",
                exit_code,
                temp_root,
                stdout_path,
                stderr_path,
                lisp_log_path,
                result_path
            )
        )

def parse_autocad_curve_fit_result(result_path):
    vertices = []
    polyflag = 0

    with open(result_path, "r") as result_file:
        lines = [line.strip() for line in result_file.readlines() if line.strip()]

    if not lines:
        raise ScriptValidationError("AutoCAD Core Console returned an empty curve-fit result.")

    if lines[0].startswith("ERROR"):
        raise ScriptValidationError("AutoCAD Core Console curve fit failed: {0}".format(lines[0]))

    if lines[0] != "OK":
        raise ScriptValidationError("AutoCAD Core Console returned an unexpected curve-fit result header: {0}".format(lines[0]))

    for line in lines[1:]:
        parts = line.split(",")
        if not parts:
            continue
        if parts[0] == "POLYFLAG" and len(parts) > 1:
            try:
                polyflag = int(parts[1])
            except Exception:
                polyflag = 0
        elif parts[0] == "VERTEX" and len(parts) >= 5:
            try:
                vertices.append({
                    "x": float(parts[1]),
                    "y": float(parts[2]),
                    "bulge": float(parts[3]),
                    "flag": int(float(parts[4]))
                })
            except Exception:
                pass

    if len(vertices) < 2:
        raise ScriptValidationError("AutoCAD Core Console returned too few curve-fit vertices.")

    return vertices, polyflag


def create_curve_from_bulge_segment(start_vertex, end_vertex, origin, x_axis, y_axis):
    start_point = point_from_local_2d(start_vertex["x"], start_vertex["y"], origin, x_axis, y_axis)
    end_point = point_from_local_2d(end_vertex["x"], end_vertex["y"], origin, x_axis, y_axis)
    chord_length = xyz_distance(start_point, end_point)
    if chord_length <= MIN_OUTPUT_CURVE_LENGTH_FT:
        return None

    bulge = float(start_vertex.get("bulge", 0.0))
    if abs(bulge) <= BULGE_ARC_TOLERANCE:
        try:
            return Line.CreateBound(start_point, end_point)
        except Exception:
            return None

    x1 = float(start_vertex["x"])
    y1 = float(start_vertex["y"])
    x2 = float(end_vertex["x"])
    y2 = float(end_vertex["y"])
    dx = x2 - x1
    dy = y2 - y1
    local_chord = math.sqrt((dx * dx) + (dy * dy))
    if local_chord <= MIN_OUTPUT_CURVE_LENGTH_FT:
        return None

    theta = 4.0 * math.atan(bulge)
    radius = local_chord * (1.0 + (bulge * bulge)) / (4.0 * abs(bulge))
    center_offset = local_chord * (1.0 - (bulge * bulge)) / (4.0 * bulge)
    mid_x = (x1 + x2) * 0.5
    mid_y = (y1 + y2) * 0.5
    left_x = -dy / local_chord
    left_y = dx / local_chord
    center_x = mid_x + (left_x * center_offset)
    center_y = mid_y + (left_y * center_offset)
    start_angle = math.atan2(y1 - center_y, x1 - center_x)
    mid_angle = start_angle + (theta * 0.5)
    arc_mid_x = center_x + (radius * math.cos(mid_angle))
    arc_mid_y = center_y + (radius * math.sin(mid_angle))
    mid_point = point_from_local_2d(arc_mid_x, arc_mid_y, origin, x_axis, y_axis)

    try:
        return Arc.Create(start_point, end_point, mid_point)
    except Exception as ex:
        logger.warning("AutoCAD bulge segment could not be converted to a Revit Arc; using line fallback. {0}".format(ex))
        try:
            return Line.CreateBound(start_point, end_point)
        except Exception:
            return None


def build_revit_curves_from_autocad_vertices(vertices, polyflag, requested_closed, origin, x_axis, y_axis):
    curves = []
    construction_points = []
    for vertex in vertices:
        construction_points.append(point_from_local_2d(vertex["x"], vertex["y"], origin, x_axis, y_axis))

    is_polyline_closed = requested_closed or ((int(polyflag) & 1) == 1)
    segment_count = len(vertices) if is_polyline_closed else len(vertices) - 1

    for index in range(segment_count):
        start_vertex = vertices[index]
        end_vertex = vertices[(index + 1) % len(vertices)]
        curve = create_curve_from_bulge_segment(start_vertex, end_vertex, origin, x_axis, y_axis)
        if curve is not None and curve_length(curve) > MIN_OUTPUT_CURVE_LENGTH_FT:
            curves.append(curve)

    if not curves:
        raise ScriptValidationError("AutoCAD Core Console produced no usable Revit Arc/Line pieces.")

    return curves, construction_points


def create_autocad_pedit_fit_curve_pieces(points_for_curve, is_closed):
    """Use real AutoCAD PEDIT Fit to generate curve-fit vertices and bulges."""
    origin, x_axis, y_axis, normal = get_local_2d_basis(points_for_curve)
    local_points = []
    for point in points_for_curve:
        local_points.append(point_to_local_2d(point, origin, x_axis, y_axis))

    temp_root = tempfile.mkdtemp(prefix="pyrevit_acad_fit_")
    input_dxf_path = os.path.join(temp_root, AUTOCAD_CURVE_FIT_INPUT_NAME)
    script_path = os.path.join(temp_root, AUTOCAD_CURVE_FIT_SCRIPT_NAME)
    lisp_path = os.path.join(temp_root, AUTOCAD_CURVE_FIT_LISP_NAME)
    batch_path = os.path.join(temp_root, AUTOCAD_CURVE_FIT_BATCH_NAME)
    result_path = os.path.join(temp_root, AUTOCAD_CURVE_FIT_RESULT_NAME)
    lisp_log_path = os.path.join(temp_root, AUTOCAD_CURVE_FIT_LOG_NAME)
    stdout_path = os.path.join(temp_root, AUTOCAD_CURVE_FIT_STDOUT_NAME)
    stderr_path = os.path.join(temp_root, AUTOCAD_CURVE_FIT_STDERR_NAME)

    try:
        logger.info("AutoCAD PEDIT Fit source local point count: {0}".format(len(local_points)))
        write_autocad_input_dxf(input_dxf_path, local_points, is_closed)
        write_autocad_curve_fit_lisp(lisp_path, result_path, lisp_log_path, local_points, is_closed)
        write_autocad_curve_fit_script(script_path, lisp_path)
        run_accoreconsole(input_dxf_path, script_path, result_path, stdout_path, stderr_path, batch_path, lisp_log_path, temp_root)
        vertices, polyflag = parse_autocad_curve_fit_result(result_path)
        logger.info("AutoCAD PEDIT Fit returned {0} curve-fit vertices; polyline flag {1}.".format(len(vertices), polyflag))
        return build_revit_curves_from_autocad_vertices(vertices, polyflag, is_closed, origin, x_axis, y_axis)
    finally:
        delete_folder_safely(temp_root)


def create_fit_curve_pieces(fit_points, is_closed, progress_bar):
    """Create AutoCAD PEDIT Fit style tangent circular arc output through vertices.

    The primary engine is AutoCAD Core Console running the real PEDIT Fit
    operation against a temporary old-style 2D polyline. The returned curve-fit
    vertices and DXF bulges are converted back into editable Revit Arc/Line
    elements. If AutoCAD Core Console is unavailable, the native G1 biarc
    approximation remains as a fallback.
    """
    duplicate_tolerance = JOIN_TOLERANCE_FT * 0.5

    if is_closed:
        points_for_curve = remove_closing_duplicate_point(
            remove_consecutive_duplicate_points(fit_points, duplicate_tolerance),
            duplicate_tolerance
        )
        points_for_curve = remove_all_duplicate_points(points_for_curve, duplicate_tolerance)
        if len(points_for_curve) < 3 or count_unique_points(points_for_curve, JOIN_TOLERANCE_FT) < 3:
            raise ScriptValidationError("At least three unique fit points are required for a closed Fit Curve.")
    else:
        points_for_curve = remove_consecutive_duplicate_points(fit_points, duplicate_tolerance)
        if len(points_for_curve) < 3 or count_unique_points(points_for_curve, JOIN_TOLERANCE_FT) < 3:
            raise ScriptValidationError("At least three unique fit points are required for an open Fit Curve.")

    logger.info("AutoCAD PEDIT Fit Curve source point count: {0}".format(len(points_for_curve)))

    if progress_bar:
        progress_bar.update_progress(1, 4)
        if progress_bar.cancelled:
            raise UserCancelled("Operation cancelled.")

    output_pieces = []
    construction_points = points_for_curve
    engine = ""

    try:
        output_pieces, construction_points = create_autocad_pedit_fit_curve_pieces(points_for_curve, is_closed)
        engine = "AutoCAD Core Console PEDIT Fit curve-fit vertices and DXF bulges"
    except Exception as ex:
        reason = compact_error_message(ex)
        logger.warning("AutoCAD PEDIT Fit engine failed; using native biarc fallback. {0}".format(reason))
        output_pieces = create_arc_fit_curve_pieces_from_points(points_for_curve, is_closed)
        construction_points = points_for_curve
        engine = "Native G1 tangent circular biarc fallback; AutoCAD PEDIT Fit unavailable"

    if progress_bar:
        progress_bar.update_progress(3, 4)
        if progress_bar.cancelled:
            raise UserCancelled("Operation cancelled.")

    usable = []
    for piece in output_pieces:
        if curve_length(piece) > MIN_OUTPUT_CURVE_LENGTH_FT:
            usable.append(piece)

    if not usable:
        raise ScriptValidationError("No usable AutoCAD PEDIT Fit Curve pieces were produced.")

    if progress_bar:
        progress_bar.update_progress(4, 4)

    return usable, construction_points, 0, engine


# -----------------------------------------------------------------------------
# Spline Curve creation: control-point NURBS
# -----------------------------------------------------------------------------

def make_open_uniform_clamped_knots(control_point_count, degree):
    if degree < 1:
        raise ScriptValidationError("NURBS degree must be at least 1.")
    if control_point_count <= degree:
        raise ScriptValidationError("Control point count must be greater than NURBS degree.")

    interior_count = control_point_count - degree - 1
    end_value = float(interior_count + 1)

    knots = []
    for _ in range(degree + 1):
        knots.append(0.0)
    for value in range(1, interior_count + 1):
        knots.append(float(value))
    for _ in range(degree + 1):
        knots.append(end_value)

    expected_count = control_point_count + degree + 1
    if len(knots) != expected_count:
        raise ScriptValidationError(
            "Internal knot creation error. Expected {0} knots, got {1}.".format(expected_count, len(knots))
        )

    return knots


def make_unit_weights(control_point_count):
    weights = []
    for _ in range(control_point_count):
        weights.append(1.0)
    return weights


def create_open_control_point_spline(control_points):
    control_point_count = len(control_points)

    if control_point_count < 2:
        raise ScriptValidationError("At least two control points are required.")

    if control_point_count == 2:
        try:
            return [Line.CreateBound(control_points[0], control_points[1])], 1, "Revit Line.CreateBound fallback"
        except Exception as ex:
            raise ScriptValidationError("Could not create a line from the two control points. {0}".format(ex))

    degree = min(NURBS_DEGREE, control_point_count - 1)
    if degree < 1:
        raise ScriptValidationError("Not enough control points to create a NURBS curve.")

    knots = make_open_uniform_clamped_knots(control_point_count, degree)
    revit_points = make_xyz_list(control_points)
    revit_knots = make_double_list(knots)

    try:
        return [NurbSpline.CreateCurve(degree, revit_knots, revit_points)], degree, "Revit NurbSpline.CreateCurve control-point spline"
    except Exception as first_error:
        try:
            revit_weights = make_double_list(make_unit_weights(control_point_count))
            return [NurbSpline.CreateCurve(degree, revit_knots, revit_points, revit_weights)], degree, "Revit NurbSpline.CreateCurve weighted fallback"
        except Exception as second_error:
            raise ScriptValidationError(
                "Could not create a degree-{0} NURBS spline from the selected control points. "
                "First error: {1}. Weighted fallback error: {2}".format(degree, first_error, second_error)
            )


def create_closed_control_point_spline(control_points, progress_bar):
    load_dynamo_bridge()

    closed_points = remove_consecutive_duplicate_points(control_points, JOIN_TOLERANCE_FT * 0.5)
    if not xyz_is_close(closed_points[0], closed_points[-1], JOIN_TOLERANCE_FT):
        closed_points.append(closed_points[0])

    unique_count = count_unique_points(closed_points, JOIN_TOLERANCE_FT)
    if unique_count < 3:
        raise ScriptValidationError("At least three unique control points are required for a closed Spline Curve.")

    degree = min(NURBS_DEGREE, len(closed_points) - 1)
    if len(closed_points) <= degree:
        raise ScriptValidationError(
            "A degree-{0} closed NURBS spline requires more than {0} control points.".format(degree)
        )

    ds_points = []
    ds_curve = None
    ds_pieces = []
    revit_pieces = []

    try:
        if progress_bar:
            progress_bar.update_progress(1, 4)
            if progress_bar.cancelled:
                raise UserCancelled("Operation cancelled.")

        ds_points, used_revitnodes_conversion = make_designscript_points(closed_points, True)

        if progress_bar:
            progress_bar.update_progress(2, 4)
            if progress_bar.cancelled:
                raise UserCancelled("Operation cancelled.")

        ds_curve = DSNurbsCurve.ByControlPoints(
            make_ds_point_array(ds_points),
            int(degree),
            True
        )
        split_result = ds_curve.SplitByParameter(make_double_array([SPLIT_NORMALIZED_PARAMETER]))
        ds_pieces = list(flatten_any(split_result))

        if progress_bar:
            progress_bar.update_progress(3, 4)
            if progress_bar.cancelled:
                raise UserCancelled("Operation cancelled.")

        for piece in ds_pieces:
            revit_curve = ds_curve_to_revit_curve(piece, used_revitnodes_conversion)
            if curve_length(revit_curve) > MIN_OUTPUT_CURVE_LENGTH_FT:
                revit_pieces.append(revit_curve)

        if not revit_pieces:
            raise ScriptValidationError("No usable Revit closed Spline Curve pieces were produced.")

        if progress_bar:
            progress_bar.update_progress(4, 4)

        return revit_pieces, closed_points, degree, "Dynamo NurbsCurve.ByControlPoints closed spline"

    finally:
        dispose_ds(ds_points)
        dispose_ds(ds_curve)
        dispose_ds(ds_pieces)


def create_spline_curve_pieces(control_points, is_closed, progress_bar):
    if is_closed:
        return create_closed_control_point_spline(control_points, progress_bar)

    open_points = remove_closing_duplicate_point(
        remove_consecutive_duplicate_points(control_points, JOIN_TOLERANCE_FT * 0.5),
        JOIN_TOLERANCE_FT * 0.5
    )
    if len(open_points) < 2 or count_unique_points(open_points, JOIN_TOLERANCE_FT) < 2:
        raise ScriptValidationError("At least two unique control points are required for an open Spline Curve.")

    if progress_bar:
        progress_bar.update_progress(1, 2)
        if progress_bar.cancelled:
            raise UserCancelled("Operation cancelled.")

    revit_pieces, degree, engine = create_open_control_point_spline(open_points)

    usable = []
    for curve in revit_pieces:
        if curve_length(curve) > MIN_OUTPUT_CURVE_LENGTH_FT:
            usable.append(curve)

    if not usable:
        raise ScriptValidationError("The open Spline Curve is below Revit's usable length tolerance.")

    if progress_bar:
        progress_bar.update_progress(2, 2)

    return usable, open_points, degree, engine


# -----------------------------------------------------------------------------
# Revit creation helpers
# -----------------------------------------------------------------------------

def set_line_style_safely(curve_element, line_style):
    if line_style is None:
        return False
    try:
        curve_element.LineStyle = line_style
        return True
    except Exception:
        return False


def create_model_curves(document, output_curves, sketch_plane, sketch_plane_plane, line_style, progress_bar):
    created = []
    sketch_plane = get_or_create_sketch_plane(document, sketch_plane, sketch_plane_plane)

    for index, curve in enumerate(output_curves):
        if progress_bar and progress_bar.cancelled:
            raise UserCancelled("Operation cancelled before creating all model curves.")
        if curve_length(curve) <= MIN_OUTPUT_CURVE_LENGTH_FT:
            logger.warning("Skipped one output curve shorter than Revit short-curve tolerance.")
            continue
        created_curve = document.Create.NewModelCurve(curve, sketch_plane)
        set_line_style_safely(created_curve, line_style)
        created.append(created_curve)
        if progress_bar:
            progress_bar.update_progress(index + 1, len(output_curves))

    if not created:
        raise ScriptValidationError("No model curves were created.")
    return created


def create_detail_curves(document, active_view, output_curves, line_style, progress_bar):
    created = []

    for index, curve in enumerate(output_curves):
        if progress_bar and progress_bar.cancelled:
            raise UserCancelled("Operation cancelled before creating all detail curves.")
        if curve_length(curve) <= MIN_OUTPUT_CURVE_LENGTH_FT:
            logger.warning("Skipped one output curve shorter than Revit short-curve tolerance.")
            continue
        created_curve = document.Create.NewDetailCurve(active_view, curve)
        set_line_style_safely(created_curve, line_style)
        created.append(created_curve)
        if progress_bar:
            progress_bar.update_progress(index + 1, len(output_curves))

    if not created:
        raise ScriptValidationError("No detail curves were created.")
    return created


# -----------------------------------------------------------------------------
# Reporting and logging
# -----------------------------------------------------------------------------

def print_report(output_mode, curve_method, detected_chain_type, source_rows, created_rows, skipped_ids,
                 construction_points, endpoint_gap, degree, engine):
    try:
        output.print_md("# {0}".format(TOOL_NAME))
        output.print_md("**Version:** {0}  ".format(VERSION))
        output.print_md("**Output mode:** {0}  ".format(output_mode))
        output.print_md("**Curve method:** {0}  ".format(curve_method))
        output.print_md("**Detected chain:** {0}  ".format(detected_chain_type))
        output.print_md("**Endpoint gap:** {0:.6f} ft  ".format(endpoint_gap))
        output.print_md("**Geometry engine:** {0}  ".format(engine))
        if degree:
            output.print_md("**NURBS degree:** {0}  ".format(degree))
        output.print_md("**Source curves:** {0}  ".format(len(source_rows)))
        output.print_md("**Construction points:** {0}  ".format(len(construction_points)))
        output.print_md("**Created curve element(s):** {0}  ".format(len(created_rows)))

        if skipped_ids:
            output.print_md("## Skipped non-curve selection")
            rows = []
            for element_id in skipped_ids:
                rows.append([get_element_link(element_id), "Not a model/detail curve"])
            if rows:
                output.print_table(rows, columns=["Element Id", "Reason"])

        if created_rows:
            output.print_md("## Created")
            output.print_table(created_rows, columns=["Element Id", "Type"])

        if source_rows:
            output.print_md("## Source")
            output.print_table(source_rows, columns=["Element Id", "Type", "Length (ft)"])
    except Exception as ex:
        logger.warning("The curves were created, but the output report could not be printed.")
        logger.warning(str(ex))
        output.print_md("# {0}".format(TOOL_NAME))
        output.print_md("## Completed with reporting warning")
        output.print_md("The curves were created, but the detailed report could not be printed.")
        output.print_md("```text\n{0}\n```".format(str(ex)))


def log_exception(message, exception_obj):
    logger.error(message)
    logger.error(str(exception_obj))
    logger.debug(traceback.format_exc())
    output.print_md("## Error")
    output.print_md(message)
    output.print_md("```text\n{0}\n```".format(str(exception_obj)))


# -----------------------------------------------------------------------------
# Main command
# -----------------------------------------------------------------------------

def run_command():
    if doc is None or uidoc is None:
        forms.alert("No active Revit document was found.", title=TOOL_NAME, exitscript=True)

    try:
        model_curves, detail_curves, skipped_ids = collect_selected_curve_elements(doc, uidoc)
    except UserCancelled as ex:
        forms.alert(str(ex), title=TOOL_NAME)
        logger.warning(str(ex))
        return
    except ScriptValidationError as ex:
        forms.alert(str(ex), title=TOOL_NAME)
        logger.warning(str(ex))
        output.print_md("# {0}".format(TOOL_NAME))
        output.print_md("## Validation stopped the command")
        output.print_md(str(ex))
        return

    source_elements = list(model_curves) + list(detail_curves)
    if not source_elements:
        forms.alert("Select at least one connected model line or detail line.", title=TOOL_NAME, exitscript=True)
        return

    source_report_rows = snapshot_source_report_rows(source_elements)

    try:
        with forms.ProgressBar(
            title="Ordering selected curves... {value}/{max_value}",
            cancellable=True
        ) as order_progress:
            order_progress.update_progress(1, 3)
            if order_progress.cancelled:
                raise UserCancelled("Operation cancelled.")
            chain = order_curves_into_single_chain(source_elements, JOIN_TOLERANCE_FT)
            order_progress.update_progress(2, 3)
            if order_progress.cancelled:
                raise UserCancelled("Operation cancelled.")
            detected_chain_type, endpoint_gap, chain_points = detect_chain_type(chain, CLOSED_CHAIN_TOLERANCE_FT)
            order_progress.update_progress(3, 3)

        output_mode, curve_method = ask_output_options(
            detected_chain_type,
            endpoint_gap,
            len(source_elements)
        )
    except UserCancelled as ex:
        forms.alert(str(ex), title=TOOL_NAME)
        logger.warning(str(ex))
        return
    except ScriptValidationError as ex:
        forms.alert(str(ex), title=TOOL_NAME)
        logger.warning(str(ex))
        output.print_md("# {0}".format(TOOL_NAME))
        output.print_md("## Validation stopped the command")
        output.print_md(str(ex))
        return

    is_closed = detected_chain_type == CHAIN_CLOSED
    created_elements = []
    created_report_rows = []
    construction_points = []
    degree_used = 0
    engine = ""
    output_curves = []
    sketch_plane = None
    sketch_plane_plane = None

    logger.info("{0} v{1} started".format(TOOL_NAME, VERSION))
    logger.info("Output mode: {0}".format(output_mode))
    logger.info("Curve method: {0}".format(curve_method))
    logger.info("Detected chain: {0}; endpoint gap: {1:.6f} ft".format(detected_chain_type, endpoint_gap))
    logger.info("Source model curve count: {0}".format(len(model_curves)))
    logger.info("Source detail curve count: {0}".format(len(detail_curves)))

    tg = TransactionGroup(doc, TOOL_NAME)
    tg.Start()

    try:
        with forms.ProgressBar(
            title="Building {0} ({1})... {{value}}/{{max_value}}".format(curve_method, detected_chain_type.lower()),
            cancellable=True
        ) as prep_progress:
            if curve_method == METHOD_FIT_CURVE:
                output_curves, construction_points, degree_used, engine = create_fit_curve_pieces(
                    chain_points,
                    is_closed,
                    prep_progress
                )
            else:
                output_curves, construction_points, degree_used, engine = create_spline_curve_pieces(
                    chain_points,
                    is_closed,
                    prep_progress
                )

        if output_mode == OUTPUT_MODEL_LINES:
            sketch_plane, sketch_plane_plane = get_model_output_sketch_plane_info(model_curves, doc.ActiveView)
            validate_points_on_plane(construction_points, sketch_plane_plane, JOIN_TOLERANCE_FT)

        line_style = get_preferred_line_style(source_elements)

        transaction = Transaction(doc, TOOL_NAME)
        transaction.Start()

        failure_handler = None
        if SUPPRESS_TRANSACTION_WARNINGS:
            try:
                failure_handler = WarningSwallower()
                failure_options = transaction.GetFailureHandlingOptions()
                failure_options.SetFailuresPreprocessor(failure_handler)
                try:
                    failure_options.SetClearAfterRollback(True)
                except Exception:
                    pass
                transaction.SetFailureHandlingOptions(failure_options)
            except Exception:
                logger.warning("Could not set failure preprocessor; continuing without warning suppression.")

        try:
            with forms.ProgressBar(
                title="Creating curve element(s)... {value}/{max_value}",
                cancellable=True
            ) as create_progress:
                if output_mode == OUTPUT_MODEL_LINES:
                    created_elements = create_model_curves(
                        doc,
                        output_curves,
                        sketch_plane,
                        sketch_plane_plane,
                        line_style,
                        create_progress
                    )
                else:
                    created_elements = create_detail_curves(
                        doc,
                        doc.ActiveView,
                        output_curves,
                        line_style,
                        create_progress
                    )

            doc.Regenerate()
            commit_result = transaction.Commit()
            try:
                commit_name = str(commit_result)
            except Exception:
                commit_name = ""
            if "RolledBack" in commit_name:
                failure_text = ""
                try:
                    if failure_handler and failure_handler.error_messages:
                        failure_text = " ".join(failure_handler.error_messages)
                except Exception:
                    failure_text = ""
                raise ScriptValidationError(
                    "Revit rejected the generated curve geometry and rolled back the transaction. {0}".format(failure_text)
                )
            created_report_rows = snapshot_created_report_rows(created_elements)
        except Exception:
            try:
                if transaction.HasStarted():
                    transaction.RollBack()
            except Exception:
                pass
            raise

        tg.Assimilate()

    except UserCancelled as ex:
        try:
            if tg.HasStarted():
                tg.RollBack()
        except Exception:
            pass
        forms.alert(str(ex), title=TOOL_NAME)
        logger.warning(str(ex))
        return

    except ScriptValidationError as ex:
        try:
            if tg.HasStarted():
                tg.RollBack()
        except Exception:
            pass
        forms.alert(str(ex), title=TOOL_NAME)
        logger.warning(str(ex))
        output.print_md("# {0}".format(TOOL_NAME))
        output.print_md("## Validation stopped the command")
        output.print_md(str(ex))
        return

    except Exception as ex:
        try:
            if tg.HasStarted():
                tg.RollBack()
        except Exception:
            pass
        log_exception("Unexpected error. No curve output was committed.", ex)
        forms.alert(
            "Unexpected error. No curve output was committed. See pyRevit output for details.",
            title=TOOL_NAME
        )
        return

    print_report(
        output_mode,
        curve_method,
        detected_chain_type,
        source_report_rows,
        created_report_rows,
        skipped_ids,
        construction_points,
        endpoint_gap,
        degree_used,
        engine
    )
    logger.info("{0} completed. Created {1} curve element(s).".format(TOOL_NAME, len(created_report_rows)))


run_command()
