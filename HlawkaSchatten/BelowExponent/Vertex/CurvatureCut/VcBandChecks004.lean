/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.CurvatureCut.VcBandInputs128
meta import HlawkaSchatten.BelowExponent.Vertex.CurvatureReplay
meta import HlawkaSchatten.BelowExponent.Vertex.CurvatureCut.VcBandInputs128

/-! Kernel arithmetic proofs for the closed curvature subcells. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

theorem vcS1128Cut_layer0 : gridLayerCurvatureOK
    vcS1128CutCell vcS1128CutRoots 1 1 1 vcS1128CutCaps vcS1128CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcS1129Cut_layer0 : gridLayerCurvatureOK
    vcS1129CutCell vcS1129CutRoots 1 1 1 vcS1129CutCaps vcS1129CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcS1130Cut_layer0 : gridLayerCurvatureOK
    vcS1130CutCell vcS1130CutRoots 1 1 1 vcS1130CutCaps vcS1130CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcS1131Cut_layer0 : gridLayerCurvatureOK
    vcS1131CutCell vcS1131CutRoots 1 1 1 vcS1131CutCaps vcS1131CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcS1132Cut_layer0 : gridLayerCurvatureOK
    vcS1132CutCell vcS1132CutRoots 1 1 1 vcS1132CutCaps vcS1132CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcS1133Cut_layer0 : gridLayerCurvatureOK
    vcS1133CutCell vcS1133CutRoots 1 1 1 vcS1133CutCaps vcS1133CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcS1134Cut_layer0 : gridLayerCurvatureOK
    vcS1134CutCell vcS1134CutRoots 1 1 1 vcS1134CutCaps vcS1134CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcS1135Cut_layer0 : gridLayerCurvatureOK
    vcS1135CutCell vcS1135CutRoots 1 1 1 vcS1135CutCaps vcS1135CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcS1136Cut_layer0 : gridLayerCurvatureOK
    vcS1136CutCell vcS1136CutRoots 1 1 1 vcS1136CutCaps vcS1136CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcS1137Cut_layer0 : gridLayerCurvatureOK
    vcS1137CutCell vcS1137CutRoots 1 1 1 vcS1137CutCaps vcS1137CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcS1138Cut_layer0 : gridLayerCurvatureOK
    vcS1138CutCell vcS1138CutRoots 1 1 1 vcS1138CutCaps vcS1138CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcS1139Cut_layer0 : gridLayerCurvatureOK
    vcS1139CutCell vcS1139CutRoots 1 1 1 vcS1139CutCaps vcS1139CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcS1140Cut_layer0 : gridLayerCurvatureOK
    vcS1140CutCell vcS1140CutRoots 1 1 1 vcS1140CutCaps vcS1140CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcS1141Cut_layer0 : gridLayerCurvatureOK
    vcS1141CutCell vcS1141CutRoots 1 1 1 vcS1141CutCaps vcS1141CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcS1142Cut_layer0 : gridLayerCurvatureOK
    vcS1142CutCell vcS1142CutRoots 1 1 1 vcS1142CutCaps vcS1142CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcS1143Cut_layer0 : gridLayerCurvatureOK
    vcS1143CutCell vcS1143CutRoots 1 1 1 vcS1143CutCaps vcS1143CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcS1144Cut_layer0 : gridLayerCurvatureOK
    vcS1144CutCell vcS1144CutRoots 1 1 1 vcS1144CutCaps vcS1144CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcS1145Cut_layer0 : gridLayerCurvatureOK
    vcS1145CutCell vcS1145CutRoots 1 1 1 vcS1145CutCaps vcS1145CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcS1146Cut_layer0 : gridLayerCurvatureOK
    vcS1146CutCell vcS1146CutRoots 1 1 1 vcS1146CutCaps vcS1146CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcS1147Cut_layer0 : gridLayerCurvatureOK
    vcS1147CutCell vcS1147CutRoots 1 1 1 vcS1147CutCaps vcS1147CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcS1148Cut_layer0 : gridLayerCurvatureOK
    vcS1148CutCell vcS1148CutRoots 1 1 1 vcS1148CutCaps vcS1148CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcS1149Cut_layer0 : gridLayerCurvatureOK
    vcS1149CutCell vcS1149CutRoots 1 1 1 vcS1149CutCaps vcS1149CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcS1150Cut_layer0 : gridLayerCurvatureOK
    vcS1150CutCell vcS1150CutRoots 1 1 1 vcS1150CutCaps vcS1150CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcS1151Cut_layer0 : gridLayerCurvatureOK
    vcS1151CutCell vcS1151CutRoots 1 1 1 vcS1151CutCaps vcS1151CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcS1152Cut_layer0 : gridLayerCurvatureOK
    vcS1152CutCell vcS1152CutRoots 1 1 1 vcS1152CutCaps vcS1152CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcS1153Cut_layer0 : gridLayerCurvatureOK
    vcS1153CutCell vcS1153CutRoots 1 1 1 vcS1153CutCaps vcS1153CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcS1154Cut_layer0 : gridLayerCurvatureOK
    vcS1154CutCell vcS1154CutRoots 1 1 1 vcS1154CutCaps vcS1154CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcS1155Cut_layer0 : gridLayerCurvatureOK
    vcS1155CutCell vcS1155CutRoots 1 1 1 vcS1155CutCaps vcS1155CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcS1156Cut_layer0 : gridLayerCurvatureOK
    vcS1156CutCell vcS1156CutRoots 1 1 1 vcS1156CutCaps vcS1156CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcS1157Cut_layer0 : gridLayerCurvatureOK
    vcS1157CutCell vcS1157CutRoots 1 1 1 vcS1157CutCaps vcS1157CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcS1158Cut_layer0 : gridLayerCurvatureOK
    vcS1158CutCell vcS1158CutRoots 1 1 1 vcS1158CutCaps vcS1158CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcS1159Cut_layer0 : gridLayerCurvatureOK
    vcS1159CutCell vcS1159CutRoots 1 1 1 vcS1159CutCaps vcS1159CutWeightFloor 0 = true := by
  replay_curvature_layer


end HlawkaSchatten.BelowExponent.Vertex
