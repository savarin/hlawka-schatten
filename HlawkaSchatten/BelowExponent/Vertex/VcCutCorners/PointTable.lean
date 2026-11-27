/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.VcCutCorners.Points000
public import HlawkaSchatten.BelowExponent.Vertex.VcCutCorners.Points032
public import HlawkaSchatten.BelowExponent.Vertex.VcCutCorners.Points064
public import HlawkaSchatten.BelowExponent.Vertex.VcCutCorners.Points096
public import HlawkaSchatten.BelowExponent.Vertex.VcCutCorners.Points128
public import HlawkaSchatten.BelowExponent.Vertex.VcCutCorners.Points160
public import HlawkaSchatten.BelowExponent.Vertex.VcCutCorners.Points192
public import HlawkaSchatten.BelowExponent.Vertex.VcCutCorners.Points224
public import HlawkaSchatten.BelowExponent.Vertex.VcCutCorners.Points256
public import HlawkaSchatten.BelowExponent.Vertex.VcCutCorners.Points288
public import HlawkaSchatten.BelowExponent.Vertex.VcCutCorners.Points320
public import HlawkaSchatten.BelowExponent.Vertex.VcCutCorners.Points352
public import HlawkaSchatten.BelowExponent.Vertex.VcCutCorners.Points384
public import HlawkaSchatten.BelowExponent.Vertex.VcCutCorners.Points416
public import HlawkaSchatten.BelowExponent.Vertex.VcCutCorners.Points448
public import HlawkaSchatten.BelowExponent.Vertex.VcCutCorners.Points480
public import HlawkaSchatten.BelowExponent.Vertex.VcCutCorners.Points512
public import HlawkaSchatten.BelowExponent.Vertex.VcCutCorners.Points544
public import HlawkaSchatten.BelowExponent.Vertex.VcCutCorners.Points576
public import HlawkaSchatten.BelowExponent.Vertex.VcCutCorners.Points608
public import HlawkaSchatten.BelowExponent.Vertex.VcCutCorners.Points640
public import HlawkaSchatten.BelowExponent.Vertex.VcCutCorners.Points672
public import HlawkaSchatten.BelowExponent.Vertex.VcCutCorners.Points704
public import HlawkaSchatten.BelowExponent.Vertex.VcCutCorners.Points736
public import HlawkaSchatten.BelowExponent.Vertex.VcCutCorners.Points768
public import HlawkaSchatten.BelowExponent.Vertex.VcCutCorners.Points800
public import HlawkaSchatten.BelowExponent.Vertex.VcCutCorners.Points832
public import HlawkaSchatten.BelowExponent.Vertex.VcCutCorners.Points864

/-! Checked corner data shared by the vertex middle and band regions: `PointTable`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

def vcCutPointBlocks : List (Array SideCornerEntry) := [
  vcCutPoints000,
  vcCutPoints032,
  vcCutPoints064,
  vcCutPoints096,
  vcCutPoints128,
  vcCutPoints160,
  vcCutPoints192,
  vcCutPoints224,
  vcCutPoints256,
  vcCutPoints288,
  vcCutPoints320,
  vcCutPoints352,
  vcCutPoints384,
  vcCutPoints416,
  vcCutPoints448,
  vcCutPoints480,
  vcCutPoints512,
  vcCutPoints544,
  vcCutPoints576,
  vcCutPoints608,
  vcCutPoints640,
  vcCutPoints672,
  vcCutPoints704,
  vcCutPoints736,
  vcCutPoints768,
  vcCutPoints800,
  vcCutPoints832,
  vcCutPoints864]

def vcCutPoints : Array SideCornerEntry :=
  vcCutPoints000 ++
  vcCutPoints032 ++
  vcCutPoints064 ++
  vcCutPoints096 ++
  vcCutPoints128 ++
  vcCutPoints160 ++
  vcCutPoints192 ++
  vcCutPoints224 ++
  vcCutPoints256 ++
  vcCutPoints288 ++
  vcCutPoints320 ++
  vcCutPoints352 ++
  vcCutPoints384 ++
  vcCutPoints416 ++
  vcCutPoints448 ++
  vcCutPoints480 ++
  vcCutPoints512 ++
  vcCutPoints544 ++
  vcCutPoints576 ++
  vcCutPoints608 ++
  vcCutPoints640 ++
  vcCutPoints672 ++
  vcCutPoints704 ++
  vcCutPoints736 ++
  vcCutPoints768 ++
  vcCutPoints800 ++
  vcCutPoints832 ++
  vcCutPoints864

theorem vcCutPoints_toList :
    vcCutPointBlocks.flatMap Array.toList = vcCutPoints.toList := by
  simp only [vcCutPointBlocks, vcCutPoints, List.flatMap_cons, List.flatMap_nil,
    Array.toList_append, List.append_nil, List.append_assoc]

end HlawkaSchatten.BelowExponent.Vertex
