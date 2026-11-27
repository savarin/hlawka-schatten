/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.VcCutCorners.PointTable
public import HlawkaSchatten.BelowExponent.Vertex.VcCutCorners.Witnesses000
public import HlawkaSchatten.BelowExponent.Vertex.VcCutCorners.Witnesses032
public import HlawkaSchatten.BelowExponent.Vertex.VcCutCorners.Witnesses064
public import HlawkaSchatten.BelowExponent.Vertex.VcCutCorners.Witnesses096
public import HlawkaSchatten.BelowExponent.Vertex.VcCutCorners.Witnesses128
public import HlawkaSchatten.BelowExponent.Vertex.VcCutCorners.Witnesses160
public import HlawkaSchatten.BelowExponent.Vertex.VcCutCorners.Witnesses192
public import HlawkaSchatten.BelowExponent.Vertex.VcCutCorners.Witnesses224
public import HlawkaSchatten.BelowExponent.Vertex.VcCutCorners.Witnesses256
public import HlawkaSchatten.BelowExponent.Vertex.VcCutCorners.Witnesses288
public import HlawkaSchatten.BelowExponent.Vertex.VcCutCorners.Witnesses320
public import HlawkaSchatten.BelowExponent.Vertex.VcCutCorners.Witnesses352
public import HlawkaSchatten.BelowExponent.Vertex.VcCutCorners.Witnesses384
public import HlawkaSchatten.BelowExponent.Vertex.VcCutCorners.Witnesses416
public import HlawkaSchatten.BelowExponent.Vertex.VcCutCorners.Witnesses448
public import HlawkaSchatten.BelowExponent.Vertex.VcCutCorners.Witnesses480
public import HlawkaSchatten.BelowExponent.Vertex.VcCutCorners.Witnesses512
public import HlawkaSchatten.BelowExponent.Vertex.VcCutCorners.Witnesses544
public import HlawkaSchatten.BelowExponent.Vertex.VcCutCorners.Witnesses576
public import HlawkaSchatten.BelowExponent.Vertex.VcCutCorners.Witnesses608
public import HlawkaSchatten.BelowExponent.Vertex.VcCutCorners.Witnesses640
public import HlawkaSchatten.BelowExponent.Vertex.VcCutCorners.Witnesses672
public import HlawkaSchatten.BelowExponent.Vertex.VcCutCorners.Witnesses704
public import HlawkaSchatten.BelowExponent.Vertex.VcCutCorners.Witnesses736
public import HlawkaSchatten.BelowExponent.Vertex.VcCutCorners.Witnesses768
public import HlawkaSchatten.BelowExponent.Vertex.VcCutCorners.Witnesses800
public import HlawkaSchatten.BelowExponent.Vertex.VcCutCorners.Witnesses832
public import HlawkaSchatten.BelowExponent.Vertex.VcCutCorners.Witnesses864

/-! Checked corner data shared by the vertex middle and band regions: `Complete`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

set_option maxRecDepth 10000

theorem vcCutPoints_checked : SideCornerEntriesOK (fun _ => True) vcCutPoints.toList := by
  simp only [vcCutPoints, Array.toList_append, List.append_assoc]
  apply sideCornerEntriesOK_append vcCutWitnesses000
  apply sideCornerEntriesOK_append vcCutWitnesses032
  apply sideCornerEntriesOK_append vcCutWitnesses064
  apply sideCornerEntriesOK_append vcCutWitnesses096
  apply sideCornerEntriesOK_append vcCutWitnesses128
  apply sideCornerEntriesOK_append vcCutWitnesses160
  apply sideCornerEntriesOK_append vcCutWitnesses192
  apply sideCornerEntriesOK_append vcCutWitnesses224
  apply sideCornerEntriesOK_append vcCutWitnesses256
  apply sideCornerEntriesOK_append vcCutWitnesses288
  apply sideCornerEntriesOK_append vcCutWitnesses320
  apply sideCornerEntriesOK_append vcCutWitnesses352
  apply sideCornerEntriesOK_append vcCutWitnesses384
  apply sideCornerEntriesOK_append vcCutWitnesses416
  apply sideCornerEntriesOK_append vcCutWitnesses448
  apply sideCornerEntriesOK_append vcCutWitnesses480
  apply sideCornerEntriesOK_append vcCutWitnesses512
  apply sideCornerEntriesOK_append vcCutWitnesses544
  apply sideCornerEntriesOK_append vcCutWitnesses576
  apply sideCornerEntriesOK_append vcCutWitnesses608
  apply sideCornerEntriesOK_append vcCutWitnesses640
  apply sideCornerEntriesOK_append vcCutWitnesses672
  apply sideCornerEntriesOK_append vcCutWitnesses704
  apply sideCornerEntriesOK_append vcCutWitnesses736
  apply sideCornerEntriesOK_append vcCutWitnesses768
  apply sideCornerEntriesOK_append vcCutWitnesses800
  apply sideCornerEntriesOK_append vcCutWitnesses832
  exact vcCutWitnesses864

end HlawkaSchatten.BelowExponent.Vertex
