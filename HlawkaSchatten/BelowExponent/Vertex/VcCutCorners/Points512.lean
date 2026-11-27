/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.VcCornerData.Points512

/-! Checked corner data shared by the vertex middle and band regions: `Points512`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

def vcCutP512 : SideCornerEntry := ⟨3/40, 17/40, 0, #v[31345947/2500000000, 95038059/10000000000, 86506/9765625]⟩
abbrev vcCutP512Roots := vcOuterP512Roots
theorem vcCutP512_roots : vcCutP512.cell.rootsOK vcCutP512Roots = true := by decide +kernel

def vcCutP513 : SideCornerEntry := ⟨3/40, 17/40, 1/36, #v[65732677/5000000000, 24815677/2500000000, 92845103/10000000000]⟩
abbrev vcCutP513Roots := vcOuterP513Roots
theorem vcCutP513_roots : vcCutP513.cell.rootsOK vcCutP513Roots = true := by decide +kernel

def vcCutP514 : SideCornerEntry := ⟨3/40, 17/40, 1/18, #v[65732677/5000000000, 24815677/2500000000, 92845103/10000000000]⟩
abbrev vcCutP514Roots := vcOuterP514Roots
theorem vcCutP514_roots : vcCutP514.cell.rootsOK vcCutP514Roots = true := by decide +kernel

def vcCutP515 : SideCornerEntry := ⟨3/40, 9/20, 0, #v[25401917/2000000000, 92114013/10000000000, 93242191/10000000000]⟩
abbrev vcCutP515Roots := vcOuterP515Roots
theorem vcCutP515_roots : vcCutP515.cell.rootsOK vcCutP515Roots = true := by decide +kernel

def vcCutP516 : SideCornerEntry := ⟨3/40, 9/20, 1/36, #v[133284271/10000000000, 96203479/10000000000, 24453891/2500000000]⟩
abbrev vcCutP516Roots := vcOuterP516Roots
theorem vcCutP516_roots : vcCutP516.cell.rootsOK vcCutP516Roots = true := by decide +kernel

def vcCutP517 : SideCornerEntry := ⟨3/40, 9/20, 1/18, #v[133284271/10000000000, 96203479/10000000000, 24453891/2500000000]⟩
abbrev vcCutP517Roots := vcOuterP517Roots
theorem vcCutP517_roots : vcCutP517.cell.rootsOK vcCutP517Roots = true := by decide +kernel

def vcCutP518 : SideCornerEntry := ⟨3/40, 19/40, 0, #v[25401917/2000000000, 22891161/2500000000, 93242191/10000000000]⟩
abbrev vcCutP518Roots := vcOuterP518Roots
theorem vcCutP518_roots : vcCutP518.cell.rootsOK vcCutP518Roots = true := by decide +kernel

def vcCutP519 : SideCornerEntry := ⟨3/40, 19/40, 1/36, #v[133284271/10000000000, 47834919/5000000000, 24453891/2500000000]⟩
abbrev vcCutP519Roots := vcOuterP519Roots
theorem vcCutP519_roots : vcCutP519.cell.rootsOK vcCutP519Roots = true := by decide +kernel

def vcCutP520 : SideCornerEntry := ⟨3/40, 19/40, 1/18, #v[133284271/10000000000, 47834919/5000000000, 24453891/2500000000]⟩
abbrev vcCutP520Roots := vcOuterP520Roots
theorem vcCutP520_roots : vcCutP520.cell.rootsOK vcCutP520Roots = true := by decide +kernel

def vcCutP521 : SideCornerEntry := ⟨7/80, 1/10, 0, #v[102856179/2500000000, 401898043/10000000000, 199968729/10000000000]⟩
abbrev vcCutP521Roots := vcOuterP521Roots
theorem vcCutP521_roots : vcCutP521.cell.rootsOK vcCutP521Roots = true := by decide +kernel

def vcCutP522 : SideCornerEntry := ⟨7/80, 1/10, 1/72, #v[102856179/2500000000, 401898043/10000000000, 199968729/10000000000]⟩
abbrev vcCutP522Roots := vcOuterP522Roots
theorem vcCutP522_roots : vcCutP522.cell.rootsOK vcCutP522Roots = true := by decide +kernel

def vcCutP523 : SideCornerEntry := ⟨7/80, 1/10, 1/36, #v[245023207/10000000000, 241852387/10000000000, 105315891/10000000000]⟩
abbrev vcCutP523Roots := vcOuterP523Roots
theorem vcCutP523_roots : vcCutP523.cell.rootsOK vcCutP523Roots = true := by decide +kernel

def vcCutP524 : SideCornerEntry := ⟨7/80, 1/10, 1/24, #v[252433461/10000000000, 15574497/625000000, 1347987/125000000]⟩
abbrev vcCutP524Roots := vcOuterP524Roots
theorem vcCutP524_roots : vcCutP524.cell.rootsOK vcCutP524Roots = true := by decide +kernel

def vcCutP525 : SideCornerEntry := ⟨7/80, 1/10, 1/18, #v[252433461/10000000000, 15574497/625000000, 1347987/125000000]⟩
abbrev vcCutP525Roots := vcOuterP525Roots
theorem vcCutP525_roots : vcCutP525.cell.rootsOK vcCutP525Roots = true := by decide +kernel

def vcCutP526 : SideCornerEntry := ⟨7/80, 9/80, 0, #v[102856179/2500000000, 401898043/10000000000, 199968729/10000000000]⟩
abbrev vcCutP526Roots := vcOuterP526Roots
theorem vcCutP526_roots : vcCutP526.cell.rootsOK vcCutP526Roots = true := by decide +kernel

def vcCutP527 : SideCornerEntry := ⟨7/80, 9/80, 1/72, #v[102856179/2500000000, 401898043/10000000000, 199968729/10000000000]⟩
abbrev vcCutP527Roots := vcOuterP527Roots
theorem vcCutP527_roots : vcCutP527.cell.rootsOK vcCutP527Roots = true := by decide +kernel

def vcCutP528 : SideCornerEntry := ⟨7/80, 9/80, 1/36, #v[295032763/10000000000, 143504433/5000000000, 144011737/10000000000]⟩
abbrev vcCutP528Roots := vcOuterP528Roots
theorem vcCutP528_roots : vcCutP528.cell.rootsOK vcCutP528Roots = true := by decide +kernel

def vcCutP529 : SideCornerEntry := ⟨7/80, 9/80, 1/24, #v[304248971/10000000000, 296017583/10000000000, 147525571/10000000000]⟩
abbrev vcCutP529Roots := vcOuterP529Roots
theorem vcCutP529_roots : vcCutP529.cell.rootsOK vcCutP529Roots = true := by decide +kernel

def vcCutP530 : SideCornerEntry := ⟨7/80, 9/80, 1/18, #v[304248971/10000000000, 296017583/10000000000, 147525571/10000000000]⟩
abbrev vcCutP530Roots := vcOuterP530Roots
theorem vcCutP530_roots : vcCutP530.cell.rootsOK vcCutP530Roots = true := by decide +kernel

def vcCutP531 : SideCornerEntry := ⟨7/80, 1/8, 0, #v[55292763/2000000000, 26884787/1000000000, 13706867/1000000000]⟩
abbrev vcCutP531Roots := vcOuterP531Roots
theorem vcCutP531_roots : vcCutP531.cell.rootsOK vcCutP531Roots = true := by decide +kernel

def vcCutP532 : SideCornerEntry := ⟨7/80, 1/8, 1/72, #v[142886429/5000000000, 277954941/10000000000, 140529157/10000000000]⟩
abbrev vcCutP532Roots := vcOuterP532Roots
theorem vcCutP532_roots : vcCutP532.cell.rootsOK vcCutP532Roots = true := by decide +kernel

def vcCutP533 : SideCornerEntry := ⟨7/80, 1/8, 1/36, #v[295032763/10000000000, 143504433/5000000000, 144011737/10000000000]⟩
abbrev vcCutP533Roots := vcOuterP533Roots
theorem vcCutP533_roots : vcCutP533.cell.rootsOK vcCutP533Roots = true := by decide +kernel

def vcCutP534 : SideCornerEntry := ⟨7/80, 1/8, 1/24, #v[304248971/10000000000, 296017583/10000000000, 147525571/10000000000]⟩
abbrev vcCutP534Roots := vcOuterP534Roots
theorem vcCutP534_roots : vcCutP534.cell.rootsOK vcCutP534Roots = true := by decide +kernel

def vcCutP535 : SideCornerEntry := ⟨7/80, 1/8, 1/18, #v[304248971/10000000000, 296017583/10000000000, 147525571/10000000000]⟩
abbrev vcCutP535Roots := vcOuterP535Roots
theorem vcCutP535_roots : vcCutP535.cell.rootsOK vcCutP535Roots = true := by decide +kernel

def vcCutP536 : SideCornerEntry := ⟨7/80, 11/80, 1/36, #v[20932901/1000000000, 40464009/2000000000, 25924439/2500000000]⟩
abbrev vcCutP536Roots := vcOuterP536Roots
theorem vcCutP536_roots : vcCutP536.cell.rootsOK vcCutP536Roots = true := by decide +kernel

def vcCutP537 : SideCornerEntry := ⟨7/80, 11/80, 1/24, #v[107909213/5000000000, 208598207/10000000000, 106244547/10000000000]⟩
abbrev vcCutP537Roots := vcOuterP537Roots
theorem vcCutP537_roots : vcCutP537.cell.rootsOK vcCutP537Roots = true := by decide +kernel

def vcCutP538 : SideCornerEntry := ⟨7/80, 11/80, 1/18, #v[107909213/5000000000, 208598207/10000000000, 106244547/10000000000]⟩
abbrev vcCutP538Roots := vcOuterP538Roots
theorem vcCutP538_roots : vcCutP538.cell.rootsOK vcCutP538Roots = true := by decide +kernel

def vcCutP539 : SideCornerEntry := ⟨7/80, 3/20, 1/36, #v[31088343/2000000000, 37259281/2500000000, 77667349/10000000000]⟩
abbrev vcCutP539Roots := vcOuterP539Roots
theorem vcCutP539_roots : vcCutP539.cell.rootsOK vcCutP539Roots = true := by decide +kernel

def vcCutP540 : SideCornerEntry := ⟨7/80, 3/20, 1/24, #v[80102671/5000000000, 153600017/10000000000, 39793933/5000000000]⟩
abbrev vcCutP540Roots := vcOuterP540Roots
theorem vcCutP540_roots : vcCutP540.cell.rootsOK vcCutP540Roots = true := by decide +kernel

def vcCutP541 : SideCornerEntry := ⟨7/80, 3/20, 1/18, #v[80102671/5000000000, 153600017/10000000000, 39793933/5000000000]⟩
abbrev vcCutP541Roots := vcOuterP541Roots
theorem vcCutP541_roots : vcCutP541.cell.rootsOK vcCutP541Roots = true := by decide +kernel

def vcCutP542 : SideCornerEntry := ⟨1/10, 1/10, 0, #v[102856179/2500000000, 401898043/10000000000, 199968729/10000000000]⟩
abbrev vcCutP542Roots := vcOuterP542Roots
theorem vcCutP542_roots : vcCutP542.cell.rootsOK vcCutP542Roots = true := by decide +kernel

def vcCutP543 : SideCornerEntry := ⟨1/10, 1/10, 1/72, #v[102856179/2500000000, 401898043/10000000000, 199968729/10000000000]⟩
abbrev vcCutP543Roots := vcOuterP543Roots
theorem vcCutP543_roots : vcCutP543.cell.rootsOK vcCutP543Roots = true := by decide +kernel

def vcCutPoints512 : Array SideCornerEntry := #[
  vcCutP512,
  vcCutP513,
  vcCutP514,
  vcCutP515,
  vcCutP516,
  vcCutP517,
  vcCutP518,
  vcCutP519,
  vcCutP520,
  vcCutP521,
  vcCutP522,
  vcCutP523,
  vcCutP524,
  vcCutP525,
  vcCutP526,
  vcCutP527,
  vcCutP528,
  vcCutP529,
  vcCutP530,
  vcCutP531,
  vcCutP532,
  vcCutP533,
  vcCutP534,
  vcCutP535,
  vcCutP536,
  vcCutP537,
  vcCutP538,
  vcCutP539,
  vcCutP540,
  vcCutP541,
  vcCutP542,
  vcCutP543]

end HlawkaSchatten.BelowExponent.Vertex
