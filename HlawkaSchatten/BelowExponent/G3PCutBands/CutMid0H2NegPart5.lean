/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid0H2NegPart5`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid0H2NegPart5Box : Box := ((((((((⟨![9/34, 1/20, 0, -8], ![27/68, 7/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).upperChild 2 (1/8)).lowerChild 2 (5/16)).upperChild 2 (7/32)

set_option maxRecDepth 16000 in
def CutMid0H2NegPart5Tree : CertTree :=
  .cut 3 (0)
    (.cut 1 (3/50)
      (.cut 1 (11/200)
        (.row ⟨65259754744, 68314662357, (.direct 0 223323981), (.chord .universal 24716235638 43500686443)⟩)
        (.row ⟨68314662356, 71228276419, (.direct 0 257395293), (.chord .universal 24716235638 43500686443)⟩))
      (.cut 3 (-1/8)
        (.row ⟨71228276418, 76698504229, (.direct 10180561190 8170056160), (.chord (.midpoint ⟨461737237222, 126507588818, 179038812905, 372602419929, 206421025917, 184719095761⟩) 24716235638 43500686443)⟩)
        (.cut 1 (13/200)
          (.cut 0 (45/136)
            (.row ⟨71228276418, 74018153447, (.direct 0 219772980), (.chord .universal 24716235638 43500686443)⟩)
            (.row ⟨71228276418, 74018153447, (.direct 0 293409111), (.chord .universal 24716235638 43500686443)⟩))
          (.cut 0 (45/136)
            (.cut 1 (27/400)
              (.row ⟨74018153446, 75371237552, (.direct 0 233798863), (.chord .universal 24716235638 43500686443)⟩)
              (.row ⟨75371237551, 76698504229, (.direct 0 248179994), (.chord .universal 24716235638 43500686443)⟩))
            (.cut 1 (27/400)
              (.cut 3 (-1/16)
                (.row ⟨74018153446, 75371237552, (.direct 3393509060 2215999894), (.chord (.midpoint ⟨531698542976, 86944810705, 140704428795, 442067463527, 179738897690, 288884290428⟩) 24716235638 43500686443)⟩)
                (.row ⟨74018153446, 75371237552, (.direct 0 312134441), (.chord .universal 24716235638 43500686443)⟩))
              (.cut 3 (-1/16)
                (.row ⟨75371237551, 76698504229, (.direct 3393509060 2174556786), (.chord (.midpoint ⟨532704749911, 86429803147, 140235877662, 443114918547, 179345223727, 289237321565⟩) 24716235638 43500686443)⟩)
                (.cut 3 (-1/32)
                  (.row ⟨75371237551, 76698504229, (.direct 1131165907 407086736), (.chord (.midpoint ⟨588553125262, 60140625193, 112736788608, 517336881305, 156878193083, 330932176679⟩) 24716235638 43500686443)⟩)
                  (.row ⟨75371237551, 76698504229, (.direct 0 331334049), (.chord (.secant 658267391284 33506576118 87430759680 5876074092) 24716235638 43500686443)⟩))))))))
    (.cut 3 (1/8)
      (.cut 1 (3/50)
        (.cut 3 (1/16)
          (.cut 3 (1/32)
            (.row ⟨65259754744, 71228276419, (.direct 1131165907 1886159957), (.chord (.secant 780984323930 3830618418 58159151152 635476937) 24716235638 43500686443)⟩)
            (.row ⟨65259754744, 71228276419, (.direct 3393509060 4436417048), (.chord (.secant 873275146194 4400790786 35731141214 9674226526) 24716235638 43500686443)⟩))
          (.row ⟨65259754744, 71228276419, (.direct 10180561190 11602203600), (.chord (.secant 1069005001641 53444106301 17620804253 25005350768) 24716235638 43500686443)⟩))
        (.cut 3 (1/16)
          (.cut 3 (1/32)
            (.cut 0 (45/136)
              (.row ⟨71228276418, 76698504229, (.direct 1131165907 1867450194), (.chord (.secant 780192334673 3942508493 41789042214 855339494) 24716235638 43500686443)⟩)
              (.row ⟨71228276418, 76698504229, (.direct 1131165907 2030490679), (.chord (.secant 744926814133 10083777473 55474222295 1218253672) 24716235638 43500686443)⟩))
            (.row ⟨71228276418, 76698504229, (.direct 3393509060 4626800462), (.chord (.secant 879350109582 5292360204 34845124796 10229530750) 24716235638 43500686443)⟩))
          (.row ⟨71228276418, 76698504229, (.direct 10180561190 11854609116), (.chord (.secant 1075112964662 55477657471 16961849296 25764631059) 24716235638 43500686443)⟩)))
      (.row ⟨65259754744, 76698504229, (.direct 30541785600 32659646221), (.chord (.secant 1508441256594 243979363610 646012755 69241878428) 24716235638 43500686443)⟩))

set_option maxRecDepth 16000 in
theorem CutMid0H2NegPart5_checked : CutMid0H2NegPart5Tree.commonOK CutMid0H2NegPart5Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
