/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid2H3NegPart8`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid2H3NegPart8Box : Box := (((((((((((⟨![27/68, 9/100, 0, -8], ![9/17, 11/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).lowerChild 2 (1/8)).lowerChild 3 (0)).upperChild 1 (1/10)).lowerChild 1 (21/200)).upperChild 3 (-1/8)).lowerChild 0 (63/136)

set_option maxRecDepth 16000 in
def CutMid2H3NegPart8Tree : CertTree :=
  .cut 1 (41/400)
    (.cut 3 (-1/16)
      (.row ⟨91020629597, 92105866080, (.direct 3393509060 1410146290), (.chord .universal 0 10180665226)⟩)
      (.cut 0 (117/272)
        (.cut 1 (81/800)
          (.cut 3 (-1/32)
            (.row ⟨91020629597, 91564989626, (.direct 1131165907 120206801), (.chord .universal 0 10180665226)⟩)
            (.cut 0 (225/544)
              (.row ⟨91020629597, 91564989626, (.direct 0 651128685), (.chord .universal 0 10180665226)⟩)
              (.row ⟨91020629597, 91564989626, (.direct 0 692889580), (.chord .universal 0 10180665226)⟩)))
          (.cut 3 (-1/32)
            (.row ⟨91564989625, 92105866080, (.direct 1131165907 112578324), (.chord .universal 0 10180665226)⟩)
            (.cut 0 (225/544)
              (.row ⟨91564989625, 92105866080, (.direct 0 664608868), (.chord .universal 0 10180665226)⟩)
              (.row ⟨91564989625, 92105866080, (.direct 0 707234331), (.chord .universal 0 10180665226)⟩))))
        (.cut 1 (81/800)
          (.cut 3 (-1/32)
            (.row ⟨91020629597, 91564989626, (.direct 1131165907 77881285), (.chord .universal 0 10180665226)⟩)
            (.cut 0 (243/544)
              (.cut 1 (161/1600)
                (.row ⟨91020629597, 91293249160, (.direct 0 728037083), (.chord .universal 0 10180665226)⟩)
                (.row ⟨91293249159, 91564989626, (.direct 0 735600853), (.chord .universal 0 10180665226)⟩))
              (.cut 1 (161/1600)
                (.cut 3 (-1/64)
                  (.row ⟨91020629597, 91293249160, (.direct 377054043 165668745), (.chord .universal 0 10180665226)⟩)
                  (.row ⟨91020629597, 91293249160, (.direct 0 771235160), (.chord .universal 0 10180665226)⟩))
                (.cut 3 (-1/64)
                  (.row ⟨91293249159, 91564989626, (.direct 377054043 170296525), (.chord .universal 0 10180665226)⟩)
                  (.row ⟨91293249159, 91564989626, (.direct 0 779247726), (.chord .universal 0 10180665226)⟩)))))
          (.cut 3 (-1/32)
            (.row ⟨91564989625, 92105866080, (.direct 1131165907 70917416), (.chord .universal 0 10180665226)⟩)
            (.cut 0 (243/544)
              (.cut 1 (163/1600)
                (.row ⟨91564989625, 91835859230, (.direct 0 743198445), (.chord .universal 0 10180665226)⟩)
                (.row ⟨91835859229, 92105866080, (.direct 0 750829846), (.chord .universal 0 10180665226)⟩))
              (.cut 1 (163/1600)
                (.cut 3 (-1/64)
                  (.row ⟨91564989625, 91835859230, (.direct 377054043 174974286), (.chord .universal 0 10180665226)⟩)
                  (.row ⟨91564989625, 91835859230, (.direct 0 787296122), (.chord .universal 0 10180665226)⟩))
                (.cut 3 (-1/64)
                  (.row ⟨91835859229, 92105866080, (.direct 377054043 179701792), (.chord .universal 0 10180665226)⟩)
                  (.row ⟨91835859229, 92105866080, (.direct 0 795380332), (.chord .universal 0 10180665226)⟩))))))))
    (.cut 3 (-1/16)
      (.row ⟨92105866079, 93177423805, (.direct 3393509060 1367790816), (.chord .universal 0 10180665226)⟩)
      (.cut 0 (117/272)
        (.cut 1 (83/800)
          (.cut 3 (-1/32)
            (.row ⟨92105866079, 92643323332, (.direct 1131165907 105126353), (.chord .universal 0 10180665226)⟩)
            (.cut 0 (225/544)
              (.row ⟨92105866079, 92643323332, (.direct 0 678208699), (.chord .universal 0 10180665226)⟩)
              (.row ⟨92105866079, 92643323332, (.direct 0 721706403), (.chord .universal 0 10180665226)⟩)))
          (.cut 3 (-1/32)
            (.row ⟨92643323331, 93177423805, (.direct 1131165907 97854994), (.chord .universal 0 10180665226)⟩)
            (.cut 0 (225/544)
              (.row ⟨92643323331, 93177423805, (.direct 0 691928076), (.chord .universal 0 10180665226)⟩)
              (.row ⟨92643323331, 93177423805, (.direct 0 736305688), (.chord .universal 0 10180665226)⟩))))
        (.cut 1 (83/800)
          (.cut 3 (-1/32)
            (.row ⟨92105866079, 92643323332, (.direct 1131165907 64188593), (.chord .universal 0 10180665226)⟩)
            (.cut 0 (243/544)
              (.cut 1 (33/320)
                (.row ⟨92105866079, 92375018160, (.direct 0 758495038), (.chord .universal 0 10180665226)⟩)
                (.row ⟨92375018159, 92643323332, (.direct 0 766194009), (.chord .universal 0 10180665226)⟩))
              (.cut 1 (33/320)
                (.row ⟨92105866079, 92375018160, (.direct 0 803500338), (.chord .universal 0 10180665226)⟩)
                (.row ⟨92375018159, 92643323332, (.direct 0 811656127), (.chord .universal 0 10180665226)⟩))))
          (.cut 3 (-1/32)
            (.row ⟨92643323331, 93177423805, (.direct 1131165907 57702248), (.chord .universal 0 10180665226)⟩)
            (.cut 0 (243/544)
              (.row ⟨92643323331, 93177423805, (.direct 0 781693227), (.chord .universal 0 10180665226)⟩)
              (.cut 1 (167/1600)
                (.row ⟨92643323331, 92910789338, (.direct 0 819847683), (.chord .universal 0 10180665226)⟩)
                (.row ⟨92910789337, 93177423805, (.direct 0 828074991), (.chord .universal 0 10180665226)⟩)))))))

set_option maxRecDepth 16000 in
theorem CutMid2H3NegPart8_checked : CutMid2H3NegPart8Tree.commonOK CutMid2H3NegPart8Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
