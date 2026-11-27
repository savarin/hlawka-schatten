/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop2H4NegPart0`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop2H4NegPart0Box : Box := (((⟨![9/34, 17/100, 0, -8], ![45/136, 9/50, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).lowerChild 3 (-1/4)

set_option maxRecDepth 16000 in
def CutTop2H4NegPart0Tree : CertTree :=
  .cut 3 (-2)
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.cut 3 (-5)
          (.row ⟨117423580139, 120689819475, (.direct 3523554676644 3306804207167), (.variance 143306326991)⟩)
          (.row ⟨117423580139, 120689819475, (.direct 824633666698 761406255512), (.variance 210511015968)⟩))
        (.cut 3 (-5)
          (.cut 3 (-13/2)
            (.row ⟨117423580139, 120689819475, (.direct 5340438828596 5024423834452), (.variance 128437548241)⟩)
            (.row ⟨117423580139, 120689819475, (.direct 3523554676644 3306804207167), (.variance 143306326991)⟩))
          (.cut 3 (-7/2)
            (.row ⟨117423580139, 120689819475, (.direct 2002014560937 1870170915423), (.variance 166372583786)⟩)
            (.row ⟨117423580139, 120689819475, (.direct 824633666698 761406255512), (.variance 210511015968)⟩))))
      (.cut 3 (-5)
        (.cut 3 (-13/2)
          (.row ⟨117423580139, 120689819475, (.direct 5340438828596 5024423834452), (.variance 128437548241)⟩)
          (.row ⟨117423580139, 120689819475, (.direct 3523554676644 3306804207167), (.variance 143306326991)⟩))
        (.cut 3 (-7/2)
          (.row ⟨117423580139, 120689819475, (.direct 2002014560937 1870170915423), (.variance 166372583786)⟩)
          (.row ⟨117423580139, 120689819475, (.direct 824633666698 761406255512), (.variance 210511015968)⟩))))
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.row ⟨117423580139, 120689819475, (.direct 30541785600 23009515951), (.variance 526287977843)⟩)
        (.cut 3 (-9/8)
          (.row ⟨117423580139, 120689819475, (.direct 331294831298 299429369868), (.variance 268788511792)⟩)
          (.cut 3 (-11/16)
            (.row ⟨117423580139, 120689819475, (.direct 151782739331 132918591369), (.variance 332483962268)⟩)
            (.cut 3 (-15/32)
              (.row ⟨117423580139, 120689819475, (.direct 82716570280 69683027156), (.variance 393741784376)⟩)
              (.cut 2 (5/16)
                (.row ⟨117423580139, 120689819475, (.direct 30541785600 23009515951), (.variance 526287977843)⟩)
                (.cut 3 (-23/64)
                  (.row ⟨117423580139, 120689819475, (.direct 54287234842 44029161800), (.chord (.midpoint ⟨322246246747, 230348472241, 234494262674, 307681607252, 257520546962, 131815558913⟩) 43500686443 91625974997)⟩)
                  (.row ⟨117423580139, 120689819475, (.direct 30541785600 23009515951), (.chord (.midpoint ⟨425338423810, 150174273028, 193870489263, 352145178706, 219908513636, 209014735236⟩) 43500686443 91625974997)⟩)))))))
      (.cut 3 (-9/8)
        (.row ⟨117423580139, 120689819475, (.direct 331294831298 299429369868), (.variance 268788511792)⟩)
        (.cut 3 (-11/16)
          (.row ⟨117423580139, 120689819475, (.direct 151782739331 132918591369), (.variance 332483962268)⟩)
          (.cut 3 (-15/32)
            (.row ⟨117423580139, 120689819475, (.direct 82716570280 69683027156), (.variance 393741784376)⟩)
            (.cut 2 (3/4)
              (.cut 3 (-23/64)
                (.row ⟨117423580139, 120689819475, (.direct 54287234842 44029161800), (.chord (.midpoint ⟨424486602621, 150754966000, 194213219342, 351704150823, 220221968771, 241919410024⟩) 91625974997 174227471798)⟩)
                (.row ⟨117423580139, 120689819475, (.direct 30541785600 23009515951), (.chord (.midpoint ⟨498864372403, 104577306877, 163433683799, 397508405639, 192415196479, 277637295764⟩) 91625974997 174227471798)⟩))
              (.row ⟨117423580139, 120689819475, (.direct 30541785600 23009515951), (.chord (.midpoint ⟨537227132092, 84133458496, 146605960175, 429366470596, 177571636299, 289442456088⟩) 174227471798 274877906944)⟩))))))

set_option maxRecDepth 16000 in
theorem CutTop2H4NegPart0_checked : CutTop2H4NegPart0Tree.commonOK CutTop2H4NegPart0Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
