/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H0NegPower

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop2H0NegRestPart0`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop2H0NegRestPart0Box : Box := (((⟨![0, 17/100, 0, -8], ![9/136, 9/50, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).lowerChild 3 (-1/4)

set_option maxRecDepth 16000 in
def CutTop2H0NegRestPart0Tree : RatioRemainder :=
  .cut 3 (-2)
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.cut 3 (-5)
          (.original (.row ⟨117423580139, 120689819475, (.direct 3523554676644 3479821180798), (.variance 141405293929)⟩))
          (.original (.row ⟨117423580139, 120689819475, (.direct 824633666698 811841829266), (.variance 207005003013)⟩)))
        (.cut 3 (-5)
          (.cut 3 (-13/2)
            (.original (.row ⟨117423580139, 120689819475, (.direct 5340438828596 5276706773707), (.variance 126800388366)⟩))
            (.original (.row ⟨117423580139, 120689819475, (.direct 3523554676644 3479821180798), (.variance 141405293929)⟩)))
          (.cut 3 (-7/2)
            (.original (.row ⟨117423580139, 120689819475, (.direct 2002014560937 1975390951458), (.variance 164004963087)⟩))
            (.original (.row ⟨117423580139, 120689819475, (.direct 824633666698 811841829266), (.variance 207005003013)⟩)))))
      (.cut 3 (-5)
        (.cut 3 (-13/2)
          (.original (.row ⟨117423580139, 120689819475, (.direct 5340438828596 5276706773707), (.variance 126800388366)⟩))
          (.original (.row ⟨117423580139, 120689819475, (.direct 3523554676644 3479821180798), (.variance 141405293929)⟩)))
        (.cut 3 (-7/2)
          (.original (.row ⟨117423580139, 120689819475, (.direct 2002014560937 1975390951458), (.variance 164004963087)⟩))
          (.original (.row ⟨117423580139, 120689819475, (.direct 824633666698 811841829266), (.variance 207005003013)⟩)))))
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.original (.row ⟨117423580139, 120689819475, (.direct 30541785600 28973094456), (.variance 495466852363)⟩))
        (.cut 3 (-9/8)
          (.original (.row ⟨117423580139, 120689819475, (.direct 331294831298 324827016547), (.variance 263118919003)⟩))
          (.cut 3 (-11/16)
            (.original (.row ⟨117423580139, 120689819475, (.direct 151782739331 147936499157), (.variance 323293484681)⟩))
            (.cut 2 (5/16)
              (.cut 3 (-15/32)
                (.original (.row ⟨117423580139, 120689819475, (.direct 82716570280 80044461616), (.variance 379705106445)⟩))
                (.original (.row ⟨117423580139, 120689819475, (.direct 30541785600 28973094456), (.variance 495466852363)⟩)))
              (.cut 3 (-15/32)
                (.original (.row ⟨117423580139, 120689819475, (.direct 82716570280 80044461616), (.variance 379705106445)⟩))
                (.cut 3 (-23/64)
                  (.original (.row ⟨117423580139, 120689819475, (.direct 54287234842 52172811953), (.variance 424739587906)⟩))
                  (.cut 2 (13/32)
                    (.original (.row ⟨117423580139, 120689819475, (.direct 30541785600 28973094456), (.chord (.midpoint ⟨471065462553, 120792945151, 202929839876, 340917384491, 202929322524, 238375158869⟩) 43500686443 65931360876)⟩))
                    (.covered))))))))
      (.cut 3 (-9/8)
        (.original (.row ⟨117423580139, 120689819475, (.direct 331294831298 324827016547), (.variance 263118919003)⟩))
        (.cut 3 (-11/16)
          (.original (.row ⟨117423580139, 120689819475, (.direct 151782739331 147936499157), (.variance 323293484681)⟩))
          (.cut 3 (-15/32)
            (.original (.row ⟨117423580139, 120689819475, (.direct 82716570280 80044461616), (.variance 379705106445)⟩))
            (.covered)))))

set_option maxRecDepth 16000 in
theorem CutTop2H0NegRestPart0_ok : CutTop2H0NegRestPart0Tree.geometryOK CutTop2H0NegPowerCache CutTop2H0NegRestPart0Box false (1) = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
