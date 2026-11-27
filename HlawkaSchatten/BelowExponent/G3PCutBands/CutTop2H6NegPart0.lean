/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop2H6NegPart0`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop2H6NegPart0Box : Box := (((⟨![27/68, 17/100, 0, -8], ![63/136, 9/50, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).lowerChild 3 (-1/4)

set_option maxRecDepth 16000 in
def CutTop2H6NegPart0Tree : CertTree :=
  .cut 3 (-2)
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.cut 3 (-5)
          (.row ⟨117423580139, 120689819475, (.direct 3523554676644 3221522351205), (.variance 144290164442)⟩)
          (.row ⟨117423580139, 120689819475, (.direct 824633666698 736638677859), (.variance 212341840852)⟩))
        (.cut 3 (-5)
          (.cut 3 (-13/2)
            (.row ⟨117423580139, 120689819475, (.direct 5340438828596 4900000267632), (.variance 129283665743)⟩)
            (.row ⟨117423580139, 120689819475, (.direct 3523554676644 3221522351205), (.variance 144290164442)⟩))
          (.cut 3 (-7/2)
            (.row ⟨117423580139, 120689819475, (.direct 2002014560937 1818361804203), (.variance 167601021762)⟩)
            (.row ⟨117423580139, 120689819475, (.direct 824633666698 736638677859), (.variance 212341840852)⟩))))
      (.cut 3 (-5)
        (.cut 3 (-13/2)
          (.row ⟨117423580139, 120689819475, (.direct 5340438828596 4900000267632), (.variance 129283665743)⟩)
          (.row ⟨117423580139, 120689819475, (.direct 3523554676644 3221522351205), (.variance 144290164442)⟩))
        (.cut 3 (-7/2)
          (.row ⟨117423580139, 120689819475, (.direct 2002014560937 1818361804203), (.variance 167601021762)⟩)
          (.row ⟨117423580139, 120689819475, (.direct 824633666698 736638677859), (.variance 212341840852)⟩))))
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.row ⟨117423580139, 120689819475, (.direct 30541785600 20221724010), (.variance 544391043063)⟩)
        (.cut 3 (-9/8)
          (.row ⟨117423580139, 120689819475, (.direct 331294831298 287018749459), (.variance 271784503711)⟩)
          (.cut 3 (-11/16)
            (.row ⟨117423580139, 120689819475, (.direct 151782739331 125634200282), (.variance 337427489839)⟩)
            (.cut 3 (-15/32)
              (.row ⟨117423580139, 120689819475, (.direct 82716570280 64703492174), (.variance 401460847620)⟩)
              (.cut 2 (5/16)
                (.row ⟨117423580139, 120689819475, (.direct 30541785600 20221724010), (.variance 544391043063)⟩)
                (.cut 3 (-23/64)
                  (.row ⟨117423580139, 120689819475, (.direct 54287234842 40151423914), (.chord (.midpoint ⟨278699476078, 271075847002, 239954630346, 302697343674, 273468503058, 110360048753⟩) 43500686443 91625974997)⟩)
                  (.row ⟨117423580139, 120689819475, (.direct 30541785600 20221724010), (.chord (.midpoint ⟨375484978967, 186352793192, 200676805802, 343628661169, 238143648979, 193183959167⟩) 43500686443 91625974997)⟩)))))))
      (.cut 3 (-9/8)
        (.row ⟨117423580139, 120689819475, (.direct 331294831298 287018749459), (.variance 271784503711)⟩)
        (.cut 3 (-11/16)
          (.row ⟨117423580139, 120689819475, (.direct 151782739331 125634200282), (.variance 337427489839)⟩)
          (.cut 3 (-15/32)
            (.row ⟨117423580139, 120689819475, (.direct 82716570280 64703492174), (.variance 401460847620)⟩)
            (.cut 2 (3/4)
              (.row ⟨117423580139, 120689819475, (.direct 30541785600 20221724010), (.chord (.midpoint ⟨440204316653, 140240388017, 173528703231, 380958709411, 214423470177, 224530864347⟩) 91625974997 174227471798)⟩)
              (.row ⟨117423580139, 120689819475, (.direct 30541785600 20221724010), (.chord (.midpoint ⟨473968424764, 119042917015, 158762634406, 405771359059, 201839249372, 272296313112⟩) 174227471798 274877906944)⟩))))))

set_option maxRecDepth 16000 in
theorem CutTop2H6NegPart0_checked : CutTop2H6NegPart0Tree.commonOK CutTop2H6NegPart0Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
