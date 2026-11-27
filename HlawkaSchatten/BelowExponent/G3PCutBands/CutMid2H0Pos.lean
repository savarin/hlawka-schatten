/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H0PosPower

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid2H0Pos`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid2H0PosBox : Box := ⟨![0, 9/100, 0, -8], ![9/68, 11/100, 1, 8]⟩

set_option maxRecDepth 16000 in
def CutMid2H0PosTree : CertTree :=
  .cut 3 (3/4)
    (.cut 3 (-1/4)
      (.cut 3 (-2)
        (.row ⟨86531900008, 95281442641, (.direct 824633666698 809585452442), (.variance 207155922570)⟩)
        (.row ⟨86531900008, 95281442641, (.direct 30541785600 28698659849), (.variance 496703179333)⟩))
      (.cut 3 (1/4)
        (.cut 2 (1/2)
          (.cut 2 (1/8)
            (.cut 2 (1/16)
              (.row ⟨86531900008, 95281442641, (.direct 30541785600 31668201037), (.chord .universal 0 3393555298)⟩)
              (.row ⟨86531900008, 95281442641, (.direct 30541785600 31668201037), (.chord .universal 3393555298 10180665226)⟩))
            (.cut 2 (5/16)
              (.cut 2 (7/32)
                (.row ⟨86531900008, 95281442641, (.direct 30541785600 31668201037), (.chord .universal 10180665226 24716235638)⟩)
                (.row ⟨86531900008, 95281442641, (.direct 30541785600 31668201037), (.chord .universal 24716235638 43500686443)⟩))
              (.row ⟨86531900008, 95281442641, (.direct 30541785600 31668201037), (.chord .universal 43500686443 91625974997)⟩)))
          (.row ⟨86531900008, 95281442641, (.direct 30541785600 31668201037), (.chord .universal 91625974997 274877906944)⟩))
        (.row ⟨86531900008, 95281442641, (.direct 174227225485 174937057313), (.variance 488671898726)⟩)))
    (.cut 3 (2)
      (.cut 3 (5/4)
        (.cut 2 (1/2)
          (.cut 2 (1/8)
            (.cone)
            (.row ⟨86531900008, 95281442641, .zero, (.variance 309737727641)⟩))
          (.row ⟨86531900008, 95281442641, .zero, (.variance 309737727641)⟩))
        (.cut 2 (1/2)
          (.cut 2 (1/8)
            (.cut 3 (13/8)
              (.cut 3 (23/16)
                (.cut 3 (43/32)
                  (.row ⟨86531900008, 95281442641, (.direct 391506126583 390550995724), (.variance 250724582901)⟩)
                  (.row ⟨86531900008, 95281442641, (.direct 439055879922 437686017553), (.variance 243354291727)⟩))
                (.row ⟨86531900008, 95281442641, (.direct 488587506629 486774115456), (.variance 236673969141)⟩))
              (.row ⟨86531900008, 95281442641, (.direct 593382169971 590599578774), (.variance 224990204733)⟩))
            (.row ⟨86531900008, 95281442641, (.direct 391506126583 390550995724), (.variance 250724582901)⟩))
          (.row ⟨86531900008, 95281442641, (.direct 391506126583 390550995724), (.variance 250724582901)⟩)))
      (.cut 2 (1/2)
        (.cut 2 (1/8)
          (.cut 3 (5)
            (.cut 3 (7/2)
              (.cut 3 (11/4)
                (.cut 3 (19/8)
                  (.row ⟨86531900008, 95281442641, (.direct 824633666698 819608101796), (.variance 206489568225)⟩)
                  (.row ⟨86531900008, 95281442641, (.direct 1082810704946 1075171477174), (.variance 192323696513)⟩))
                (.row ⟨86531900008, 95281442641, (.direct 1366046989981 1355455524981), (.variance 181003987945)⟩))
              (.row ⟨86531900008, 95281442641, (.direct 2002014560937 1984595711632), (.variance 163805434931)⟩))
            (.cut 3 (13/2)
              (.row ⟨86531900008, 95281442641, (.direct 3523554676644 3489228722517), (.variance 141305361376)⟩)
              (.row ⟨86531900008, 95281442641, (.direct 5340438828596 5285421692856), (.variance 126745607266)⟩)))
          (.cut 3 (5)
            (.cut 3 (7/2)
              (.cut 3 (11/4)
                (.cut 3 (19/8)
                  (.row ⟨86531900008, 95281442641, (.direct 824633666698 819608101796), (.variance 206489568225)⟩)
                  (.row ⟨86531900008, 95281442641, (.direct 1082810704946 1075171477174), (.variance 192323696513)⟩))
                (.row ⟨86531900008, 95281442641, (.direct 1366046989981 1355455524981), (.variance 181003987945)⟩))
              (.cut 3 (17/4)
                (.row ⟨86531900008, 95281442641, (.direct 2002014560937 1984595711632), (.variance 163805434931)⟩)
                (.row ⟨86531900008, 95281442641, (.direct 2723407729414 2698043946997), (.variance 151148134408)⟩)))
            (.cut 3 (13/2)
              (.row ⟨86531900008, 95281442641, (.direct 3523554676644 3489228722517), (.variance 141305361376)⟩)
              (.row ⟨86531900008, 95281442641, (.direct 5340438828596 5285421692856), (.variance 126745607266)⟩))))
        (.cut 3 (5)
          (.row ⟨86531900008, 95281442641, (.direct 824633666698 819608101796), (.variance 206489568225)⟩)
          (.cut 3 (13/2)
            (.row ⟨86531900008, 95281442641, (.direct 3523554676644 3489228722517), (.variance 141305361376)⟩)
            (.row ⟨86531900008, 95281442641, (.direct 5340438828596 5285421692856), (.variance 126745607266)⟩)))))

set_option maxRecDepth 16000 in
theorem CutMid2H0Pos_checked : CutMid2H0PosTree.geometryOK CutMid2H0PosPowerCache CutMid2H0PosBox true = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
