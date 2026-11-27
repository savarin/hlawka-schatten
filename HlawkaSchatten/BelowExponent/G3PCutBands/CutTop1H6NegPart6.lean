/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop1H6NegPart6`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop1H6NegPart6Box : Box := ((((((((((⟨![27/68, 4/25, 0, -8], ![63/136, 17/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).upperChild 2 (1/8)).lowerChild 3 (0)).upperChild 2 (5/16)).upperChild 3 (-1/8)).lowerChild 3 (-1/16)

set_option maxRecDepth 16000 in
def CutTop1H6NegPart6Tree : CertTree :=
  .cut 0 (117/272)
    (.cut 3 (-3/32)
      (.row ⟨114055813619, 117423580140, (.direct 6452795533 2386014261), (.chord (.midpoint ⟨524259168803, 90798827624, 135551186107, 453926767306, 182639255996, 319629275751⟩) 43500686443 91625974997)⟩)
      (.cut 2 (13/32)
        (.cut 1 (33/200)
          (.row ⟨114055813619, 115752966124, (.direct 3393509060 620947201), (.chord (.midpoint ⟨550708436856, 77465048864, 122515659684, 487687546806, 172241414243, 333369190784⟩) 43500686443 65931360876)⟩)
          (.row ⟨115752966123, 117423580140, (.direct 3393509060 559542801), (.chord (.midpoint ⟨552595902886, 76552460248, 121557268532, 490412550374, 171489722969, 333945988432⟩) 43500686443 65931360876)⟩))
        (.row ⟨114055813619, 117423580140, (.direct 3393509060 559542801), (.chord (.midpoint ⟨557820170029, 74053307422, 118882521437, 498215842056, 169401806359, 339131277110⟩) 65931360876 91625974997)⟩)))
    (.cut 2 (13/32)
      (.cut 3 (-3/32)
        (.row ⟨114055813619, 117423580140, (.direct 6452795533 2137001691), (.chord (.midpoint ⟨498017433239, 105053650900, 143706774290, 435494529614, 192738202765, 316333283912⟩) 43500686443 65931360876)⟩)
        (.row ⟨114055813619, 117423580140, (.direct 3393509060 422090899), (.chord (.midpoint ⟨538541149338, 83471851244, 123980032259, 483593533965, 177054985554, 330130365528⟩) 43500686443 65931360876)⟩))
      (.row ⟨114055813619, 117423580140, (.direct 3393509060 422090899), (.chord (.midpoint ⟨542871672391, 81309273835, 121775579852, 489788599695, 175347973546, 325158140836⟩) 65931360876 91625974997)⟩))

set_option maxRecDepth 16000 in
theorem CutTop1H6NegPart6_checked : CutTop1H6NegPart6Tree.commonOK CutTop1H6NegPart6Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
