/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H3NegPower

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid2H3NegRestPart12`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid2H3NegRestPart12Box : Box := (((((((((((((⟨![27/68, 9/100, 0, -8], ![9/17, 11/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).lowerChild 2 (1/8)).upperChild 3 (0)).lowerChild 3 (1/8)).lowerChild 3 (1/16)).lowerChild 1 (1/10)).lowerChild 3 (1/32)).lowerChild 1 (19/200)).upperChild 0 (63/136)

set_option maxRecDepth 16000 in
def CutMid2H3NegRestPart12Tree : RatioRemainder :=
  .cut 1 (37/400)
    (.cut 0 (135/272)
      (.cut 1 (73/800)
        (.cut 0 (261/544)
          (.cut 1 (29/320)
            (.cut 3 (1/64)
              (.cut 2 (1/16)
                (.original (.row ⟨86531900008, 86819820706, (.direct 377054043 1544874863), (.variance 1344351398726)⟩))
                (.covered))
              (.cut 2 (1/16)
                (.original (.row ⟨86531900008, 86819820706, (.direct 1131165907 2637439342), (.variance 1078564736569)⟩))
                (.covered)))
            (.cut 3 (1/64)
              (.cut 2 (1/16)
                (.original (.row ⟨86819820705, 87106710699, (.direct 377054043 1555314178), (.variance 1340313562439)⟩))
                (.covered))
              (.cut 2 (1/16)
                (.original (.row ⟨86819820705, 87106710699, (.direct 1131165907 2649950383), (.variance 1076685082763)⟩))
                (.covered))))
          (.cut 3 (1/64)
            (.cut 2 (1/16)
              (.original (.row ⟨86531900008, 87106710699, (.direct 377054043 1605850203), (.variance 1324913863132)⟩))
              (.covered))
            (.cut 2 (1/16)
              (.original (.row ⟨86531900008, 87106710699, (.direct 1131165907 2710387166), (.variance 1069441686692)⟩))
              (.covered))))
        (.cut 0 (261/544)
          (.cut 1 (147/1600)
            (.cut 3 (1/64)
              (.cut 2 (1/16)
                (.original (.row ⟨87106710698, 87392580700, (.direct 377054043 1565786281), (.variance 1336314174068)⟩))
                (.covered))
              (.cut 2 (1/16)
                (.original (.row ⟨87106710698, 87392580700, (.direct 1131165907 2662491479), (.variance 1074815330601)⟩))
                (.covered)))
            (.cut 3 (1/64)
              (.cut 2 (1/16)
                (.original (.row ⟨87392580699, 87677441236, (.direct 377054043 1576291186), (.variance 1332352602469)⟩))
                (.covered))
              (.cut 2 (1/16)
                (.original (.row ⟨87392580699, 87677441236, (.direct 1131165907 2675062654), (.variance 1072955388584)⟩))
                (.covered))))
          (.cut 3 (1/64)
            (.cut 2 (1/16)
              (.original (.row ⟨87106710698, 87677441236, (.direct 377054043 1627808915), (.variance 1316992846067)⟩))
              (.covered))
            (.cut 2 (1/16)
              (.original (.row ⟨87106710698, 87677441236, (.direct 1131165907 2736583396), (.variance 1065669554869)⟩))
              (.covered)))))
      (.cut 3 (1/64)
        (.cut 2 (1/16)
          (.original (.row ⟨86531900008, 87677441236, (.direct 377054043 1732666126), (.variance 1306402308743)⟩))
          (.covered))
        (.cut 2 (1/16)
          (.original (.row ⟨86531900008, 87677441236, (.direct 1131165907 2861166062), (.variance 1060576483104)⟩))
          (.covered))))
    (.cut 0 (135/272)
      (.cut 1 (3/32)
        (.cut 0 (261/544)
          (.cut 1 (149/1600)
            (.cut 3 (1/64)
              (.cut 2 (1/16)
                (.original (.row ⟨87677441235, 87961302658, (.direct 377054043 1586828904), (.variance 1328428231068)⟩))
                (.covered))
              (.cut 2 (1/16)
                (.original (.row ⟨87677441235, 87961302658, (.direct 1131165907 2687663933), (.variance 1071105166406)⟩))
                (.covered)))
            (.cut 3 (1/64)
              (.cut 2 (1/16)
                (.original (.row ⟨87961302657, 88244175140, (.direct 377054043 1597399448), (.variance 1324540457435)⟩))
                (.covered))
              (.cut 2 (1/16)
                (.original (.row ⟨87961302657, 88244175140, (.direct 1131165907 2700295340), (.variance 1069264574936)⟩))
                (.covered))))
          (.cut 3 (1/64)
            (.cut 2 (1/16)
              (.original (.row ⟨87677441235, 88244175140, (.direct 377054043 1649906516), (.variance 1309220923328)⟩))
              (.covered))
            (.cut 2 (1/16)
              (.original (.row ⟨87677441235, 88244175140, (.direct 1131165907 2762907043), (.variance 1061937547705)⟩))
              (.covered))))
        (.cut 3 (1/64)
          (.cut 2 (1/16)
            (.original (.row ⟨88244175139, 88806993133, (.direct 377054043 1672143106), (.variance 1320688692863)⟩))
            (.covered))
          (.cut 2 (1/16)
            (.original (.row ⟨88244175139, 88806993133, (.direct 1131165907 2789358308), (.variance 1067433526194)⟩))
            (.covered))))
      (.cut 3 (1/64)
        (.cut 2 (1/16)
          (.original (.row ⟨87677441235, 88806993133, (.direct 377054043 1781064227), (.variance 1290928629011)⟩))
          (.covered))
        (.cut 2 (1/16)
          (.original (.row ⟨87677441235, 88806993133, (.direct 1131165907 2918399358), (.variance 1053032051987)⟩))
          (.covered))))

set_option maxRecDepth 16000 in
theorem CutMid2H3NegRestPart12_ok : CutMid2H3NegRestPart12Tree.geometryOK CutMid2H3NegPowerCache CutMid2H3NegRestPart12Box false (1) = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
