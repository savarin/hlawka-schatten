/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PRatioData

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid4H0NegChartPart1`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid4H0NegChartPart1Box : Box := (((((⟨![0, 13/100, 0, -1], ![9/68, 3/20, 1, 1]⟩ : Box)).lowerChild 3 (1/4)).upperChild 3 (-1/4)).lowerChild 2 (1/2)).lowerChild 2 (1/8)

set_option maxRecDepth 16000 in
def CutMid4H0NegChartPart1Tree : RatioChart :=
  .cut 1 (7/50)
    (.cut 0 (9/136)
      (.cut 1 (27/200)
        (.cut 3 (0)
          (.cut 3 (-1/8)
            (.row ⟨103236350715, 105123556200, (.direct 1131165907 1408762563), 0, 10180665226, 374416013081/274877906944, .leaf (.secant 993888389401 30541785600 3082652371 10180561190)⟩)
            (.row ⟨103236350715, 105123556200, (.direct 377054043 572734614), 0, 10180665226, 126238934899/68719476736, .leaf (.secant 907805998772 10180561190 3715346965 0)⟩))
          (.row ⟨103236350715, 105123556200, (.direct 0 57888903), 0, 10180665226, 2, .leaf .universal⟩))
        (.cut 3 (0)
          (.cut 3 (-1/8)
            (.row ⟨105123556199, 106974752992, (.direct 1131165907 1420277278), 0, 10180665226, 374416013081/274877906944, .leaf (.secant 993888389401 30541785600 3082652371 10180561190)⟩)
            (.row ⟨105123556199, 106974752992, (.direct 377054043 581138010), 0, 10180665226, 126238934899/68719476736, .leaf (.secant 907805998772 10180561190 3715346965 0)⟩))
          (.row ⟨105123556199, 106974752992, (.direct 0 61585225), 0, 10180665226, 2, .leaf .universal⟩)))
      (.cut 1 (27/200)
        (.cut 0 (27/272)
          (.cut 3 (0)
            (.row ⟨103236350715, 105123556200, (.direct 885283551 1278876748), 0, 10180665226, 133942293449/68719476736, .leaf (.secant 947956812746 18760293062 7064759841 0)⟩)
            (.row ⟨103236350715, 105123556200, (.direct 54693626 21934538), 0, 10180665226, 2, .leaf .universal⟩))
          (.cut 3 (0)
            (.row ⟨103236350715, 105123556200, (.direct 770084941 1284787342), 0, 10180665226, 540012363615/274877906944, .leaf (.secant 925293052316 13697376423 11146040162 0)⟩)
            (.row ⟨103236350715, 105123556200, (.direct 104382604 23309515), 0, 10180665226, 2, .leaf .universal⟩)))
        (.cut 0 (27/272)
          (.cut 3 (0)
            (.row ⟨105123556199, 106974752992, (.direct 875578187 1284543576), 0, 10180665226, 133942293449/68719476736, .leaf (.secant 947956812746 18760293062 7064759841 0)⟩)
            (.row ⟨105123556199, 106974752992, (.direct 58329623 23252246), 0, 10180665226, 2, .leaf .universal⟩))
          (.cut 3 (0)
            (.row ⟨105123556199, 106974752992, (.direct 756209786 1290523671), 0, 10180665226, 540012363615/274877906944, .leaf (.secant 925293052316 13697376423 11146040162 0)⟩)
            (.row ⟨105123556199, 106974752992, (.direct 111338833 24670922), 0, 10180665226, 2, .leaf .universal⟩)))))
    (.cut 0 (9/136)
      (.cut 1 (29/200)
        (.cut 3 (0)
          (.row ⟨106974752991, 108791878640, (.direct 1131165907 1431888905), 0, 10180665226, 537816322705/274877906944, .leaf (.secant 993888389401 30541785600 3715346965 0)⟩)
          (.row ⟨106974752991, 108791878640, (.direct 0 65385911), 0, 10180665226, 2, .leaf .universal⟩))
        (.cut 3 (0)
          (.row ⟨108791878639, 110576703735, (.direct 1131165907 1443598438), 0, 10180665226, 537816322705/274877906944, .leaf (.secant 993888389401 30541785600 3715346965 0)⟩)
          (.row ⟨108791878639, 110576703735, (.direct 0 69291164), 0, 10180665226, 2, .leaf .universal⟩)))
      (.cut 1 (29/200)
        (.cut 0 (27/272)
          (.row ⟨106974752991, 108791878640, (.direct 865856799 1290252614), 0, 10180665226, 2, .leaf .universal⟩)
          (.row ⟨106974752991, 108791878640, (.direct 742346178 1296303992), 0, 10180665226, 2, .leaf .universal⟩))
        (.cut 1 (59/400)
          (.row ⟨108791878639, 109688224065, (.direct 856119710 1445279597), 0, 10180665226, 2, .leaf .universal⟩)
          (.cut 0 (27/272)
            (.row ⟨109688224064, 110576703735, (.direct 851245384 1290368237), 0, 10180665226, 2, .leaf .universal⟩)
            (.row ⟨109688224064, 110576703735, (.direct 721575519 1293641774), 0, 10180665226, 2, .leaf .universal⟩)))))

set_option maxRecDepth 16000 in
theorem CutMid4H0NegChartPart1_ok : CutMid4H0NegChartPart1Tree.ok CutMid4H0NegChartPart1Box false = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
