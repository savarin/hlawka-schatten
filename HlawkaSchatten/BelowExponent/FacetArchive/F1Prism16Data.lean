/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.FacetNumeric

/-! Archived facet prism certificate data: `F1Prism16Data`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true

@[expose] public section

namespace HlawkaSchatten.BelowExponent.FacetNumeric

def f1Archived16 : Prism := {
  vertices := [⟨80000, 35200, 12800, 0⟩,
    ⟨69600, 47200, 11200, 0⟩,
    ⟨75600, 42000, 10400, 0⟩,
    ⟨79800, 35112, 12768, 320⟩,
    ⟨69426, 47082, 11172, 320⟩,
    ⟨75411, 41895, 10374, 320⟩]
  profileDen := 128000
  pi := [120283088, 183417377, 246975694, 523065665]
  slope := [228709785, -18614323, -237705961]
  radiusNum := 1
  radiusDen := 8
}

set_option maxRecDepth 40000
set_option maxHeartbeats 0

theorem f1Archived16_data_ok : dataOK f1Archived16 = true := by decide +kernel

def f1Archived16Chart0 : RowTree :=
  (.splitA
    (.splitB
      (.splitA
        (.splitB
          (.splitA
            (.splitB
              (.splitA
                (.splitB
                  (.splitA
                    (.splitB
                      (.splitA
                        (.box 128 125)
                        (.box 124 125)
                      )
                      (.splitB
                        (.box 125 120)
                        (.splitA
                          (.box 127 116)
                          (.box 124 116)
                        )
                      )
                    )
                    (.splitB
                      (.box 120 125)
                      (.box 120 117)
                    )
                  )
                  (.splitA
                    (.splitB
                      (.box 125 111)
                      (.box 125 104)
                    )
                    (.splitB
                      (.box 119 111)
                      (.box 119 104)
                    )
                  )
                )
                (.splitB
                  (.box 111 121)
                  (.box 111 105)
                )
              )
              (.splitA
                (.splitB
                  (.box 121 92)
                  (.box 121 79)
                )
                (.splitB
                  (.box 108 92)
                  (.box 108 76)
                )
              )
            )
            (.splitB
              (.box 92 113)
              (.splitB
                (.box 92 89)
                (.box 87 76)
              )
            )
          )
          (.splitB
            (.splitA
              (.box 113 177)
              (.splitB
                (.box 81 177)
                (.box 81 145)
              )
            )
            (.splitA
              (.box 113 193)
              (.splitB
                (.box 81 225)
                (.box 81 257)
              )
            )
          )
        )
        (.splitB
          (.splitB
            (.box 65 97)
            (.box 161 81)
          )
          (.splitB
            (.splitA
              (.box 161 161)
              (.box 193 129)
            )
            (.splitA
              (.splitB
                (.splitA
                  (.box 177 225)
                  (.box 145 193)
                )
                (.splitA
                  (.box 161 257)
                  (.splitB
                    (.splitA
                      (.box 153 273)
                      (.box 137 272)
                    )
                    (.splitA
                      (.box 145 353)
                      (.splitB
                        (.splitA
                          (.box 141 353)
                          (.box 133 353)
                        )
                        (.box 137 321)
                      )
                    )
                  )
                )
              )
              (.splitA
                (.splitB
                  (.box 225 193)
                  (.splitB
                    (.box 242 273)
                    (.splitB
                      (.box 242 354)
                      (.box 241 321)
                    )
                  )
                )
                (.box 193 257)
              )
            )
          )
        )
      )
      (.splitA
        (.splitB
          (.splitA
            (.box 113 193)
            (.box 65 193)
          )
          (.box 84 65)
        )
        (.splitB
          (.splitA
            (.splitB
              (.splitA
                (.box 177 0)
                (.box 145 0)
              )
              (.box 161 161)
            )
            (.splitB
              (.splitA
                (.box 225 0)
                (.box 257 0)
              )
              (.box 193 161)
            )
          )
          (.box 129 97)
        )
      )
    )
    (.splitB
      (.splitB
        (.box 0 97)
        (.splitA
          (.box 0 193)
          (.box 97 129)
        )
      )
      (.splitB
        (.splitA
          (.box 0 193)
          (.box 97 129)
        )
        (.box 65 97)
      )
    )
  )

theorem f1Archived16Chart0_ok : checkChart f1Archived16 0 1 2 f1Archived16Chart0 = true := by decide +kernel

def f1Archived16Chart1 : RowTree :=
  (.splitA
    (.splitB
      (.splitA
        (.splitB
          (.box 84 65)
          (.splitA
            (.box 113 193)
            (.box 81 193)
          )
        )
        (.splitB
          (.box 129 97)
          (.splitA
            (.splitB
              (.box 161 161)
              (.box 161 257)
            )
            (.box 129 193)
          )
        )
      )
      (.splitB
        (.splitA
          (.splitB
            (.splitA
              (.box 113 193)
              (.box 81 193)
            )
            (.splitA
              (.box 113 177)
              (.box 81 176)
            )
          )
          (.splitB
            (.splitA
              (.splitB
                (.box 161 257)
                (.box 161 225)
              )
              (.box 193 257)
            )
            (.box 161 161)
          )
        )
        (.splitA
          (.splitA
            (.splitB
              (.splitA
                (.splitB
                  (.box 121 79)
                  (.box 121 92)
                )
                (.splitB
                  (.box 108 76)
                  (.box 108 92)
                )
              )
              (.splitA
                (.splitB
                  (.splitA
                    (.splitB
                      (.box 125 104)
                      (.box 125 111)
                    )
                    (.splitB
                      (.box 119 104)
                      (.box 119 111)
                    )
                  )
                  (.splitA
                    (.splitB
                      (.splitB
                        (.splitA
                          (.box 127 116)
                          (.box 124 116)
                        )
                        (.box 125 120)
                      )
                      (.splitA
                        (.box 128 125)
                        (.box 124 125)
                      )
                    )
                    (.splitB
                      (.box 120 118)
                      (.box 119 125)
                    )
                  )
                )
                (.splitB
                  (.box 111 106)
                  (.box 111 120)
                )
              )
            )
            (.splitB
              (.splitB
                (.box 87 76)
                (.box 92 89)
              )
              (.box 92 113)
            )
          )
          (.splitB
            (.box 161 81)
            (.box 161 113)
          )
        )
      )
    )
    (.splitB
      (.splitB
        (.box 65 97)
        (.box 129 193)
      )
      (.splitB
        (.box 129 193)
        (.box 0 97)
      )
    )
  )

theorem f1Archived16Chart1_ok : checkChart f1Archived16 1 0 2 f1Archived16Chart1 = true := by decide +kernel

def f1Archived16Chart2 : RowTree :=
  (.splitA
    (.splitB
      (.splitA
        (.box 97 129)
        (.splitB
          (.box 0 65)
          (.splitA
            (.box 161 0)
            (.box 193 193)
          )
        )
      )
      (.splitA
        (.splitB
          (.splitA
            (.box 105 161)
            (.splitB
              (.box 81 193)
              (.box 81 177)
            )
          )
          (.splitA
            (.splitB
              (.splitA
                (.box 115 92)
                (.splitB
                  (.box 102 81)
                  (.box 105 92)
                )
              )
              (.splitA
                (.splitB
                  (.splitA
                    (.box 122 111)
                    (.splitB
                      (.box 115 105)
                      (.box 117 111)
                    )
                  )
                  (.splitA
                    (.splitB
                      (.splitB
                        (.box 123 117)
                        (.box 125 120)
                      )
                      (.splitA
                        (.splitB
                          (.box 127 124)
                          (.box 127 127)
                        )
                        (.box 123 125)
                      )
                    )
                    (.splitB
                      (.splitA
                        (.splitB
                          (.box 119 116)
                          (.box 120 119)
                        )
                        (.splitB
                          (.box 116 116)
                          (.box 116 119)
                        )
                      )
                      (.splitA
                        (.box 120 125)
                        (.box 116 123)
                      )
                    )
                  )
                )
                (.splitB
                  (.splitA
                    (.splitB
                      (.box 109 104)
                      (.box 111 109)
                    )
                    (.splitB
                      (.box 103 103)
                      (.box 103 109)
                    )
                  )
                  (.splitB
                    (.splitA
                      (.box 111 117)
                      (.box 104 115)
                    )
                    (.box 109 122)
                  )
                )
              )
            )
            (.splitB
              (.splitA
                (.splitB
                  (.box 89 76)
                  (.box 92 89)
                )
                (.splitB
                  (.box 76 76)
                  (.box 76 89)
                )
              )
              (.splitB
                (.splitA
                  (.box 92 105)
                  (.box 81 102)
                )
                (.box 87 116)
              )
            )
          )
        )
        (.splitB
          (.splitA
            (.splitB
              (.box 161 193)
              (.splitA
                (.box 177 161)
                (.box 145 161)
              )
            )
            (.splitB
              (.box 193 193)
              (.box 193 161)
            )
          )
          (.splitB
            (.splitA
              (.box 177 81)
              (.box 193 81)
            )
            (.box 161 105)
          )
        )
      )
    )
    (.splitB
      (.splitA
        (.splitB
          (.box 129 97)
          (.splitA
            (.box 193 193)
            (.box 161 129)
          )
        )
        (.box 65 65)
      )
      (.splitA
        (.splitB
          (.splitA
            (.box 0 193)
            (.box 161 129)
          )
          (.box 0 75)
        )
        (.box 97 65)
      )
    )
  )

theorem f1Archived16Chart2_ok : checkChart f1Archived16 2 0 1 f1Archived16Chart2 = true := by decide +kernel

end HlawkaSchatten.BelowExponent.FacetNumeric
