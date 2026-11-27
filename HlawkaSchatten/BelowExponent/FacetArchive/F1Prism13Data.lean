/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.FacetNumeric

/-! Archived facet prism certificate data: `F1Prism13Data`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true

@[expose] public section

namespace HlawkaSchatten.BelowExponent.FacetNumeric

def f1Archived13 : Prism := {
  vertices := [⟨75600, 42000, 10400, 0⟩,
    ⟨69600, 47200, 11200, 0⟩,
    ⟨76400, 42800, 8800, 0⟩,
    ⟨75411, 41895, 10374, 320⟩,
    ⟨69426, 47082, 11172, 320⟩,
    ⟨76209, 42693, 8778, 320⟩]
  profileDen := 128000
  pi := [130384595, 208349470, 211962839, 523044920]
  slope := [217950560, 51076421, -296678970]
  radiusNum := 1
  radiusDen := 8
}

set_option maxRecDepth 40000
set_option maxHeartbeats 0

theorem f1Archived13_data_ok : dataOK f1Archived13 = true := by decide +kernel

def f1Archived13Chart0 : RowTree :=
  (.splitA
    (.splitB
      (.splitB
        (.splitA
          (.splitA
            (.splitB
              (.splitB
                (.splitA
                  (.splitB
                    (.splitA
                      (.splitB
                        (.box 126 127)
                        (.box 125 124)
                      )
                      (.box 120 125)
                    )
                    (.splitA
                      (.splitB
                        (.box 125 120)
                        (.box 125 116)
                      )
                      (.box 120 117)
                    )
                  )
                  (.box 111 121)
                )
                (.splitA
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
                  (.box 111 105)
                )
              )
              (.splitB
                (.splitA
                  (.box 121 92)
                  (.box 108 92)
                )
                (.box 113 79)
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
            (.box 65 97)
            (.box 161 81)
          )
        )
        (.splitA
          (.splitB
            (.splitA
              (.box 113 176)
              (.splitA
                (.box 89 161)
                (.box 73 161)
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
                  (.splitB
                    (.box 177 273)
                    (.box 161 321)
                  )
                  (.splitB
                    (.splitA
                      (.box 153 273)
                      (.box 137 273)
                    )
                    (.splitA
                      (.splitA
                        (.box 157 321)
                        (.splitB
                          (.box 149 353)
                          (.box 149 385)
                        )
                      )
                      (.splitB
                        (.box 137 353)
                        (.box 137 321)
                      )
                    )
                  )
                )
              )
              (.splitB
                (.box 225 193)
                (.splitA
                  (.splitB
                    (.box 241 273)
                    (.splitB
                      (.box 242 353)
                      (.box 241 321)
                    )
                  )
                  (.box 257 257)
                )
              )
            )
          )
        )
      )
      (.splitA
        (.splitB
          (.splitA
            (.box 113 193)
            (.splitB
              (.box 65 0)
              (.box 81 161)
            )
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
        (.box 0 75)
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
        (.box 0 65)
      )
    )
  )

theorem f1Archived13Chart0_ok : checkChart f1Archived13 0 1 2 f1Archived13Chart0 = true := by decide +kernel

def f1Archived13Chart1 : RowTree :=
  (.splitA
    (.splitB
      (.splitA
        (.splitB
          (.box 97 65)
          (.splitA
            (.box 113 193)
            (.splitB
              (.box 81 161)
              (.box 70 0)
            )
          )
        )
        (.splitB
          (.box 129 97)
          (.splitA
            (.splitB
              (.box 161 161)
              (.splitA
                (.splitB
                  (.box 177 225)
                  (.box 177 0)
                )
                (.splitB
                  (.box 145 225)
                  (.splitA
                    (.splitB
                      (.box 153 289)
                      (.box 153 0)
                    )
                    (.splitB
                      (.box 137 289)
                      (.splitA
                        (.box 141 0)
                        (.box 133 0)
                      )
                    )
                  )
                )
              )
            )
            (.splitB
              (.box 193 161)
              (.splitA
                (.splitB
                  (.box 225 225)
                  (.splitA
                    (.splitB
                      (.box 241 289)
                      (.box 249 0)
                    )
                    (.box 225 321)
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
          (.splitB
            (.splitA
              (.box 113 193)
              (.splitB
                (.box 81 257)
                (.box 81 225)
              )
            )
            (.splitA
              (.box 112 176)
              (.box 88 161)
            )
          )
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
                      (.box 119 103)
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
                        (.box 127 125)
                        (.box 124 125)
                      )
                    )
                    (.splitB
                      (.splitB
                        (.box 119 116)
                        (.box 120 119)
                      )
                      (.splitA
                        (.box 121 125)
                        (.box 117 125)
                      )
                    )
                  )
                )
                (.splitB
                  (.splitB
                    (.box 108 103)
                    (.box 111 109)
                  )
                  (.splitB
                    (.box 111 117)
                    (.box 111 125)
                  )
                )
              )
            )
            (.splitB
              (.splitB
                (.box 87 76)
                (.box 92 89)
              )
              (.splitB
                (.box 92 105)
                (.box 92 121)
              )
            )
          )
        )
        (.splitB
          (.splitB
            (.splitA
              (.splitB
                (.splitA
                  (.box 177 321)
                  (.splitA
                    (.splitB
                      (.box 153 385)
                      (.box 153 289)
                    )
                    (.splitB
                      (.splitA
                        (.splitB
                          (.box 141 449)
                          (.box 141 353)
                        )
                        (.splitB
                          (.box 133 449)
                          (.box 133 353)
                        )
                      )
                      (.box 137 289)
                    )
                  )
                )
                (.box 161 225)
              )
              (.splitA
                (.splitB
                  (.splitA
                    (.splitB
                      (.splitA
                        (.splitB
                          (.box 249 449)
                          (.box 249 353)
                        )
                        (.box 233 385)
                      )
                      (.box 241 289)
                    )
                    (.box 225 321)
                  )
                  (.box 225 225)
                )
                (.box 193 257)
              )
            )
            (.splitA
              (.box 161 161)
              (.box 193 161)
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
        (.box 65 65)
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
        (.box 0 97)
      )
    )
  )

theorem f1Archived13Chart1_ok : checkChart f1Archived13 1 0 2 f1Archived13Chart1 = true := by decide +kernel

def f1Archived13Chart2 : RowTree :=
  (.splitA
    (.splitB
      (.splitA
        (.box 97 129)
        (.splitB
          (.box 0 65)
          (.splitA
            (.box 161 129)
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
                    (.box 122 110)
                    (.splitB
                      (.box 115 105)
                      (.box 117 111)
                    )
                  )
                  (.splitA
                    (.splitB
                      (.splitB
                        (.box 124 117)
                        (.box 125 120)
                      )
                      (.splitA
                        (.box 127 125)
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
                        (.box 121 123)
                        (.box 117 123)
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
                      (.box 105 115)
                    )
                    (.box 108 122)
                  )
                )
              )
            )
            (.splitB
              (.splitA
                (.splitB
                  (.box 89 79)
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
                  (.box 81 99)
                )
                (.box 87 115)
              )
            )
          )
        )
        (.splitB
          (.splitA
            (.splitB
              (.box 161 193)
              (.box 161 176)
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
            (.box 161 97)
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

theorem f1Archived13Chart2_ok : checkChart f1Archived13 2 0 1 f1Archived13Chart2 = true := by decide +kernel

end HlawkaSchatten.BelowExponent.FacetNumeric
