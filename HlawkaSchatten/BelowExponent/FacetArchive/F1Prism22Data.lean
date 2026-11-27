/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.FacetNumeric

/-! Archived facet prism certificate data: `F1Prism22Data`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true

@[expose] public section

namespace HlawkaSchatten.BelowExponent.FacetNumeric

def f1Archived22 : Prism := {
  vertices := [⟨96800, 18400, 12800, 0⟩,
    ⟨91200, 24000, 12800, 0⟩,
    ⟨97200, 18800, 12000, 0⟩,
    ⟨96558, 18354, 12768, 320⟩,
    ⟨90972, 23940, 12768, 320⟩,
    ⟨96957, 18753, 11970, 320⟩]
  profileDen := 128000
  pi := [78459081, 229013949, 242732411, 523536383]
  slope := [373214411, -164554086, -235329388]
  radiusNum := 1
  radiusDen := 8
}

set_option maxRecDepth 40000
set_option maxHeartbeats 0

theorem f1Archived22_data_ok : dataOK f1Archived22 = true := by decide +kernel

def f1Archived22Chart0 : RowTree :=
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
                        (.box 127 125)
                        (.box 124 125)
                      )
                      (.splitB
                        (.box 125 120)
                        (.box 125 116)
                      )
                    )
                    (.splitB
                      (.splitA
                        (.box 120 125)
                        (.box 117 125)
                      )
                      (.splitB
                        (.box 119 120)
                        (.box 119 116)
                      )
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
                  (.splitB
                    (.box 108 125)
                    (.box 108 117)
                  )
                  (.splitB
                    (.box 108 111)
                    (.box 108 103)
                  )
                )
              )
              (.splitA
                (.splitB
                  (.box 121 92)
                  (.box 121 79)
                )
                (.splitB
                  (.box 108 92)
                  (.box 105 79)
                )
              )
            )
            (.splitB
              (.splitB
                (.box 87 121)
                (.box 87 105)
              )
              (.splitB
                (.box 87 89)
                (.box 87 73)
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
              (.box 73 193)
            )
          )
        )
        (.splitB
          (.splitA
            (.splitB
              (.box 161 113)
              (.box 161 81)
            )
            (.splitB
              (.box 193 113)
              (.box 193 81)
            )
          )
          (.splitB
            (.splitA
              (.splitA
                (.box 185 146)
                (.box 145 144)
              )
              (.splitA
                (.box 241 144)
                (.box 257 145)
              )
            )
            (.splitA
              (.splitB
                (.splitA
                  (.box 177 225)
                  (.splitB
                    (.box 137 225)
                    (.splitA
                      (.box 153 209)
                      (.splitB
                        (.box 137 217)
                        (.box 133 201)
                      )
                    )
                  )
                )
                (.splitA
                  (.box 177 289)
                  (.splitB
                    (.splitA
                      (.box 153 289)
                      (.box 133 305)
                    )
                    (.box 145 257)
                  )
                )
              )
              (.splitB
                (.splitA
                  (.splitA
                    (.splitB
                      (.box 241 241)
                      (.splitA
                        (.splitB
                          (.box 249 217)
                          (.box 249 201)
                        )
                        (.box 237 202)
                      )
                    )
                    (.splitB
                      (.box 209 241)
                      (.box 225 209)
                    )
                  )
                  (.box 193 225)
                )
                (.splitA
                  (.splitA
                    (.splitB
                      (.splitA
                        (.box 249 305)
                        (.box 233 305)
                      )
                      (.box 241 321)
                    )
                    (.splitB
                      (.box 209 305)
                      (.box 209 321)
                    )
                  )
                  (.box 193 289)
                )
              )
            )
          )
        )
      )
      (.splitA
        (.splitB
          (.box 81 193)
          (.box 84 65)
        )
        (.splitB
          (.splitA
            (.splitB
              (.box 161 0)
              (.box 161 161)
            )
            (.splitB
              (.box 224 0)
              (.box 193 161)
            )
          )
          (.box 129 97)
        )
      )
    )
    (.splitB
      (.splitB
        (.splitA
          (.box 0 65)
          (.box 97 97)
        )
        (.splitB
          (.splitA
            (.box 0 145)
            (.box 97 161)
          )
          (.splitA
            (.splitA
              (.box 0 193)
              (.box 161 193)
            )
            (.box 97 193)
          )
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

theorem f1Archived22Chart0_ok : checkChart f1Archived22 0 1 2 f1Archived22Chart0 = true := by decide +kernel

def f1Archived22Chart1 : RowTree :=
  (.splitA
    (.splitB
      (.splitA
        (.splitB
          (.box 84 65)
          (.splitA
            (.box 113 129)
            (.box 81 193)
          )
        )
        (.splitB
          (.box 129 97)
          (.splitA
            (.box 161 193)
            (.box 193 193)
          )
        )
      )
      (.splitA
        (.splitB
          (.splitB
            (.splitA
              (.box 113 193)
              (.box 81 193)
            )
            (.splitA
              (.splitA
                (.box 121 161)
                (.box 105 161)
              )
              (.splitA
                (.box 89 161)
                (.box 73 161)
              )
            )
          )
          (.splitA
            (.splitB
              (.splitA
                (.splitB
                  (.box 118 81)
                  (.box 121 93)
                )
                (.splitB
                  (.box 105 79)
                  (.splitA
                    (.box 111 92)
                    (.box 103 92)
                  )
                )
              )
              (.splitA
                (.splitB
                  (.splitA
                    (.splitB
                      (.box 123 105)
                      (.box 125 111)
                    )
                    (.splitB
                      (.box 117 104)
                      (.box 118 111)
                    )
                  )
                  (.splitA
                    (.splitB
                      (.splitB
                        (.splitA
                          (.box 126 117)
                          (.box 123 116)
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
                        (.box 118 116)
                        (.splitA
                          (.box 120 120)
                          (.box 116 119)
                        )
                      )
                      (.splitA
                        (.box 120 125)
                        (.box 116 125)
                      )
                    )
                  )
                )
                (.splitB
                  (.splitB
                    (.splitA
                      (.box 111 103)
                      (.box 104 103)
                    )
                    (.splitA
                      (.box 111 111)
                      (.box 104 109)
                    )
                  )
                  (.splitB
                    (.splitA
                      (.box 109 117)
                      (.box 108 117)
                    )
                    (.box 108 124)
                  )
                )
              )
            )
            (.splitB
              (.splitB
                (.splitA
                  (.box 92 76)
                  (.box 79 76)
                )
                (.splitA
                  (.box 92 92)
                  (.box 79 89)
                )
              )
              (.splitB
                (.splitA
                  (.box 95 105)
                  (.box 81 105)
                )
                (.box 87 119)
              )
            )
          )
        )
        (.splitB
          (.splitA
            (.splitB
              (.box 161 193)
              (.box 161 161)
            )
            (.splitB
              (.box 193 193)
              (.box 193 161)
            )
          )
          (.splitB
            (.splitA
              (.box 161 81)
              (.box 193 81)
            )
            (.splitA
              (.box 161 113)
              (.box 193 113)
            )
          )
        )
      )
    )
    (.splitB
      (.splitA
        (.box 193 129)
        (.box 97 65)
      )
      (.splitB
        (.splitA
          (.box 193 129)
          (.box 65 0)
        )
        (.box 129 97)
      )
    )
  )

theorem f1Archived22Chart1_ok : checkChart f1Archived22 1 0 2 f1Archived22Chart1 = true := by decide +kernel

def f1Archived22Chart2 : RowTree :=
  (.splitA
    (.splitB
      (.splitA
        (.splitB
          (.box 97 97)
          (.box 97 193)
        )
        (.splitB
          (.box 129 97)
          (.splitA
            (.box 161 193)
            (.box 193 193)
          )
        )
      )
      (.splitA
        (.splitB
          (.splitA
            (.splitB
              (.box 113 193)
              (.box 113 177)
            )
            (.splitB
              (.box 81 193)
              (.splitA
                (.box 89 161)
                (.box 73 161)
              )
            )
          )
          (.splitA
            (.splitB
              (.splitA
                (.splitB
                  (.box 118 81)
                  (.box 118 95)
                )
                (.splitB
                  (.box 105 79)
                  (.splitA
                    (.box 107 95)
                    (.box 103 92)
                  )
                )
              )
              (.splitA
                (.splitB
                  (.splitA
                    (.splitB
                      (.box 123 105)
                      (.box 123 112)
                    )
                    (.splitB
                      (.box 117 104)
                      (.box 117 111)
                    )
                  )
                  (.splitA
                    (.splitB
                      (.splitB
                        (.splitA
                          (.box 126 117)
                          (.box 123 116)
                        )
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
                        (.box 116 117)
                      )
                      (.splitA
                        (.box 120 125)
                        (.box 117 124)
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
                    (.box 104 105)
                  )
                  (.splitA
                    (.splitB
                      (.box 111 117)
                      (.box 112 123)
                    )
                    (.box 105 118)
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
                (.box 78 81)
              )
              (.splitA
                (.splitB
                  (.box 92 105)
                  (.box 95 118)
                )
                (.box 81 107)
              )
            )
          )
        )
        (.splitB
          (.splitA
            (.splitB
              (.box 161 193)
              (.box 176 161)
            )
            (.splitB
              (.box 193 193)
              (.box 193 161)
            )
          )
          (.splitA
            (.splitB
              (.box 177 81)
              (.box 161 105)
            )
            (.box 193 81)
          )
        )
      )
    )
    (.splitB
      (.splitA
        (.splitB
          (.box 129 97)
          (.box 193 193)
        )
        (.box 97 65)
      )
      (.splitB
        (.splitA
          (.splitA
            (.box 0 193)
            (.box 161 129)
          )
          (.box 75 0)
        )
        (.box 129 97)
      )
    )
  )

theorem f1Archived22Chart2_ok : checkChart f1Archived22 2 0 1 f1Archived22Chart2 = true := by decide +kernel

end HlawkaSchatten.BelowExponent.FacetNumeric
