/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.FacetNumeric

/-! Archived facet prism certificate data: `F0Prism6Data`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true

@[expose] public section

namespace HlawkaSchatten.BelowExponent.FacetNumeric

def f0Archived6 : Prism := {
  vertices := [⟨142400, 24800, 24800, 0⟩,
    ⟨153600, 19200, 19200, 0⟩,
    ⟨145200, 27600, 19200, 0⟩,
    ⟨142044, 24738, 24738, 480⟩,
    ⟨153216, 19152, 19152, 480⟩,
    ⟨144837, 27531, 19152, 480⟩]
  profileDen := 192000
  pi := [65305057, 234417946, 249150112, 524868709]
  slope := [402069163, -212402738, -213670834]
  radiusNum := 1
  radiusDen := 8
}

set_option maxRecDepth 40000
set_option maxHeartbeats 0

theorem f0Archived6_data_ok : dataOK f0Archived6 = true := by decide +kernel

def f0Archived6Chart0 : RowTree :=
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
                        (.box 116 125)
                      )
                      (.splitA
                        (.box 120 118)
                        (.box 116 119)
                      )
                    )
                  )
                  (.splitA
                    (.splitB
                      (.box 125 112)
                      (.box 125 104)
                    )
                    (.splitB
                      (.box 117 112)
                      (.box 117 104)
                    )
                  )
                )
                (.splitB
                  (.splitB
                    (.splitA
                      (.box 112 125)
                      (.box 105 125)
                    )
                    (.splitA
                      (.box 112 117)
                      (.box 105 117)
                    )
                  )
                  (.splitA
                    (.box 111 108)
                    (.box 103 108)
                  )
                )
              )
              (.splitA
                (.splitB
                  (.box 121 95)
                  (.box 121 79)
                )
                (.splitB
                  (.box 105 95)
                  (.box 105 79)
                )
              )
            )
            (.splitB
              (.splitB
                (.splitA
                  (.box 95 121)
                  (.box 81 118)
                )
                (.splitA
                  (.box 95 105)
                  (.box 79 105)
                )
              )
              (.splitB
                (.splitA
                  (.box 92 92)
                  (.box 79 89)
                )
                (.box 81 79)
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
              (.box 65 225)
            )
          )
        )
        (.splitB
          (.splitA
            (.splitB
              (.box 161 112)
              (.splitA
                (.box 177 81)
                (.box 145 81)
              )
            )
            (.splitB
              (.box 193 113)
              (.box 193 73)
            )
          )
          (.splitB
            (.splitA
              (.splitA
                (.splitB
                  (.box 177 177)
                  (.box 177 145)
                )
                (.splitB
                  (.box 145 177)
                  (.box 137 137)
                )
              )
              (.splitA
                (.splitB
                  (.box 225 177)
                  (.splitA
                    (.box 241 137)
                    (.box 209 137)
                  )
                )
                (.splitB
                  (.box 257 177)
                  (.box 193 137)
                )
              )
            )
            (.splitA
              (.splitB
                (.splitA
                  (.box 177 225)
                  (.splitB
                    (.box 137 233)
                    (.splitA
                      (.box 153 209)
                      (.box 129 209)
                    )
                  )
                )
                (.splitA
                  (.box 177 257)
                  (.box 137 289)
                )
              )
              (.splitA
                (.splitB
                  (.splitA
                    (.splitB
                      (.splitA
                        (.box 249 233)
                        (.box 233 233)
                      )
                      (.splitA
                        (.splitB
                          (.box 249 217)
                          (.box 249 201)
                        )
                        (.splitB
                          (.box 233 217)
                          (.box 233 201)
                        )
                      )
                    )
                    (.splitB
                      (.splitA
                        (.box 217 233)
                        (.box 201 241)
                      )
                      (.splitB
                        (.box 217 217)
                        (.box 217 201)
                      )
                    )
                  )
                  (.splitA
                    (.splitB
                      (.box 241 193)
                      (.box 241 321)
                    )
                    (.box 217 289)
                  )
                )
                (.splitB
                  (.splitB
                    (.box 289 241)
                    (.box 289 209)
                  )
                  (.box 289 289)
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
            (.splitA
              (.splitB
                (.box 225 0)
                (.box 225 161)
              )
              (.splitB
                (.box 257 0)
                (.box 257 161)
              )
            )
          )
          (.box 129 97)
        )
      )
    )
    (.splitB
      (.splitB
        (.splitA
          (.box 193 81)
          (.box 65 84)
        )
        (.splitA
          (.splitB
            (.splitA
              (.box 0 161)
              (.box 161 161)
            )
            (.splitB
              (.splitA
                (.box 0 225)
                (.box 161 225)
              )
              (.splitA
                (.box 0 257)
                (.box 161 257)
              )
            )
          )
          (.box 97 129)
        )
      )
      (.splitB
        (.splitA
          (.splitA
            (.box 0 193)
            (.box 161 129)
          )
          (.box 65 0)
        )
        (.box 65 97)
      )
    )
  )

theorem f0Archived6Chart0_ok : checkChart f0Archived6 0 1 2 f0Archived6Chart0 = true := by decide +kernel

def f0Archived6Chart1 : RowTree :=
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
                (.box 105 177)
              )
              (.splitA
                (.box 89 177)
                (.box 73 161)
              )
            )
          )
          (.splitA
            (.splitB
              (.splitA
                (.splitB
                  (.box 118 79)
                  (.splitA
                    (.box 122 95)
                    (.box 117 92)
                  )
                )
                (.splitB
                  (.box 105 79)
                  (.splitA
                    (.box 109 92)
                    (.box 103 92)
                  )
                )
              )
              (.splitA
                (.splitB
                  (.splitA
                    (.splitB
                      (.box 123 104)
                      (.splitA
                        (.box 126 112)
                        (.box 123 111)
                      )
                    )
                    (.splitB
                      (.box 117 104)
                      (.splitA
                        (.box 119 111)
                        (.box 116 111)
                      )
                    )
                  )
                  (.splitA
                    (.splitB
                      (.splitB
                        (.splitA
                          (.box 126 116)
                          (.box 123 116)
                        )
                        (.box 125 120)
                      )
                      (.splitA
                        (.splitB
                          (.box 127 123)
                          (.box 127 127)
                        )
                        (.box 124 125)
                      )
                    )
                    (.splitB
                      (.splitA
                        (.splitB
                          (.box 120 116)
                          (.box 120 119)
                        )
                        (.box 116 117)
                      )
                      (.splitA
                        (.box 120 125)
                        (.box 116 125)
                      )
                    )
                  )
                )
                (.splitB
                  (.splitA
                    (.splitB
                      (.box 111 103)
                      (.box 111 109)
                    )
                    (.box 104 105)
                  )
                  (.splitA
                    (.splitB
                      (.box 111 117)
                      (.box 112 123)
                    )
                    (.box 104 121)
                  )
                )
              )
            )
            (.splitB
              (.splitA
                (.splitB
                  (.box 92 76)
                  (.box 92 89)
                )
                (.box 79 81)
              )
              (.splitA
                (.splitB
                  (.box 92 105)
                  (.box 95 118)
                )
                (.box 79 113)
              )
            )
          )
        )
        (.splitB
          (.splitA
            (.splitB
              (.box 161 193)
              (.box 177 161)
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
            (.box 129 97)
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

theorem f0Archived6Chart1_ok : checkChart f0Archived6 1 0 2 f0Archived6Chart1 = true := by decide +kernel

def f0Archived6Chart2 : RowTree :=
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
            (.box 194 193)
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
                (.box 105 177)
              )
              (.splitA
                (.box 89 177)
                (.box 73 177)
              )
            )
          )
          (.splitA
            (.splitB
              (.splitA
                (.splitB
                  (.box 118 79)
                  (.splitA
                    (.box 123 95)
                    (.box 117 92)
                  )
                )
                (.splitB
                  (.box 105 79)
                  (.splitA
                    (.box 109 92)
                    (.box 101 92)
                  )
                )
              )
              (.splitA
                (.splitB
                  (.splitA
                    (.splitB
                      (.box 123 105)
                      (.splitA
                        (.box 126 112)
                        (.box 123 111)
                      )
                    )
                    (.splitB
                      (.box 117 104)
                      (.splitA
                        (.box 119 111)
                        (.box 115 111)
                      )
                    )
                  )
                  (.splitA
                    (.splitB
                      (.splitB
                        (.splitA
                          (.box 126 117)
                          (.box 123 116)
                        )
                        (.box 125 119)
                      )
                      (.splitA
                        (.splitB
                          (.box 127 123)
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
                        (.box 116 117)
                      )
                      (.splitA
                        (.box 120 125)
                        (.box 116 125)
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
                    (.box 104 121)
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
                (.box 79 80)
              )
              (.splitA
                (.splitB
                  (.box 92 105)
                  (.box 95 118)
                )
                (.box 79 113)
              )
            )
          )
        )
        (.splitB
          (.splitA
            (.splitB
              (.splitB
                (.box 161 257)
                (.box 161 225)
              )
              (.box 176 161)
            )
            (.splitB
              (.box 225 257)
              (.box 193 161)
            )
          )
          (.splitA
            (.splitB
              (.box 177 81)
              (.box 161 106)
            )
            (.box 129 97)
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
        (.box 75 65)
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

theorem f0Archived6Chart2_ok : checkChart f0Archived6 2 0 1 f0Archived6Chart2 = true := by decide +kernel

end HlawkaSchatten.BelowExponent.FacetNumeric
