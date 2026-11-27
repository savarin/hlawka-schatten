/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.FacetNumeric

/-! Archived facet prism certificate data: `F0Prism4Data`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true

@[expose] public section

namespace HlawkaSchatten.BelowExponent.FacetNumeric

def f0Archived4 : Prism := {
  vertices := [⟨65600, 15200, 15200, 0⟩,
    ⟨68400, 18000, 9600, 0⟩,
    ⟨60000, 26400, 9600, 0⟩,
    ⟨65436, 15162, 15162, 240⟩,
    ⟨68229, 17955, 9576, 240⟩,
    ⟨59850, 26334, 9576, 240⟩]
  profileDen := 96000
  pi := [92833280, 201918687, 255675879, 523313978]
  slope := [282308118, -128725625, -180696364]
  radiusNum := 1
  radiusDen := 8
}

set_option maxRecDepth 40000
set_option maxHeartbeats 0

theorem f0Archived4_data_ok : dataOK f0Archived4 = true := by decide +kernel

def f0Archived4Chart0 : RowTree :=
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
                        (.box 121 125)
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
                    (.box 111 123)
                    (.box 108 117)
                  )
                  (.splitB
                    (.box 108 111)
                    (.box 108 104)
                  )
                )
              )
              (.splitA
                (.splitB
                  (.box 121 92)
                  (.box 118 81)
                )
                (.splitB
                  (.box 108 92)
                  (.box 105 79)
                )
              )
            )
            (.splitB
              (.splitB
                (.box 92 118)
                (.box 87 105)
              )
              (.splitB
                (.box 87 92)
                (.box 87 73)
              )
            )
          )
          (.splitB
            (.splitA
              (.box 113 177)
              (.splitA
                (.box 89 161)
                (.box 73 161)
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
            (.box 193 97)
          )
          (.splitB
            (.splitA
              (.splitA
                (.box 177 161)
                (.box 145 145)
              )
              (.box 225 129)
            )
            (.splitA
              (.splitB
                (.splitA
                  (.box 177 209)
                  (.splitA
                    (.box 153 209)
                    (.splitB
                      (.box 137 241)
                      (.box 137 193)
                    )
                  )
                )
                (.splitA
                  (.box 161 257)
                  (.splitB
                    (.splitA
                      (.box 153 289)
                      (.splitB
                        (.splitA
                          (.box 141 305)
                          (.box 133 305)
                        )
                        (.splitA
                          (.box 141 273)
                          (.box 133 273)
                        )
                      )
                    )
                    (.splitA
                      (.box 153 257)
                      (.box 137 257)
                    )
                  )
                )
              )
              (.splitB
                (.splitA
                  (.splitA
                    (.box 249 209)
                    (.box 209 193)
                  )
                  (.box 257 225)
                )
                (.splitA
                  (.splitB
                    (.splitA
                      (.splitB
                        (.box 249 305)
                        (.box 249 273)
                      )
                      (.box 209 289)
                    )
                    (.splitA
                      (.box 241 257)
                      (.box 209 321)
                    )
                  )
                  (.box 193 257)
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
            (.box 65 193)
          )
          (.box 84 65)
        )
        (.splitB
          (.splitA
            (.splitB
              (.box 146 0)
              (.box 161 161)
            )
            (.splitB
              (.box 225 0)
              (.box 193 161)
            )
          )
          (.box 129 97)
        )
      )
    )
    (.splitB
      (.splitB
        (.box 129 97)
        (.splitA
          (.splitA
            (.splitB
              (.box 193 161)
              (.box 193 193)
            )
            (.box 161 129)
          )
          (.box 65 0)
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

theorem f0Archived4Chart0_ok : checkChart f0Archived4 0 1 2 f0Archived4Chart0 = true := by decide +kernel

def f0Archived4Chart1 : RowTree :=
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
              (.box 113 177)
              (.box 82 177)
            )
          )
          (.splitA
            (.splitB
              (.splitA
                (.splitB
                  (.box 118 79)
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
                      (.box 123 105)
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
                          (.box 126 117)
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
                        (.box 119 120)
                      )
                      (.splitA
                        (.box 120 125)
                        (.box 117 125)
                      )
                    )
                  )
                )
                (.splitB
                  (.splitB
                    (.box 108 103)
                    (.box 108 111)
                  )
                  (.splitB
                    (.box 108 117)
                    (.box 108 125)
                  )
                )
              )
            )
            (.splitB
              (.splitB
                (.box 87 73)
                (.box 87 92)
              )
              (.splitB
                (.box 87 105)
                (.box 87 121)
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
            (.box 161 81)
            (.box 161 113)
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
          (.box 0 193)
          (.box 97 129)
        )
        (.box 129 97)
      )
    )
  )

theorem f0Archived4Chart1_ok : checkChart f0Archived4 1 0 2 f0Archived4Chart1 = true := by decide +kernel

def f0Archived4Chart2 : RowTree :=
  (.splitA
    (.splitB
      (.splitA
        (.box 81 129)
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
              (.box 80 176)
            )
          )
          (.splitA
            (.splitB
              (.splitA
                (.splitB
                  (.box 115 81)
                  (.box 118 95)
                )
                (.splitB
                  (.box 102 81)
                  (.box 105 92)
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
                      (.box 115 105)
                      (.box 117 111)
                    )
                  )
                  (.splitA
                    (.splitB
                      (.splitB
                        (.splitA
                          (.box 126 117)
                          (.box 122 117)
                        )
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
                          (.box 116 117)
                          (.box 116 118)
                        )
                      )
                      (.splitA
                        (.box 120 125)
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
                    (.box 104 105)
                  )
                  (.splitB
                    (.splitA
                      (.box 111 117)
                      (.box 104 115)
                    )
                    (.splitA
                      (.box 112 123)
                      (.box 105 122)
                    )
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
                  (.box 79 102)
                )
                (.splitA
                  (.box 95 118)
                  (.box 81 113)
                )
              )
            )
          )
        )
        (.splitB
          (.splitA
            (.splitB
              (.box 161 193)
              (.box 176 160)
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
            (.splitA
              (.box 161 105)
              (.box 193 113)
            )
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

theorem f0Archived4Chart2_ok : checkChart f0Archived4 2 0 1 f0Archived4Chart2 = true := by decide +kernel

end HlawkaSchatten.BelowExponent.FacetNumeric
