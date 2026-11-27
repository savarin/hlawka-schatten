/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.FacetNumeric

/-! Archived facet prism certificate data: `F0Prism3Data`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true

@[expose] public section

namespace HlawkaSchatten.BelowExponent.FacetNumeric

def f0Archived3 : Prism := {
  vertices := [⟨27200, 10400, 10400, 0⟩,
    ⟨30000, 13200, 4800, 0⟩,
    ⟨24400, 16000, 7600, 0⟩,
    ⟨27132, 10374, 10374, 120⟩,
    ⟨29925, 13167, 4788, 120⟩,
    ⟨24339, 15960, 7581, 120⟩]
  profileDen := 48000
  pi := [124062579, 220925272, 209721650, 519032323]
  slope := [225189494, -56770798, -204095881]
  radiusNum := 1
  radiusDen := 8
}

set_option maxRecDepth 40000
set_option maxHeartbeats 0

theorem f0Archived3_data_ok : dataOK f0Archived3 = true := by decide +kernel

def f0Archived3Chart0 : RowTree :=
  (.splitA
    (.splitB
      (.splitB
        (.splitA
          (.splitB
            (.splitA
              (.splitB
                (.splitA
                  (.splitB
                    (.splitA
                      (.splitB
                        (.box 125 127)
                        (.box 125 124)
                      )
                      (.splitA
                        (.box 121 125)
                        (.box 117 125)
                      )
                    )
                    (.splitA
                      (.splitB
                        (.box 125 120)
                        (.box 125 116)
                      )
                      (.box 119 118)
                    )
                  )
                  (.splitB
                    (.box 111 125)
                    (.box 111 117)
                  )
                )
                (.splitA
                  (.splitA
                    (.splitB
                      (.box 125 112)
                      (.box 123 105)
                    )
                    (.splitB
                      (.box 119 111)
                      (.box 119 104)
                    )
                  )
                  (.splitB
                    (.box 111 109)
                    (.box 108 104)
                  )
                )
              )
              (.splitB
                (.box 92 121)
                (.box 92 105)
              )
            )
            (.splitA
              (.splitA
                (.splitB
                  (.box 121 92)
                  (.box 118 81)
                )
                (.splitB
                  (.box 108 92)
                  (.box 108 79)
                )
              )
              (.splitB
                (.box 87 92)
                (.box 87 76)
              )
            )
          )
          (.splitB
            (.box 161 113)
            (.splitA
              (.box 161 81)
              (.box 193 81)
            )
          )
        )
        (.splitA
          (.splitB
            (.splitA
              (.box 113 161)
              (.box 81 162)
            )
            (.splitA
              (.box 113 193)
              (.box 81 193)
            )
          )
          (.splitB
            (.splitA
              (.splitA
                (.box 177 161)
                (.box 145 161)
              )
              (.box 193 130)
            )
            (.splitA
              (.splitB
                (.splitA
                  (.box 177 225)
                  (.box 137 209)
                )
                (.splitA
                  (.box 177 257)
                  (.splitB
                    (.splitB
                      (.box 137 305)
                      (.box 137 273)
                    )
                    (.box 137 257)
                  )
                )
              )
              (.splitB
                (.splitA
                  (.splitA
                    (.box 241 193)
                    (.box 209 193)
                  )
                  (.box 257 193)
                )
                (.splitA
                  (.splitB
                    (.splitA
                      (.splitB
                        (.box 241 305)
                        (.box 241 273)
                      )
                      (.box 225 273)
                    )
                    (.splitA
                      (.box 241 353)
                      (.box 225 353)
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
          (.box 81 193)
          (.box 84 65)
        )
        (.splitB
          (.splitA
            (.splitB
              (.box 145 0)
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
        (.box 129 97)
        (.splitA
          (.splitA
            (.splitB
              (.box 193 161)
              (.box 0 193)
            )
            (.box 161 129)
          )
          (.box 97 129)
        )
      )
      (.splitA
        (.splitB
          (.box 0 193)
          (.box 129 97)
        )
        (.box 97 65)
      )
    )
  )

theorem f0Archived3Chart0_ok : checkChart f0Archived3 0 1 2 f0Archived3Chart0 = true := by decide +kernel

def f0Archived3Chart1 : RowTree :=
  (.splitA
    (.splitB
      (.splitA
        (.splitB
          (.box 84 65)
          (.box 81 193)
        )
        (.splitA
          (.splitB
            (.box 161 97)
            (.splitB
              (.box 161 161)
              (.box 145 0)
            )
          )
          (.splitB
            (.box 193 97)
            (.splitA
              (.splitB
                (.box 225 161)
                (.box 225 257)
              )
              (.splitB
                (.box 257 161)
                (.box 257 257)
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
              (.box 81 193)
            )
            (.splitA
              (.box 113 177)
              (.box 81 177)
            )
          )
          (.splitA
            (.splitB
              (.splitA
                (.splitB
                  (.box 118 81)
                  (.box 121 92)
                )
                (.splitB
                  (.box 105 79)
                  (.box 108 92)
                )
              )
              (.splitA
                (.splitB
                  (.splitA
                    (.splitB
                      (.box 125 104)
                      (.box 125 112)
                    )
                    (.splitB
                      (.box 117 104)
                      (.box 119 111)
                    )
                  )
                  (.splitA
                    (.splitB
                      (.splitB
                        (.box 125 116)
                        (.box 125 120)
                      )
                      (.splitA
                        (.box 128 125)
                        (.box 124 125)
                      )
                    )
                    (.splitB
                      (.splitB
                        (.box 119 116)
                        (.box 119 120)
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
                    (.box 108 111)
                  )
                  (.splitB
                    (.box 108 117)
                    (.box 111 123)
                  )
                )
              )
            )
            (.splitB
              (.splitB
                (.box 87 76)
                (.box 87 92)
              )
              (.splitB
                (.box 87 105)
                (.box 92 118)
              )
            )
          )
        )
        (.splitB
          (.splitB
            (.splitA
              (.splitB
                (.box 161 321)
                (.box 161 225)
              )
              (.splitA
                (.box 225 257)
                (.box 257 257)
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
      (.splitA
        (.splitB
          (.box 129 97)
          (.box 0 193)
        )
        (.box 97 65)
      )
      (.splitB
        (.splitA
          (.box 0 193)
          (.box 65 0)
        )
        (.box 129 97)
      )
    )
  )

theorem f0Archived3Chart1_ok : checkChart f0Archived3 1 0 2 f0Archived3Chart1 = true := by decide +kernel

def f0Archived3Chart2 : RowTree :=
  (.splitA
    (.splitB
      (.splitA
        (.box 97 129)
        (.splitA
          (.box 161 129)
          (.box 193 129)
        )
      )
      (.splitA
        (.splitB
          (.splitA
            (.box 113 161)
            (.splitB
              (.box 81 193)
              (.box 81 177)
            )
          )
          (.splitA
            (.splitB
              (.splitA
                (.box 118 92)
                (.splitB
                  (.box 102 81)
                  (.box 105 95)
                )
              )
              (.splitA
                (.splitB
                  (.splitA
                    (.box 123 109)
                    (.splitB
                      (.box 117 105)
                      (.box 117 112)
                    )
                  )
                  (.splitA
                    (.splitB
                      (.splitB
                        (.box 125 117)
                        (.box 125 120)
                      )
                      (.splitA
                        (.box 128 125)
                        (.box 124 125)
                      )
                    )
                    (.splitB
                      (.splitA
                        (.splitB
                          (.box 119 117)
                          (.box 120 120)
                        )
                        (.box 117 117)
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
                      (.box 111 111)
                    )
                    (.box 105 105)
                  )
                  (.splitB
                    (.splitA
                      (.box 111 117)
                      (.box 105 115)
                    )
                    (.box 108 123)
                  )
                )
              )
            )
            (.splitB
              (.splitA
                (.splitB
                  (.box 89 79)
                  (.box 92 92)
                )
                (.box 79 81)
              )
              (.splitB
                (.splitA
                  (.box 92 105)
                  (.box 81 102)
                )
                (.box 87 118)
              )
            )
          )
        )
        (.splitB
          (.splitB
            (.splitA
              (.box 161 193)
              (.box 193 193)
            )
            (.splitA
              (.box 161 177)
              (.box 193 161)
            )
          )
          (.splitB
            (.splitA
              (.box 161 80)
              (.box 193 81)
            )
            (.box 161 113)
          )
        )
      )
    )
    (.splitB
      (.splitA
        (.splitB
          (.box 129 97)
          (.box 193 129)
        )
        (.box 97 65)
      )
      (.splitA
        (.splitB
          (.box 193 129)
          (.box 0 75)
        )
        (.box 97 65)
      )
    )
  )

theorem f0Archived3Chart2_ok : checkChart f0Archived3 2 0 1 f0Archived3Chart2 = true := by decide +kernel

end HlawkaSchatten.BelowExponent.FacetNumeric
