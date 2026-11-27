/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.FacetNumeric

/-! Archived facet prism certificate data: `F0Prism10Data`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true

@[expose] public section

namespace HlawkaSchatten.BelowExponent.FacetNumeric

def f0Archived10 : Prism := {
  vertices := [⟨16000, 16000, 16000, 0⟩,
    ⟨27200, 10400, 10400, 0⟩,
    ⟨24400, 16000, 7600, 0⟩,
    ⟨15960, 15960, 15960, 120⟩,
    ⟨27132, 10374, 10374, 120⟩,
    ⟨24339, 15960, 7581, 120⟩]
  profileDen := 48000
  pi := [143667942, 193335422, 218970954, 517767506]
  slope := [105607723, -72854106, -70960433]
  radiusNum := 1
  radiusDen := 4
}

set_option maxRecDepth 40000
set_option maxHeartbeats 0

theorem f0Archived10_data_ok : dataOK f0Archived10 = true := by decide +kernel

def f0Archived10Chart0 : RowTree :=
  (.splitA
    (.splitB
      (.splitB
        (.splitA
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
                      (.box 125 119)
                    )
                    (.splitB
                      (.box 119 125)
                      (.box 119 119)
                    )
                  )
                  (.splitA
                    (.box 125 108)
                    (.box 119 108)
                  )
                )
                (.splitB
                  (.splitA
                    (.box 112 121)
                    (.box 105 121)
                  )
                  (.box 108 108)
                )
              )
              (.splitA
                (.box 121 87)
                (.box 108 87)
              )
            )
            (.splitB
              (.splitB
                (.box 92 118)
                (.box 87 105)
              )
              (.splitA
                (.box 92 87)
                (.box 76 87)
              )
            )
          )
          (.splitA
            (.splitB
              (.box 65 107)
              (.box 161 81)
            )
            (.box 193 97)
          )
        )
        (.splitA
          (.splitB
            (.splitA
              (.box 113 161)
              (.box 81 161)
            )
            (.box 97 193)
          )
          (.splitA
            (.splitB
              (.box 161 161)
              (.box 145 193)
            )
            (.splitB
              (.box 193 145)
              (.splitB
                (.splitA
                  (.box 225 225)
                  (.box 257 225)
                )
                (.splitA
                  (.box 225 257)
                  (.box 257 289)
                )
              )
            )
          )
        )
      )
      (.splitA
        (.box 81 129)
        (.splitA
          (.splitB
            (.box 161 0)
            (.box 161 97)
          )
          (.splitB
            (.box 193 0)
            (.box 193 97)
          )
        )
      )
    )
    (.splitB
      (.splitB
        (.box 129 65)
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
          (.box 0 0)
          (.box 129 97)
        )
        (.box 97 65)
      )
    )
  )

theorem f0Archived10Chart0_ok : checkChart f0Archived10 0 1 2 f0Archived10Chart0 = true := by decide +kernel

def f0Archived10Chart1 : RowTree :=
  (.splitA
    (.splitB
      (.splitA
        (.box 81 129)
        (.splitA
          (.splitB
            (.box 161 97)
            (.box 161 0)
          )
          (.splitB
            (.box 193 97)
            (.box 193 0)
          )
        )
      )
      (.splitA
        (.splitB
          (.splitB
            (.box 97 193)
            (.splitA
              (.box 113 161)
              (.box 81 161)
            )
          )
          (.splitA
            (.splitB
              (.splitA
                (.box 121 87)
                (.box 108 87)
              )
              (.splitA
                (.splitB
                  (.splitA
                    (.box 125 108)
                    (.box 119 108)
                  )
                  (.splitA
                    (.splitB
                      (.box 125 119)
                      (.splitA
                        (.box 127 125)
                        (.box 124 125)
                      )
                    )
                    (.splitB
                      (.box 119 119)
                      (.box 119 125)
                    )
                  )
                )
                (.splitB
                  (.box 108 108)
                  (.splitA
                    (.box 112 121)
                    (.box 105 121)
                  )
                )
              )
            )
            (.splitB
              (.box 87 87)
              (.splitB
                (.box 92 102)
                (.box 92 118)
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
        (.box 0 129)
        (.box 97 65)
      )
      (.splitB
        (.splitA
          (.box 0 129)
          (.box 97 129)
        )
        (.box 0 97)
      )
    )
  )

theorem f0Archived10Chart1_ok : checkChart f0Archived10 1 0 2 f0Archived10Chart1 = true := by decide +kernel

def f0Archived10Chart2 : RowTree :=
  (.splitA
    (.splitB
      (.splitA
        (.box 97 129)
        (.splitB
          (.box 129 97)
          (.splitA
            (.box 161 0)
            (.box 193 193)
          )
        )
      )
      (.splitA
        (.splitB
          (.splitA
            (.box 113 161)
            (.splitB
              (.box 81 193)
              (.box 81 161)
            )
          )
          (.splitA
            (.splitB
              (.splitA
                (.box 118 92)
                (.box 105 88)
              )
              (.splitA
                (.splitB
                  (.splitB
                    (.box 118 105)
                    (.box 121 112)
                  )
                  (.splitA
                    (.splitB
                      (.box 125 119)
                      (.splitA
                        (.box 127 125)
                        (.box 124 125)
                      )
                    )
                    (.splitB
                      (.box 119 117)
                      (.box 119 125)
                    )
                  )
                )
                (.splitB
                  (.splitB
                    (.box 108 103)
                    (.box 108 111)
                  )
                  (.splitA
                    (.box 112 121)
                    (.box 105 118)
                  )
                )
              )
            )
            (.splitB
              (.splitA
                (.box 89 87)
                (.box 81 81)
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
              (.box 161 193)
              (.box 193 193)
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
          (.box 193 193)
        )
        (.box 97 65)
      )
      (.splitB
        (.splitA
          (.box 0 193)
          (.box 65 0)
        )
        (.box 0 65)
      )
    )
  )

theorem f0Archived10Chart2_ok : checkChart f0Archived10 2 0 1 f0Archived10Chart2 = true := by decide +kernel

end HlawkaSchatten.BelowExponent.FacetNumeric
