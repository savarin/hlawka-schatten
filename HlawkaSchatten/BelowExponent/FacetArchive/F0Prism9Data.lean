/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.FacetNumeric

/-! Archived facet prism certificate data: `F0Prism9Data`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true

@[expose] public section

namespace HlawkaSchatten.BelowExponent.FacetNumeric

def f0Archived9 : Prism := {
  vertices := [⟨16000, 16000, 16000, 0⟩,
    ⟨24400, 16000, 7600, 0⟩,
    ⟨21600, 21600, 4800, 0⟩,
    ⟨15960, 15960, 15960, 120⟩,
    ⟨24339, 15960, 7581, 120⟩,
    ⟨21546, 21546, 4788, 120⟩]
  profileDen := 48000
  pi := [165074078, 165084497, 224922393, 518660856]
  slope := [185826856, -86925621, -135321352]
  radiusNum := 1
  radiusDen := 8
}

set_option maxRecDepth 40000
set_option maxHeartbeats 0

theorem f0Archived9_data_ok : dataOK f0Archived9 = true := by decide +kernel

def f0Archived9Chart0 : RowTree :=
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
                        (.box 125 117)
                      )
                    )
                    (.splitB
                      (.box 120 125)
                      (.box 119 118)
                    )
                  )
                  (.splitA
                    (.splitB
                      (.box 125 112)
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
                  (.box 108 108)
                )
              )
              (.splitA
                (.splitB
                  (.box 121 92)
                  (.box 121 79)
                )
                (.splitB
                  (.box 108 92)
                  (.box 108 79)
                )
              )
            )
            (.splitB
              (.box 92 113)
              (.splitB
                (.box 87 92)
                (.box 87 76)
              )
            )
          )
          (.splitB
            (.splitA
              (.box 113 161)
              (.box 81 177)
            )
            (.splitA
              (.box 113 193)
              (.box 81 193)
            )
          )
        )
        (.splitB
          (.splitB
            (.box 65 113)
            (.box 161 81)
          )
          (.splitB
            (.splitA
              (.box 161 161)
              (.box 193 161)
            )
            (.splitA
              (.splitB
                (.box 145 225)
                (.splitB
                  (.box 144 257)
                  (.splitA
                    (.box 177 321)
                    (.box 129 321)
                  )
                )
              )
              (.splitA
                (.splitB
                  (.box 225 225)
                  (.splitB
                    (.splitA
                      (.box 241 257)
                      (.box 209 257)
                    )
                    (.splitA
                      (.splitB
                        (.box 233 353)
                        (.box 233 321)
                      )
                      (.splitB
                        (.box 217 353)
                        (.box 217 385)
                      )
                    )
                  )
                )
                (.splitB
                  (.box 257 225)
                  (.splitA
                    (.splitB
                      (.box 289 289)
                      (.box 289 321)
                    )
                    (.box 321 257)
                  )
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
        (.splitA
          (.splitB
            (.splitB
              (.box 145 0)
              (.box 161 161)
            )
            (.box 161 97)
          )
          (.splitB
            (.splitA
              (.splitB
                (.box 225 0)
                (.box 225 161)
              )
              (.splitB
                (.box 193 0)
                (.box 257 161)
              )
            )
            (.box 193 97)
          )
        )
      )
    )
    (.splitB
      (.splitB
        (.box 0 75)
        (.splitA
          (.box 0 193)
          (.box 65 0)
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

theorem f0Archived9Chart0_ok : checkChart f0Archived9 0 1 2 f0Archived9Chart0 = true := by decide +kernel

def f0Archived9Chart1 : RowTree :=
  (.splitA
    (.splitB
      (.splitA
        (.splitB
          (.box 84 65)
          (.box 81 193)
        )
        (.splitB
          (.box 129 97)
          (.splitA
            (.box 160 193)
            (.box 225 193)
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
              (.box 113 161)
              (.box 81 177)
            )
          )
          (.splitB
            (.splitA
              (.box 160 193)
              (.box 193 257)
            )
            (.splitA
              (.box 161 161)
              (.box 193 161)
            )
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
                  (.box 108 79)
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
                    (.box 119 108)
                  )
                  (.splitA
                    (.splitB
                      (.splitB
                        (.box 125 117)
                        (.box 125 120)
                      )
                      (.splitA
                        (.box 127 125)
                        (.box 124 125)
                      )
                    )
                    (.splitB
                      (.box 120 118)
                      (.box 120 125)
                    )
                  )
                )
                (.splitB
                  (.box 111 105)
                  (.box 111 121)
                )
              )
            )
            (.splitB
              (.box 92 81)
              (.box 92 113)
            )
          )
          (.splitA
            (.box 65 97)
            (.box 193 97)
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
        (.box 0 84)
      )
    )
  )

theorem f0Archived9Chart1_ok : checkChart f0Archived9 1 0 2 f0Archived9Chart1 = true := by decide +kernel

def f0Archived9Chart2 : RowTree :=
  (.splitA
    (.splitB
      (.splitA
        (.box 97 0)
        (.splitB
          (.box 0 65)
          (.splitA
            (.box 161 0)
            (.splitB
              (.box 193 161)
              (.box 193 0)
            )
          )
        )
      )
      (.splitB
        (.splitA
          (.splitA
            (.box 113 161)
            (.splitB
              (.box 81 193)
              (.box 81 177)
            )
          )
          (.splitA
            (.splitB
              (.box 161 193)
              (.box 161 177)
            )
            (.splitB
              (.splitB
                (.box 193 257)
                (.box 193 225)
              )
              (.box 193 161)
            )
          )
        )
        (.splitA
          (.splitB
            (.splitA
              (.splitA
                (.box 115 92)
                (.splitB
                  (.box 102 81)
                  (.box 105 92)
                )
              )
              (.splitB
                (.box 81 79)
                (.splitA
                  (.box 92 92)
                  (.box 79 89)
                )
              )
            )
            (.splitA
              (.splitB
                (.splitA
                  (.splitA
                    (.box 122 111)
                    (.splitB
                      (.box 115 105)
                      (.box 117 111)
                    )
                  )
                  (.splitB
                    (.box 105 105)
                    (.splitA
                      (.box 111 111)
                      (.box 104 109)
                    )
                  )
                )
                (.splitA
                  (.splitB
                    (.splitA
                      (.splitB
                        (.box 123 117)
                        (.box 125 120)
                      )
                      (.splitB
                        (.box 117 117)
                        (.splitA
                          (.box 120 120)
                          (.box 116 119)
                        )
                      )
                    )
                    (.splitA
                      (.splitB
                        (.box 125 123)
                        (.box 125 128)
                      )
                      (.splitA
                        (.box 120 125)
                        (.box 117 123)
                      )
                    )
                  )
                  (.splitB
                    (.splitA
                      (.box 111 117)
                      (.box 105 115)
                    )
                    (.box 111 121)
                  )
                )
              )
              (.splitB
                (.splitA
                  (.box 92 105)
                  (.box 81 102)
                )
                (.box 92 115)
              )
            )
          )
          (.splitB
            (.splitA
              (.box 65 73)
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
          (.splitA
            (.box 0 193)
            (.box 161 129)
          )
        )
        (.box 97 65)
      )
      (.splitB
        (.splitA
          (.splitB
            (.splitA
              (.box 0 193)
              (.box 161 193)
            )
            (.box 0 161)
          )
          (.box 65 0)
        )
        (.box 129 97)
      )
    )
  )

theorem f0Archived9Chart2_ok : checkChart f0Archived9 2 0 1 f0Archived9Chart2 = true := by decide +kernel

end HlawkaSchatten.BelowExponent.FacetNumeric
