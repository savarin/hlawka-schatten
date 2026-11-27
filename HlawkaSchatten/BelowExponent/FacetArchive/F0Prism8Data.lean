/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.FacetNumeric

/-! Archived facet prism certificate data: `F0Prism8Data`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true

@[expose] public section

namespace HlawkaSchatten.BelowExponent.FacetNumeric

def f0Archived8 : Prism := {
  vertices := [⟨27200, 10400, 10400, 0⟩,
    ⟨32800, 7600, 7600, 0⟩,
    ⟨30000, 13200, 4800, 0⟩,
    ⟨27132, 10374, 10374, 120⟩,
    ⟨32718, 7581, 7581, 120⟩,
    ⟨29925, 13167, 4788, 120⟩]
  profileDen := 48000
  pi := [105193952, 203426177, 243561049, 521560646]
  slope := [251617809, -115629954, -166608390]
  radiusNum := 1
  radiusDen := 8
}

set_option maxRecDepth 40000
set_option maxHeartbeats 0

theorem f0Archived8_data_ok : dataOK f0Archived8 = true := by decide +kernel

def f0Archived8Chart0 : RowTree :=
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
                        (.box 125 117)
                      )
                    )
                    (.splitB
                      (.splitA
                        (.box 120 125)
                        (.box 117 125)
                      )
                      (.box 119 118)
                    )
                  )
                  (.splitA
                    (.splitB
                      (.box 125 112)
                      (.box 125 105)
                    )
                    (.box 119 108)
                  )
                )
                (.splitB
                  (.splitB
                    (.box 108 125)
                    (.box 108 119)
                  )
                  (.box 108 108)
                )
              )
              (.splitA
                (.splitB
                  (.box 121 95)
                  (.box 121 79)
                )
                (.box 108 87)
              )
            )
            (.splitB
              (.splitB
                (.box 87 121)
                (.box 87 105)
              )
              (.splitB
                (.box 87 92)
                (.box 87 76)
              )
            )
          )
          (.splitB
            (.splitA
              (.box 113 161)
              (.box 81 161)
            )
            (.splitA
              (.box 113 193)
              (.box 81 193)
            )
          )
        )
        (.splitB
          (.splitA
            (.splitB
              (.box 161 113)
              (.box 161 81)
            )
            (.box 225 97)
          )
          (.splitB
            (.splitA
              (.splitA
                (.box 177 161)
                (.box 145 145)
              )
              (.splitA
                (.box 225 145)
                (.box 257 129)
              )
            )
            (.splitA
              (.splitB
                (.splitA
                  (.box 177 225)
                  (.box 129 224)
                )
                (.splitA
                  (.box 177 257)
                  (.box 129 289)
                )
              )
              (.splitA
                (.splitB
                  (.splitA
                    (.splitB
                      (.box 241 241)
                      (.box 233 201)
                    )
                    (.splitB
                      (.box 209 241)
                      (.splitA
                        (.box 217 201)
                        (.box 201 201)
                      )
                    )
                  )
                  (.splitA
                    (.splitB
                      (.box 233 305)
                      (.box 241 321)
                    )
                    (.splitB
                      (.splitA
                        (.box 217 305)
                        (.box 201 305)
                      )
                      (.box 209 321)
                    )
                  )
                )
                (.splitB
                  (.splitA
                    (.box 193 209)
                    (.box 321 225)
                  )
                  (.splitB
                    (.box 289 305)
                    (.box 193 257)
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
              (.box 161 0)
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
                (.box 257 0)
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
        (.splitA
          (.box 0 97)
          (.box 97 97)
        )
        (.splitB
          (.splitA
            (.box 0 161)
            (.box 97 161)
          )
          (.splitA
            (.box 0 193)
            (.box 97 193)
          )
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

theorem f0Archived8Chart0_ok : checkChart f0Archived8 0 1 2 f0Archived8Chart0 = true := by decide +kernel

def f0Archived8Chart1 : RowTree :=
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
              (.box 81 177)
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
                      (.box 119 104)
                      (.box 119 111)
                    )
                  )
                  (.splitA
                    (.splitB
                      (.splitB
                        (.splitA
                          (.box 125 117)
                          (.box 125 116)
                        )
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
                        (.box 119 119)
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
                    (.box 108 123)
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
                (.box 87 118)
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
          (.box 193 129)
          (.box 97 129)
        )
        (.box 129 97)
      )
    )
  )

theorem f0Archived8Chart1_ok : checkChart f0Archived8 1 0 2 f0Archived8Chart1 = true := by decide +kernel

def f0Archived8Chart2 : RowTree :=
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
              (.box 113 65)
            )
            (.splitB
              (.box 81 193)
              (.box 81 177)
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
                  (.box 102 81)
                  (.box 105 92)
                )
              )
              (.splitA
                (.splitB
                  (.splitA
                    (.splitB
                      (.box 123 105)
                      (.box 123 113)
                    )
                    (.splitB
                      (.box 115 105)
                      (.box 117 111)
                    )
                  )
                  (.splitA
                    (.splitB
                      (.splitA
                        (.splitB
                          (.box 126 117)
                          (.box 126 120)
                        )
                        (.splitB
                          (.box 122 117)
                          (.box 123 120)
                        )
                      )
                      (.splitA
                        (.box 128 125)
                        (.box 123 125)
                      )
                    )
                    (.splitB
                      (.splitB
                        (.splitA
                          (.box 119 116)
                          (.box 116 116)
                        )
                        (.splitA
                          (.box 120 119)
                          (.box 116 119)
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
                  (.splitB
                    (.splitA
                      (.box 109 104)
                      (.box 103 103)
                    )
                    (.splitA
                      (.box 111 109)
                      (.box 104 109)
                    )
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
              (.splitB
                (.splitA
                  (.box 89 79)
                  (.box 76 76)
                )
                (.splitA
                  (.box 92 89)
                  (.box 79 89)
                )
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
              (.box 177 81)
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
          (.box 193 193)
        )
        (.box 65 65)
      )
      (.splitB
        (.splitA
          (.box 193 193)
          (.box 65 0)
        )
        (.box 129 97)
      )
    )
  )

theorem f0Archived8Chart2_ok : checkChart f0Archived8 2 0 1 f0Archived8Chart2 = true := by decide +kernel

end HlawkaSchatten.BelowExponent.FacetNumeric
