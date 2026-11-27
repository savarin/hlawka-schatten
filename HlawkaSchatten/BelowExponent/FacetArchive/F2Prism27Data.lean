/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.FacetNumeric

/-! Archived facet prism certificate data: `F2Prism27Data`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true

@[expose] public section

namespace HlawkaSchatten.BelowExponent.FacetNumeric

def f2Archived27 : Prism := {
  vertices := [⟨421600, 52000, 38400, 0⟩,
    ⟨420800, 59200, 32000, 0⟩,
    ⟨427600, 52400, 32000, 0⟩,
    ⟨420546, 51870, 38304, 1280⟩,
    ⟨419748, 59052, 31920, 1280⟩,
    ⟨426531, 52269, 31920, 1280⟩]
  profileDen := 512000
  pi := [53334296, 255258156, 237772561, 527376811]
  slope := [452315423, -202380907, -268922721]
  radiusNum := 1
  radiusDen := 8
}

set_option maxRecDepth 40000
set_option maxHeartbeats 0

theorem f2Archived27_data_ok : dataOK f2Archived27 = true := by decide +kernel

def f2Archived27Chart0 : RowTree :=
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
                        (.splitA
                          (.box 127 127)
                          (.box 124 127)
                        )
                        (.splitA
                          (.box 127 124)
                          (.box 124 123)
                        )
                      )
                      (.splitA
                        (.box 120 125)
                        (.box 116 125)
                      )
                    )
                    (.splitA
                      (.splitB
                        (.box 125 120)
                        (.splitA
                          (.box 126 116)
                          (.box 125 116)
                        )
                      )
                      (.splitB
                        (.box 118 120)
                        (.box 119 116)
                      )
                    )
                  )
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
                )
                (.splitA
                  (.splitB
                    (.splitA
                      (.box 125 111)
                      (.box 119 111)
                    )
                    (.splitA
                      (.box 121 104)
                      (.box 121 103)
                    )
                  )
                  (.splitB
                    (.box 108 109)
                    (.box 108 103)
                  )
                )
              )
              (.splitB
                (.splitA
                  (.box 95 121)
                  (.box 81 121)
                )
                (.splitA
                  (.box 95 105)
                  (.box 79 105)
                )
              )
            )
            (.splitA
              (.splitB
                (.splitA
                  (.box 121 92)
                  (.box 105 92)
                )
                (.splitA
                  (.box 121 76)
                  (.box 105 76)
                )
              )
              (.splitB
                (.splitA
                  (.box 92 92)
                  (.box 79 89)
                )
                (.splitA
                  (.box 92 76)
                  (.box 76 76)
                )
              )
            )
          )
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
        )
        (.splitA
          (.splitB
            (.splitA
              (.splitA
                (.box 121 161)
                (.box 105 161)
              )
              (.splitB
                (.box 81 177)
                (.box 81 145)
              )
            )
            (.splitA
              (.box 113 193)
              (.splitB
                (.box 81 225)
                (.box 81 289)
              )
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
                  (.splitA
                    (.box 153 137)
                    (.box 137 137)
                  )
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
                (.box 193 145)
              )
            )
            (.splitA
              (.splitB
                (.splitA
                  (.box 169 225)
                  (.splitB
                    (.splitA
                      (.box 153 241)
                      (.splitA
                        (.box 141 233)
                        (.box 133 233)
                      )
                    )
                    (.splitA
                      (.box 153 209)
                      (.splitB
                        (.splitA
                          (.box 141 217)
                          (.box 133 217)
                        )
                        (.box 134 205)
                      )
                    )
                  )
                )
                (.splitA
                  (.box 177 289)
                  (.splitB
                    (.splitA
                      (.box 153 289)
                      (.box 137 305)
                    )
                    (.box 145 321)
                  )
                )
              )
              (.splitB
                (.splitA
                  (.splitB
                    (.splitA
                      (.splitA
                        (.box 249 233)
                        (.box 233 233)
                      )
                      (.box 209 233)
                    )
                    (.splitA
                      (.splitB
                        (.splitA
                          (.box 249 217)
                          (.box 233 217)
                        )
                        (.splitA
                          (.box 249 201)
                          (.box 233 201)
                        )
                      )
                      (.box 225 209)
                    )
                  )
                  (.box 193 225)
                )
                (.splitA
                  (.splitA
                    (.splitB
                      (.box 241 306)
                      (.box 241 321)
                    )
                    (.box 225 289)
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
          (.splitB
            (.box 81 257)
            (.box 97 161)
          )
          (.box 84 75)
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
            (.box 193 145)
            (.splitA
              (.box 0 193)
              (.box 161 193)
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

theorem f2Archived27Chart0_ok : checkChart f2Archived27 0 1 2 f2Archived27Chart0 = true := by decide +kernel

def f2Archived27Chart1 : RowTree :=
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
            (.splitB
              (.box 193 161)
              (.box 193 257)
            )
          )
        )
      )
      (.splitA
        (.splitB
          (.splitB
            (.splitA
              (.box 113 225)
              (.splitB
                (.box 81 257)
                (.box 81 225)
              )
            )
            (.splitA
              (.splitA
                (.box 121 177)
                (.splitB
                  (.box 105 145)
                  (.box 105 177)
                )
              )
              (.splitA
                (.splitB
                  (.box 89 145)
                  (.box 89 177)
                )
                (.box 77 161)
              )
            )
          )
          (.splitA
            (.splitB
              (.splitA
                (.splitB
                  (.box 118 79)
                  (.splitA
                    (.box 123 92)
                    (.box 117 92)
                  )
                )
                (.splitB
                  (.box 105 76)
                  (.splitA
                    (.box 109 92)
                    (.box 103 89)
                  )
                )
              )
              (.splitA
                (.splitB
                  (.splitA
                    (.splitB
                      (.box 125 103)
                      (.splitA
                        (.box 126 111)
                        (.box 123 111)
                      )
                    )
                    (.splitB
                      (.box 117 103)
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
                          (.box 127 116)
                          (.box 123 116)
                        )
                        (.splitA
                          (.box 127 120)
                          (.box 123 120)
                        )
                      )
                      (.splitA
                        (.splitB
                          (.box 127 123)
                          (.box 127 127)
                        )
                        (.splitB
                          (.box 124 123)
                          (.box 124 127)
                        )
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
                      (.box 109 103)
                      (.box 111 109)
                    )
                    (.box 104 105)
                  )
                  (.splitA
                    (.splitB
                      (.box 111 117)
                      (.box 111 125)
                    )
                    (.box 104 121)
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
                (.box 76 81)
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
              (.splitA
                (.box 177 161)
                (.box 145 161)
              )
            )
            (.splitB
              (.box 225 257)
              (.box 193 161)
            )
          )
          (.splitA
            (.splitB
              (.box 177 81)
              (.box 177 113)
            )
            (.box 129 81)
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
        (.splitA
          (.box 129 81)
          (.box 65 75)
        )
      )
    )
  )

theorem f2Archived27Chart1_ok : checkChart f2Archived27 1 0 2 f2Archived27Chart1 = true := by decide +kernel

def f2Archived27Chart2 : RowTree :=
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
        (.splitA
          (.splitB
            (.box 161 97)
            (.box 161 193)
          )
          (.splitB
            (.box 0 65)
            (.splitB
              (.box 193 161)
              (.box 193 193)
            )
          )
        )
      )
      (.splitA
        (.splitB
          (.splitA
            (.splitB
              (.box 113 193)
              (.splitA
                (.box 121 161)
                (.box 105 177)
              )
            )
            (.splitB
              (.box 81 225)
              (.splitA
                (.box 89 177)
                (.splitB
                  (.box 73 145)
                  (.box 73 177)
                )
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
                    (.box 115 92)
                  )
                )
                (.splitB
                  (.box 105 76)
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
                      (.box 123 104)
                      (.splitA
                        (.box 126 112)
                        (.box 123 111)
                      )
                    )
                    (.splitB
                      (.box 117 103)
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
                          (.box 126 116)
                          (.box 123 116)
                        )
                        (.splitA
                          (.box 127 120)
                          (.box 123 120)
                        )
                      )
                      (.splitA
                        (.splitB
                          (.box 127 123)
                          (.box 127 127)
                        )
                        (.splitB
                          (.box 123 123)
                          (.box 124 126)
                        )
                      )
                    )
                    (.splitB
                      (.splitA
                        (.splitB
                          (.box 119 116)
                          (.box 120 119)
                        )
                        (.splitB
                          (.box 116 115)
                          (.box 116 119)
                        )
                      )
                      (.splitA
                        (.box 120 125)
                        (.splitB
                          (.box 116 122)
                          (.box 116 126)
                        )
                      )
                    )
                  )
                )
                (.splitB
                  (.splitA
                    (.splitB
                      (.box 109 103)
                      (.splitA
                        (.box 112 109)
                        (.box 108 109)
                      )
                    )
                    (.splitB
                      (.box 103 101)
                      (.box 103 109)
                    )
                  )
                  (.splitA
                    (.splitB
                      (.splitA
                        (.box 112 117)
                        (.box 108 117)
                      )
                      (.box 111 123)
                    )
                    (.splitB
                      (.box 104 115)
                      (.box 104 122)
                    )
                  )
                )
              )
            )
            (.splitB
              (.splitA
                (.splitB
                  (.box 89 76)
                  (.splitA
                    (.box 95 89)
                    (.box 88 89)
                  )
                )
                (.splitB
                  (.box 76 73)
                  (.box 76 89)
                )
              )
              (.splitA
                (.splitB
                  (.splitA
                    (.box 95 105)
                    (.box 88 105)
                  )
                  (.box 92 118)
                )
                (.box 79 107)
              )
            )
          )
        )
        (.splitB
          (.splitA
            (.splitB
              (.splitA
                (.box 177 193)
                (.box 145 193)
              )
              (.splitA
                (.box 177 161)
                (.box 145 161)
              )
            )
            (.splitB
              (.splitA
                (.box 225 193)
                (.box 257 193)
              )
              (.box 193 160)
            )
          )
          (.splitA
            (.splitB
              (.splitA
                (.box 177 81)
                (.box 145 81)
              )
              (.box 177 113)
            )
            (.box 129 81)
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
      (.splitA
        (.splitB
          (.splitA
            (.splitB
              (.box 193 193)
              (.box 193 161)
            )
            (.box 161 129)
          )
          (.box 129 81)
        )
        (.box 97 129)
      )
    )
  )

theorem f2Archived27Chart2_ok : checkChart f2Archived27 2 0 1 f2Archived27Chart2 = true := by decide +kernel

end HlawkaSchatten.BelowExponent.FacetNumeric
