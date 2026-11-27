/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.FacetNumeric

/-! Archived facet prism certificate data: `F2Prism48Data`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true

@[expose] public section

namespace HlawkaSchatten.BelowExponent.FacetNumeric

def f2Archived48 : Prism := {
  vertices := [⟨197600, 36000, 22400, 0⟩,
    ⟨196800, 43200, 16000, 0⟩,
    ⟨200400, 38000, 17600, 0⟩,
    ⟨197106, 35910, 22344, 640⟩,
    ⟨196308, 43092, 15960, 640⟩,
    ⟨199899, 37905, 17556, 640⟩]
  profileDen := 256000
  pi := [70248621, 245630580, 231678156, 526184467]
  slope := [393269225, -147428698, -267213420]
  radiusNum := 1
  radiusDen := 8
}

set_option maxRecDepth 40000
set_option maxHeartbeats 0

theorem f2Archived48_data_ok : dataOK f2Archived48 = true := by decide +kernel

def f2Archived48Chart0 : RowTree :=
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
                        (.box 126 123)
                      )
                      (.splitA
                        (.box 120 125)
                        (.box 117 125)
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
                        (.box 119 120)
                        (.box 119 116)
                      )
                    )
                  )
                  (.splitB
                    (.box 108 125)
                    (.box 108 117)
                  )
                )
                (.splitA
                  (.splitA
                    (.splitB
                      (.box 125 111)
                      (.box 125 104)
                    )
                    (.splitB
                      (.box 119 111)
                      (.box 119 103)
                    )
                  )
                  (.splitB
                    (.box 108 111)
                    (.box 108 103)
                  )
                )
              )
              (.splitB
                (.box 87 121)
                (.box 87 105)
              )
            )
            (.splitA
              (.splitB
                (.splitA
                  (.box 121 92)
                  (.box 108 92)
                )
                (.box 113 78)
              )
              (.splitB
                (.box 87 89)
                (.box 87 73)
              )
            )
          )
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
        )
        (.splitA
          (.splitB
            (.splitA
              (.box 112 176)
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
                  (.box 145 129)
                )
              )
              (.splitA
                (.box 241 145)
                (.box 257 145)
              )
            )
            (.splitA
              (.splitB
                (.splitA
                  (.box 161 224)
                  (.splitA
                    (.splitB
                      (.box 153 241)
                      (.box 145 209)
                    )
                    (.splitB
                      (.box 137 241)
                      (.splitA
                        (.splitB
                          (.box 141 217)
                          (.box 141 201)
                        )
                        (.splitB
                          (.box 133 217)
                          (.box 133 201)
                        )
                      )
                    )
                  )
                )
                (.splitA
                  (.box 161 289)
                  (.splitA
                    (.splitB
                      (.box 153 305)
                      (.box 153 321)
                    )
                    (.splitB
                      (.splitA
                        (.box 141 305)
                        (.splitB
                          (.box 133 305)
                          (.box 133 273)
                        )
                      )
                      (.box 137 321)
                    )
                  )
                )
              )
              (.splitB
                (.splitA
                  (.splitB
                    (.box 241 225)
                    (.splitA
                      (.splitB
                        (.box 241 209)
                        (.box 248 201)
                      )
                      (.box 209 209)
                    )
                  )
                  (.box 193 225)
                )
                (.splitA
                  (.splitB
                    (.splitA
                      (.splitB
                        (.box 249 313)
                        (.box 241 289)
                      )
                      (.box 209 305)
                    )
                    (.box 241 257)
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
            (.box 73 193)
          )
          (.box 84 75)
        )
        (.splitB
          (.splitA
            (.splitB
              (.box 161 0)
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
        (.box 129 80)
        (.splitB
          (.splitA
            (.box 0 145)
            (.box 97 161)
          )
          (.splitA
            (.box 193 193)
            (.box 97 193)
          )
        )
      )
      (.splitB
        (.splitA
          (.box 193 193)
          (.box 97 129)
        )
        (.box 65 97)
      )
    )
  )

theorem f2Archived48Chart0_ok : checkChart f2Archived48 0 1 2 f2Archived48Chart0 = true := by decide +kernel

def f2Archived48Chart1 : RowTree :=
  (.splitA
    (.splitB
      (.splitA
        (.splitB
          (.box 84 75)
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
                (.box 104 176)
              )
              (.splitA
                (.box 92 161)
                (.box 73 161)
              )
            )
          )
          (.splitA
            (.splitB
              (.splitA
                (.splitB
                  (.box 121 76)
                  (.splitA
                    (.box 123 92)
                    (.box 117 92)
                  )
                )
                (.splitB
                  (.box 105 76)
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
                          (.box 124 124)
                          (.box 124 125)
                        )
                      )
                    )
                    (.splitB
                      (.splitB
                        (.splitA
                          (.box 120 116)
                          (.box 116 116)
                        )
                        (.splitA
                          (.box 120 119)
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
                      (.box 111 117)
                      (.box 104 117)
                    )
                    (.splitA
                      (.box 112 125)
                      (.box 105 123)
                    )
                  )
                )
              )
            )
            (.splitB
              (.splitB
                (.splitA
                  (.box 92 76)
                  (.box 79 73)
                )
                (.splitA
                  (.box 92 92)
                  (.box 79 89)
                )
              )
              (.splitB
                (.splitA
                  (.box 92 105)
                  (.box 79 105)
                )
                (.splitA
                  (.box 95 121)
                  (.box 81 118)
                )
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
              (.box 177 161)
            )
            (.splitB
              (.box 225 193)
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
        (.splitB
          (.box 129 97)
          (.box 193 193)
        )
        (.box 97 65)
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

theorem f2Archived48Chart1_ok : checkChart f2Archived48 1 0 2 f2Archived48Chart1 = true := by decide +kernel

def f2Archived48Chart2 : RowTree :=
  (.splitA
    (.splitB
      (.splitA
        (.splitB
          (.box 97 97)
          (.box 97 193)
        )
        (.splitA
          (.splitB
            (.box 161 97)
            (.box 161 193)
          )
          (.splitB
            (.box 0 65)
            (.box 193 193)
          )
        )
      )
      (.splitA
        (.splitB
          (.splitA
            (.splitB
              (.box 113 193)
              (.box 112 177)
            )
            (.splitB
              (.box 81 193)
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
                  (.box 118 81)
                  (.box 118 95)
                )
                (.splitB
                  (.box 102 81)
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
                      (.box 124 112)
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
                      (.splitA
                        (.splitB
                          (.box 126 117)
                          (.box 126 120)
                        )
                        (.splitB
                          (.box 123 116)
                          (.box 123 120)
                        )
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
                          (.box 116 115)
                          (.box 116 119)
                        )
                      )
                      (.splitA
                        (.box 120 125)
                        (.box 116 124)
                      )
                    )
                  )
                )
                (.splitB
                  (.splitA
                    (.splitB
                      (.box 109 103)
                      (.splitA
                        (.box 111 111)
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
                      (.box 111 116)
                      (.box 111 123)
                    )
                    (.box 104 118)
                  )
                )
              )
            )
            (.splitB
              (.splitA
                (.splitB
                  (.box 89 76)
                  (.splitA
                    (.box 93 92)
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
                  (.box 92 105)
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
              (.box 160 225)
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
              (.box 193 161)
            )
          )
          (.splitA
            (.splitB
              (.splitA
                (.box 177 81)
                (.box 145 81)
              )
              (.box 161 105)
            )
            (.box 193 82)
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
          (.box 0 75)
        )
        (.box 97 65)
      )
    )
  )

theorem f2Archived48Chart2_ok : checkChart f2Archived48 2 0 1 f2Archived48Chart2 = true := by decide +kernel

end HlawkaSchatten.BelowExponent.FacetNumeric
