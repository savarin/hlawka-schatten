/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.FacetNumeric

/-! Archived facet prism certificate data: `F2Prism5Data`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true

@[expose] public section

namespace HlawkaSchatten.BelowExponent.FacetNumeric

def f2Archived5 : Prism := {
  vertices := [⟨435200, 38400, 38400, 0⟩,
    ⟨441200, 38800, 32000, 0⟩,
    ⟨448000, 32000, 32000, 0⟩,
    ⟨434112, 38304, 38304, 1280⟩,
    ⟨440097, 38703, 31920, 1280⟩,
    ⟨446880, 31920, 31920, 1280⟩]
  profileDen := 512000
  pi := [40398453, 251153213, 253328801, 528861357]
  slope := [491397069, -252780184, -254635999]
  radiusNum := 1
  radiusDen := 8
}

set_option maxRecDepth 40000
set_option maxHeartbeats 0

theorem f2Archived5_data_ok : dataOK f2Archived5 = true := by decide +kernel

def f2Archived5Chart0 : RowTree :=
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
                        (.splitB
                          (.box 127 127)
                          (.box 127 124)
                        )
                        (.splitB
                          (.box 124 127)
                          (.box 123 124)
                        )
                      )
                      (.splitB
                        (.box 125 120)
                        (.splitA
                          (.box 127 116)
                          (.box 123 116)
                        )
                      )
                    )
                    (.splitB
                      (.splitA
                        (.box 120 125)
                        (.splitB
                          (.box 116 127)
                          (.box 116 123)
                        )
                      )
                      (.splitA
                        (.splitB
                          (.box 120 120)
                          (.box 120 116)
                        )
                        (.splitB
                          (.box 116 120)
                          (.box 116 116)
                        )
                      )
                    )
                  )
                  (.splitB
                    (.splitA
                      (.box 125 111)
                      (.box 117 111)
                    )
                    (.splitA
                      (.box 125 104)
                      (.box 117 104)
                    )
                  )
                )
                (.splitB
                  (.splitA
                    (.splitB
                      (.box 111 125)
                      (.box 111 117)
                    )
                    (.splitB
                      (.box 104 125)
                      (.box 104 117)
                    )
                  )
                  (.splitA
                    (.splitB
                      (.box 111 111)
                      (.box 111 103)
                    )
                    (.splitB
                      (.box 103 111)
                      (.box 103 103)
                    )
                  )
                )
              )
              (.splitB
                (.splitA
                  (.box 121 92)
                  (.box 105 92)
                )
                (.splitA
                  (.box 121 79)
                  (.box 105 76)
                )
              )
            )
            (.splitB
              (.splitA
                (.splitB
                  (.box 92 121)
                  (.box 92 105)
                )
                (.splitB
                  (.box 79 121)
                  (.box 76 105)
                )
              )
              (.splitA
                (.splitB
                  (.box 92 89)
                  (.box 89 76)
                )
                (.splitB
                  (.box 76 89)
                  (.box 76 73)
                )
              )
            )
          )
          (.splitB
            (.splitA
              (.splitA
                (.box 121 161)
                (.box 105 177)
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
                (.box 81 257)
              )
            )
          )
        )
        (.splitB
          (.splitA
            (.splitB
              (.splitB
                (.box 161 121)
                (.box 177 105)
              )
              (.splitA
                (.box 177 81)
                (.box 145 81)
              )
            )
            (.splitB
              (.box 193 113)
              (.splitA
                (.box 225 81)
                (.box 257 81)
              )
            )
          )
          (.splitB
            (.splitA
              (.splitA
                (.splitB
                  (.box 177 177)
                  (.box 169 145)
                )
                (.splitB
                  (.box 145 169)
                  (.splitA
                    (.box 149 138)
                    (.splitB
                      (.box 137 153)
                      (.box 133 133)
                    )
                  )
                )
              )
              (.splitA
                (.splitB
                  (.box 225 169)
                  (.splitA
                    (.splitB
                      (.box 241 153)
                      (.splitA
                        (.box 249 133)
                        (.box 233 133)
                      )
                    )
                    (.splitB
                      (.box 209 153)
                      (.box 217 133)
                    )
                  )
                )
                (.splitB
                  (.box 257 161)
                  (.box 289 138)
                )
              )
            )
            (.splitA
              (.splitB
                (.splitA
                  (.box 169 225)
                  (.splitB
                    (.splitA
                      (.box 153 241)
                      (.splitB
                        (.box 133 249)
                        (.box 133 233)
                      )
                    )
                    (.splitA
                      (.box 153 209)
                      (.box 133 217)
                    )
                  )
                )
                (.splitA
                  (.box 177 289)
                  (.box 138 290)
                )
              )
              (.splitA
                (.splitB
                  (.splitA
                    (.splitB
                      (.splitB
                        (.splitA
                          (.box 249 245)
                          (.box 233 245)
                        )
                        (.splitA
                          (.box 249 234)
                          (.splitA
                            (.box 237 233)
                            (.box 229 233)
                          )
                        )
                      )
                      (.splitA
                        (.box 249 217)
                        (.splitB
                          (.box 233 217)
                          (.box 233 201)
                        )
                      )
                    )
                    (.splitB
                      (.splitB
                        (.box 217 249)
                        (.box 217 233)
                      )
                      (.box 217 217)
                    )
                  )
                  (.splitA
                    (.box 241 289)
                    (.box 209 289)
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
          (.splitB
            (.box 82 257)
            (.box 97 161)
          )
          (.box 84 75)
        )
        (.splitB
          (.splitA
            (.splitB
              (.box 160 257)
              (.box 161 161)
            )
            (.splitA
              (.splitB
                (.box 225 257)
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
          (.splitA
            (.box 257 82)
            (.box 161 97)
          )
          (.box 75 84)
        )
        (.splitA
          (.splitB
            (.splitA
              (.box 257 161)
              (.box 161 161)
            )
            (.splitB
              (.splitA
                (.box 257 225)
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
      (.splitA
        (.splitB
          (.splitA
            (.box 0 193)
            (.box 161 129)
          )
          (.box 0 75)
        )
        (.box 97 129)
      )
    )
  )

theorem f2Archived5Chart0_ok : checkChart f2Archived5 0 1 2 f2Archived5Chart0 = true := by decide +kernel

def f2Archived5Chart1 : RowTree :=
  (.splitA
    (.splitB
      (.splitA
        (.splitB
          (.box 84 75)
          (.splitA
            (.box 113 193)
            (.splitB
              (.box 81 161)
              (.box 81 193)
            )
          )
        )
        (.splitB
          (.box 129 65)
          (.splitA
            (.splitB
              (.box 161 161)
              (.box 161 257)
            )
            (.splitA
              (.splitB
                (.box 225 161)
                (.box 225 193)
              )
              (.box 257 193)
            )
          )
        )
      )
      (.splitA
        (.splitB
          (.splitA
            (.splitB
              (.box 113 225)
              (.splitA
                (.box 121 177)
                (.splitB
                  (.box 105 145)
                  (.box 105 177)
                )
              )
            )
            (.splitB
              (.splitB
                (.box 81 257)
                (.box 81 225)
              )
              (.splitA
                (.splitB
                  (.box 89 145)
                  (.box 89 177)
                )
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
                    (.box 123 92)
                    (.box 117 92)
                  )
                )
                (.splitB
                  (.box 105 76)
                  (.splitA
                    (.splitB
                      (.box 109 88)
                      (.box 109 95)
                    )
                    (.splitB
                      (.box 101 88)
                      (.box 101 95)
                    )
                  )
                )
              )
              (.splitA
                (.splitB
                  (.splitA
                    (.splitB
                      (.box 123 104)
                      (.splitA
                        (.box 126 111)
                        (.box 123 110)
                      )
                    )
                    (.splitB
                      (.box 117 103)
                      (.splitA
                        (.splitB
                          (.box 119 108)
                          (.box 119 112)
                        )
                        (.splitB
                          (.box 115 108)
                          (.box 115 112)
                        )
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
                          (.box 123 123)
                          (.box 123 127)
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
                        (.splitB
                          (.box 120 123)
                          (.box 120 126)
                        )
                        (.splitB
                          (.box 116 123)
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
                      (.box 111 124)
                    )
                    (.splitB
                      (.box 103 117)
                      (.box 103 123)
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
                (.splitB
                  (.box 76 105)
                  (.box 79 118)
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
              (.splitA
                (.box 177 162)
                (.box 145 161)
              )
            )
            (.splitB
              (.splitA
                (.box 225 193)
                (.box 257 193)
              )
              (.box 225 161)
            )
          )
          (.splitA
            (.splitB
              (.splitA
                (.box 177 81)
                (.box 145 81)
              )
              (.box 177 105)
            )
            (.splitB
              (.box 193 81)
              (.box 193 113)
            )
          )
        )
      )
    )
    (.splitB
      (.splitA
        (.splitB
          (.box 129 65)
          (.splitA
            (.box 257 193)
            (.box 161 129)
          )
        )
        (.box 84 65)
      )
      (.splitA
        (.splitB
          (.splitB
            (.box 193 257)
            (.box 193 161)
          )
          (.box 193 97)
        )
        (.box 97 129)
      )
    )
  )

theorem f2Archived5Chart1_ok : checkChart f2Archived5 1 0 2 f2Archived5Chart1 = true := by decide +kernel

def f2Archived5Chart2 : RowTree :=
  (.splitA
    (.splitB
      (.splitA
        (.splitB
          (.box 97 75)
          (.splitA
            (.box 113 193)
            (.box 81 193)
          )
        )
        (.splitB
          (.box 129 65)
          (.splitA
            (.splitB
              (.box 161 161)
              (.box 161 257)
            )
            (.splitA
              (.splitB
                (.box 225 161)
                (.box 225 193)
              )
              (.box 257 193)
            )
          )
        )
      )
      (.splitA
        (.splitB
          (.splitA
            (.splitB
              (.box 113 225)
              (.splitA
                (.box 121 177)
                (.splitB
                  (.box 105 145)
                  (.box 105 177)
                )
              )
            )
            (.splitB
              (.splitA
                (.box 89 193)
                (.box 73 193)
              )
              (.splitA
                (.splitB
                  (.box 89 145)
                  (.box 89 177)
                )
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
                    (.box 123 92)
                    (.box 117 92)
                  )
                )
                (.splitB
                  (.box 105 76)
                  (.splitA
                    (.splitB
                      (.box 109 88)
                      (.box 109 95)
                    )
                    (.splitB
                      (.box 101 88)
                      (.box 101 95)
                    )
                  )
                )
              )
              (.splitA
                (.splitB
                  (.splitA
                    (.splitB
                      (.box 123 104)
                      (.splitA
                        (.box 126 111)
                        (.box 123 110)
                      )
                    )
                    (.splitB
                      (.box 117 103)
                      (.splitA
                        (.splitB
                          (.box 119 108)
                          (.box 119 112)
                        )
                        (.splitB
                          (.box 115 108)
                          (.box 115 112)
                        )
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
                          (.box 123 123)
                          (.box 123 127)
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
                        (.splitB
                          (.box 120 123)
                          (.box 120 126)
                        )
                        (.splitB
                          (.box 116 123)
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
                      (.box 111 124)
                    )
                    (.splitB
                      (.box 103 117)
                      (.box 103 123)
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
                (.splitB
                  (.box 76 105)
                  (.box 79 118)
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
                (.box 161 241)
              )
              (.splitA
                (.box 185 161)
                (.box 145 161)
              )
            )
            (.splitB
              (.splitA
                (.box 225 193)
                (.box 257 193)
              )
              (.box 225 161)
            )
          )
          (.splitA
            (.splitB
              (.splitA
                (.box 177 81)
                (.box 145 81)
              )
              (.box 177 105)
            )
            (.splitB
              (.box 193 81)
              (.box 193 113)
            )
          )
        )
      )
    )
    (.splitB
      (.splitA
        (.splitB
          (.box 129 65)
          (.splitA
            (.splitB
              (.box 193 161)
              (.box 193 193)
            )
            (.box 161 129)
          )
        )
        (.splitB
          (.box 84 84)
          (.box 97 129)
        )
      )
      (.splitA
        (.splitB
          (.splitB
            (.box 193 257)
            (.box 193 161)
          )
          (.box 193 97)
        )
        (.box 97 129)
      )
    )
  )

theorem f2Archived5Chart2_ok : checkChart f2Archived5 2 0 1 f2Archived5Chart2 = true := by decide +kernel

end HlawkaSchatten.BelowExponent.FacetNumeric
