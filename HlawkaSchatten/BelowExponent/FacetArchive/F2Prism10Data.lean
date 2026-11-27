/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.FacetNumeric

/-! Archived facet prism certificate data: `F2Prism10Data`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true

@[expose] public section

namespace HlawkaSchatten.BelowExponent.FacetNumeric

def f2Archived10 : Prism := {
  vertices := [⟨441200, 38800, 32000, 0⟩,
    ⟨434400, 45600, 32000, 0⟩,
    ⟨440800, 42400, 28800, 0⟩,
    ⟨440097, 38703, 31920, 1280⟩,
    ⟨433314, 45486, 31920, 1280⟩,
    ⟨439698, 42294, 28728, 1280⟩]
  profileDen := 512000
  pi := [44743972, 254667679, 246024397, 528305776]
  slope := [477792723, -229173356, -265749643]
  radiusNum := 1
  radiusDen := 8
}

set_option maxRecDepth 40000
set_option maxHeartbeats 0

theorem f2Archived10_data_ok : dataOK f2Archived10 = true := by decide +kernel

def f2Archived10Chart0 : RowTree :=
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
                          (.box 127 116)
                          (.box 123 116)
                        )
                      )
                      (.splitB
                        (.splitA
                          (.box 120 120)
                          (.box 116 120)
                        )
                        (.box 118 116)
                      )
                    )
                  )
                  (.splitB
                    (.splitA
                      (.box 111 125)
                      (.box 104 125)
                    )
                    (.splitA
                      (.box 111 117)
                      (.box 104 117)
                    )
                  )
                )
                (.splitA
                  (.splitB
                    (.splitA
                      (.box 125 111)
                      (.box 117 111)
                    )
                    (.splitA
                      (.box 125 103)
                      (.box 117 103)
                    )
                  )
                  (.splitB
                    (.splitA
                      (.box 111 111)
                      (.box 104 109)
                    )
                    (.splitA
                      (.box 111 103)
                      (.box 103 103)
                    )
                  )
                )
              )
              (.splitA
                (.splitB
                  (.box 92 121)
                  (.box 92 105)
                )
                (.splitB
                  (.box 79 121)
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
              (.splitA
                (.splitB
                  (.box 92 92)
                  (.box 92 76)
                )
                (.splitB
                  (.box 79 89)
                  (.box 76 73)
                )
              )
            )
          )
          (.splitA
            (.splitB
              (.box 177 113)
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
        )
        (.splitA
          (.splitB
            (.splitA
              (.splitA
                (.box 121 177)
                (.box 105 176)
              )
              (.splitB
                (.box 81 177)
                (.box 81 144)
              )
            )
            (.splitA
              (.box 113 193)
              (.splitB
                (.box 73 225)
                (.box 81 289)
              )
            )
          )
          (.splitB
            (.splitA
              (.splitA
                (.splitB
                  (.box 177 177)
                  (.box 177 137)
                )
                (.splitB
                  (.box 145 177)
                  (.splitA
                    (.box 153 137)
                    (.splitB
                      (.box 137 153)
                      (.box 137 133)
                    )
                  )
                )
              )
              (.splitA
                (.splitB
                  (.box 225 177)
                  (.splitA
                    (.splitB
                      (.box 241 153)
                      (.box 241 133)
                    )
                    (.box 217 137)
                  )
                )
                (.splitB
                  (.box 257 177)
                  (.box 289 137)
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
                        (.box 134 233)
                      )
                    )
                    (.splitA
                      (.box 153 209)
                      (.splitB
                        (.box 134 217)
                        (.box 137 205)
                      )
                    )
                  )
                )
                (.splitA
                  (.box 177 289)
                  (.splitA
                    (.box 153 289)
                    (.splitB
                      (.box 137 193)
                      (.box 137 321)
                    )
                  )
                )
              )
              (.splitB
                (.splitA
                  (.splitA
                    (.splitB
                      (.splitB
                        (.splitA
                          (.box 249 249)
                          (.box 233 249)
                        )
                        (.splitA
                          (.box 249 233)
                          (.box 233 233)
                        )
                      )
                      (.splitB
                        (.splitA
                          (.box 249 217)
                          (.box 233 221)
                        )
                        (.box 241 205)
                      )
                    )
                    (.splitB
                      (.splitB
                        (.box 217 249)
                        (.box 217 233)
                      )
                      (.splitB
                        (.box 217 217)
                        (.box 209 209)
                      )
                    )
                  )
                  (.splitB
                    (.box 289 241)
                    (.box 289 209)
                  )
                )
                (.splitA
                  (.splitA
                    (.splitB
                      (.box 241 193)
                      (.box 241 321)
                    )
                    (.box 209 289)
                  )
                  (.box 193 290)
                )
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
              (.box 81 257)
            )
            (.box 97 161)
          )
          (.box 84 75)
        )
        (.splitB
          (.splitA
            (.splitB
              (.splitA
                (.box 177 257)
                (.box 145 257)
              )
              (.box 161 161)
            )
            (.splitB
              (.splitA
                (.box 225 257)
                (.box 257 257)
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
        (.splitA
          (.splitA
            (.box 0 84)
            (.box 161 97)
          )
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
              (.box 193 290)
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
        (.box 65 81)
      )
    )
  )

theorem f2Archived10Chart0_ok : checkChart f2Archived10 0 1 2 f2Archived10Chart0 = true := by decide +kernel

def f2Archived10Chart1 : RowTree :=
  (.splitA
    (.splitB
      (.splitA
        (.splitB
          (.box 97 75)
          (.splitA
            (.box 113 193)
            (.splitB
              (.box 81 161)
              (.box 81 193)
            )
          )
        )
        (.splitB
          (.box 129 97)
          (.splitA
            (.splitB
              (.box 161 161)
              (.box 161 257)
            )
            (.splitA
              (.box 225 193)
              (.box 257 193)
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
                (.box 121 176)
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
                    (.box 101 92)
                  )
                )
              )
              (.splitA
                (.splitB
                  (.splitA
                    (.splitB
                      (.box 125 103)
                      (.splitA
                        (.box 127 111)
                        (.box 123 110)
                      )
                    )
                    (.splitB
                      (.box 117 103)
                      (.splitA
                        (.box 119 110)
                        (.box 115 110)
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
                          (.box 120 124)
                          (.box 120 125)
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
                      (.box 111 125)
                    )
                    (.splitB
                      (.box 104 115)
                      (.box 104 123)
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
                  (.box 92 121)
                )
                (.splitB
                  (.box 79 102)
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
              (.box 177 113)
            )
            (.box 225 97)
          )
        )
      )
    )
    (.splitB
      (.splitA
        (.splitB
          (.box 129 97)
          (.splitA
            (.box 257 193)
            (.box 161 129)
          )
        )
        (.box 84 65)
      )
      (.splitB
        (.splitA
          (.splitA
            (.splitB
              (.box 193 193)
              (.box 193 161)
            )
            (.box 161 129)
          )
          (.box 84 0)
        )
        (.splitA
          (.box 193 97)
          (.box 75 75)
        )
      )
    )
  )

theorem f2Archived10Chart1_ok : checkChart f2Archived10 1 0 2 f2Archived10Chart1 = true := by decide +kernel

def f2Archived10Chart2 : RowTree :=
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
        (.splitA
          (.splitB
            (.box 161 97)
            (.splitB
              (.box 161 161)
              (.box 161 257)
            )
          )
          (.splitB
            (.box 193 97)
            (.splitA
              (.box 225 193)
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
                (.box 105 177)
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
                        (.box 126 111)
                        (.box 123 111)
                      )
                    )
                    (.splitB
                      (.box 117 103)
                      (.splitA
                        (.box 119 110)
                        (.box 115 110)
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
                        (.splitB
                          (.box 120 122)
                          (.box 120 126)
                        )
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
                      (.box 103 115)
                      (.box 104 123)
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
                  (.box 76 102)
                  (.box 79 118)
                )
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
                (.box 177 80)
                (.box 145 81)
              )
              (.box 177 113)
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
          (.box 129 97)
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
            (.box 194 257)
            (.box 193 161)
          )
          (.box 193 97)
        )
        (.box 97 129)
      )
    )
  )

theorem f2Archived10Chart2_ok : checkChart f2Archived10 2 0 1 f2Archived10Chart2 = true := by decide +kernel

end HlawkaSchatten.BelowExponent.FacetNumeric
