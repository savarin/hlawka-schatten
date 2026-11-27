/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.FacetNumeric

/-! Archived facet prism certificate data: `F2Prism14Data`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true

@[expose] public section

namespace HlawkaSchatten.BelowExponent.FacetNumeric

def f2Archived14 : Prism := {
  vertices := [⟨204800, 25600, 25600, 0⟩,
    ⟨210800, 26000, 19200, 0⟩,
    ⟨211200, 22400, 22400, 0⟩,
    ⟨204288, 25536, 25536, 640⟩,
    ⟨210273, 25935, 19152, 640⟩,
    ⟨210672, 22344, 22344, 640⟩]
  profileDen := 256000
  pi := [56946209, 248516146, 242175471, 526103998]
  slope := [440442780, -220677575, -241299037]
  radiusNum := 1
  radiusDen := 8
}

set_option maxRecDepth 40000
set_option maxHeartbeats 0

theorem f2Archived14_data_ok : dataOK f2Archived14 = true := by decide +kernel

def f2Archived14Chart0 : RowTree :=
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
                        (.box 125 124)
                      )
                      (.splitA
                        (.box 120 125)
                        (.box 116 125)
                      )
                    )
                    (.splitA
                      (.splitB
                        (.box 125 120)
                        (.box 125 116)
                      )
                      (.splitB
                        (.box 118 120)
                        (.box 119 116)
                      )
                    )
                  )
                  (.splitB
                    (.splitA
                      (.box 111 125)
                      (.box 104 125)
                    )
                    (.splitA
                      (.box 111 119)
                      (.box 104 117)
                    )
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
                      (.box 117 104)
                    )
                  )
                  (.splitB
                    (.splitA
                      (.box 111 111)
                      (.box 104 111)
                    )
                    (.box 108 103)
                  )
                )
              )
              (.splitB
                (.splitA
                  (.box 92 121)
                  (.box 79 121)
                )
                (.splitA
                  (.box 92 105)
                  (.box 79 105)
                )
              )
            )
            (.splitA
              (.splitB
                (.splitA
                  (.box 121 92)
                  (.box 108 92)
                )
                (.box 113 76)
              )
              (.splitB
                (.splitA
                  (.box 92 92)
                  (.box 76 92)
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
              (.box 177 113)
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
              (.box 113 177)
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
          (.splitB
            (.splitA
              (.splitA
                (.splitB
                  (.box 177 177)
                  (.box 177 145)
                )
                (.splitB
                  (.box 145 177)
                  (.splitB
                    (.box 145 153)
                    (.box 137 137)
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
                    (.splitB
                      (.box 209 153)
                      (.box 209 133)
                    )
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
                  (.box 177 225)
                  (.splitB
                    (.splitA
                      (.box 153 241)
                      (.box 133 241)
                    )
                    (.splitA
                      (.box 153 209)
                      (.box 137 216)
                    )
                  )
                )
                (.splitA
                  (.box 177 257)
                  (.box 137 289)
                )
              )
              (.splitB
                (.splitA
                  (.splitB
                    (.splitA
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
                        (.box 217 245)
                        (.splitA
                          (.box 217 233)
                          (.box 201 233)
                        )
                      )
                    )
                    (.splitA
                      (.splitA
                        (.box 249 217)
                        (.box 233 217)
                      )
                      (.splitB
                        (.box 216 221)
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
                    (.box 241 289)
                    (.box 209 289)
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
          (.box 82 193)
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

theorem f2Archived14Chart0_ok : checkChart f2Archived14 0 1 2 f2Archived14Chart0 = true := by decide +kernel

def f2Archived14Chart1 : RowTree :=
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
            (.box 161 193)
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
              (.box 113 193)
              (.splitA
                (.box 89 193)
                (.box 73 193)
              )
            )
            (.splitA
              (.splitA
                (.box 121 177)
                (.box 105 177)
              )
              (.splitA
                (.box 89 176)
                (.box 73 176)
              )
            )
          )
          (.splitA
            (.splitB
              (.splitA
                (.splitB
                  (.box 121 79)
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
                      (.box 125 104)
                      (.splitA
                        (.box 126 111)
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
                    (.splitB
                      (.box 103 103)
                      (.box 103 109)
                    )
                  )
                  (.splitA
                    (.splitB
                      (.box 111 117)
                      (.box 111 123)
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
                (.splitB
                  (.box 76 76)
                  (.box 76 89)
                )
              )
              (.splitA
                (.splitB
                  (.box 92 105)
                  (.box 92 118)
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
              (.splitB
                (.box 161 145)
                (.box 161 184)
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
              (.box 177 80)
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
          (.box 65 65)
        )
      )
    )
  )

theorem f2Archived14Chart1_ok : checkChart f2Archived14 1 0 2 f2Archived14Chart1 = true := by decide +kernel

def f2Archived14Chart2 : RowTree :=
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
                      (.box 123 105)
                      (.splitA
                        (.box 126 111)
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
                          (.box 116 116)
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
                      (.box 109 104)
                      (.box 110 109)
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
                  (.box 92 89)
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
                (.box 81 107)
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
              (.box 193 193)
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
            (.splitB
              (.box 193 193)
              (.box 193 161)
            )
            (.box 161 129)
          )
          (.box 75 0)
        )
        (.splitA
          (.box 129 81)
          (.box 65 65)
        )
      )
    )
  )

theorem f2Archived14Chart2_ok : checkChart f2Archived14 2 0 1 f2Archived14Chart2 = true := by decide +kernel

end HlawkaSchatten.BelowExponent.FacetNumeric
