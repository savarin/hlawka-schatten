/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.FacetNumeric

/-! Archived facet prism certificate data: `F2Prism56Data`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true

@[expose] public section

namespace HlawkaSchatten.BelowExponent.FacetNumeric

def f2Archived56 : Prism := {
  vertices := [⟨163200, 73600, 19200, 0⟩,
    ⟨162800, 77200, 16000, 0⟩,
    ⟨169200, 74000, 12800, 0⟩,
    ⟨162792, 73416, 19152, 640⟩,
    ⟨162393, 77007, 15960, 640⟩,
    ⟨168777, 73815, 12768, 640⟩]
  profileDen := 256000
  pi := [99795920, 202936522, 243115571, 527893811]
  slope := [293128502, -40151064, -270931644]
  radiusNum := 1
  radiusDen := 8
}

set_option maxRecDepth 40000
set_option maxHeartbeats 0

theorem f2Archived56_data_ok : dataOK f2Archived56 = true := by decide +kernel

def f2Archived56Chart0 : RowTree :=
  (.splitA
    (.splitB
      (.splitB
        (.splitA
          (.splitA
            (.splitB
              (.splitB
                (.splitA
                  (.splitB
                    (.splitA
                      (.splitB
                        (.splitA
                          (.box 128 127)
                          (.box 124 127)
                        )
                        (.splitA
                          (.box 127 123)
                          (.box 124 123)
                        )
                      )
                      (.box 120 125)
                    )
                    (.splitA
                      (.splitB
                        (.box 126 120)
                        (.splitA
                          (.box 127 116)
                          (.box 124 116)
                        )
                      )
                      (.box 120 117)
                    )
                  )
                  (.box 111 121)
                )
                (.splitA
                  (.splitB
                    (.splitA
                      (.splitA
                        (.box 127 111)
                        (.box 124 111)
                      )
                      (.box 120 111)
                    )
                    (.splitA
                      (.box 125 103)
                      (.box 120 103)
                    )
                  )
                  (.box 111 105)
                )
              )
              (.splitB
                (.splitA
                  (.splitA
                    (.box 125 92)
                    (.box 119 92)
                  )
                  (.box 108 92)
                )
                (.splitA
                  (.box 121 76)
                  (.box 108 76)
                )
              )
            )
            (.splitB
              (.box 92 113)
              (.box 92 81)
            )
          )
          (.splitB
            (.box 65 113)
            (.box 161 81)
          )
        )
        (.splitA
          (.splitB
            (.splitA
              (.splitA
                (.box 121 177)
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
          (.splitB
            (.splitA
              (.box 161 161)
              (.box 193 161)
            )
            (.splitA
              (.splitB
                (.box 161 225)
                (.splitA
                  (.box 177 257)
                  (.box 145 257)
                )
              )
              (.box 129 258)
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
          (.box 97 75)
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
            (.box 256 193)
          )
          (.box 129 97)
        )
      )
    )
    (.splitB
      (.splitB
        (.box 0 97)
        (.splitA
          (.box 0 129)
          (.box 97 129)
        )
      )
      (.splitB
        (.box 0 193)
        (.box 0 75)
      )
    )
  )

theorem f2Archived56Chart0_ok : checkChart f2Archived56 0 1 2 f2Archived56Chart0 = true := by decide +kernel

def f2Archived56Chart1 : RowTree :=
  (.splitA
    (.splitB
      (.splitA
        (.splitB
          (.box 97 75)
          (.splitA
            (.box 113 193)
            (.splitB
              (.box 81 161)
              (.box 81 257)
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
            (.box 225 193)
          )
        )
      )
      (.splitB
        (.splitA
          (.splitB
            (.splitA
              (.box 113 194)
              (.splitB
                (.box 81 257)
                (.box 81 225)
              )
            )
            (.splitA
              (.splitA
                (.box 120 176)
                (.splitB
                  (.box 105 145)
                  (.box 105 177)
                )
              )
              (.splitB
                (.box 81 145)
                (.box 81 185)
              )
            )
          )
          (.splitB
            (.splitA
              (.splitB
                (.box 161 257)
                (.box 161 225)
              )
              (.box 193 257)
            )
            (.box 161 161)
          )
        )
        (.splitA
          (.splitA
            (.splitB
              (.splitA
                (.splitB
                  (.box 121 76)
                  (.splitA
                    (.box 125 92)
                    (.box 117 92)
                  )
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
                      (.box 125 103)
                      (.splitA
                        (.box 127 111)
                        (.box 124 111)
                      )
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
                          (.box 127 116)
                          (.box 124 116)
                        )
                        (.splitA
                          (.box 127 120)
                          (.box 124 120)
                        )
                      )
                      (.splitA
                        (.splitB
                          (.box 127 123)
                          (.box 127 127)
                        )
                        (.box 124 125)
                      )
                    )
                    (.splitB
                      (.box 119 118)
                      (.splitA
                        (.box 120 125)
                        (.box 119 125)
                      )
                    )
                  )
                )
                (.splitB
                  (.box 110 105)
                  (.box 111 120)
                )
              )
            )
            (.splitB
              (.splitB
                (.box 87 76)
                (.box 92 89)
              )
              (.box 92 113)
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
      (.splitB
        (.box 129 97)
        (.splitA
          (.box 0 129)
          (.box 97 129)
        )
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

theorem f2Archived56Chart1_ok : checkChart f2Archived56 1 0 2 f2Archived56Chart1 = true := by decide +kernel

def f2Archived56Chart2 : RowTree :=
  (.splitA
    (.splitB
      (.splitA
        (.box 81 129)
        (.splitB
          (.box 0 65)
          (.splitA
            (.box 161 0)
            (.splitB
              (.box 193 161)
              (.box 193 257)
            )
          )
        )
      )
      (.splitA
        (.splitB
          (.splitA
            (.box 105 161)
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
                (.box 115 92)
                (.splitB
                  (.box 102 81)
                  (.splitA
                    (.box 107 95)
                    (.box 101 92)
                  )
                )
              )
              (.splitA
                (.splitB
                  (.splitA
                    (.box 122 110)
                    (.splitB
                      (.box 115 105)
                      (.splitA
                        (.box 118 112)
                        (.box 115 111)
                      )
                    )
                  )
                  (.splitA
                    (.splitB
                      (.splitB
                        (.box 124 117)
                        (.splitA
                          (.box 126 120)
                          (.box 123 120)
                        )
                      )
                      (.splitA
                        (.splitB
                          (.box 127 124)
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
                          (.box 119 120)
                        )
                        (.splitB
                          (.box 116 115)
                          (.box 116 119)
                        )
                      )
                      (.splitA
                        (.box 120 124)
                        (.box 116 123)
                      )
                    )
                  )
                )
                (.splitB
                  (.splitA
                    (.splitB
                      (.box 109 103)
                      (.splitA
                        (.box 111 110)
                        (.box 108 109)
                      )
                    )
                    (.splitB
                      (.box 103 101)
                      (.box 103 109)
                    )
                  )
                  (.splitB
                    (.splitA
                      (.splitB
                        (.box 111 115)
                        (.box 112 117)
                      )
                      (.box 104 114)
                    )
                    (.box 109 122)
                  )
                )
              )
            )
            (.splitB
              (.splitA
                (.splitB
                  (.box 89 76)
                  (.splitA
                    (.box 91 92)
                    (.box 87 89)
                  )
                )
                (.splitB
                  (.box 76 73)
                  (.box 76 89)
                )
              )
              (.splitB
                (.splitA
                  (.splitB
                    (.box 92 101)
                    (.box 95 105)
                  )
                  (.box 79 99)
                )
                (.splitA
                  (.box 95 115)
                  (.box 81 113)
                )
              )
            )
          )
        )
        (.splitB
          (.splitA
            (.splitB
              (.box 161 225)
              (.splitA
                (.splitB
                  (.box 177 145)
                  (.box 177 177)
                )
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
              (.splitB
                (.box 177 73)
                (.box 177 89)
              )
              (.box 161 97)
            )
            (.box 193 81)
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
              (.box 193 257)
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
          (.splitA
            (.splitB
              (.box 193 257)
              (.box 193 161)
            )
            (.box 161 129)
          )
          (.box 0 65)
        )
        (.box 97 129)
      )
    )
  )

theorem f2Archived56Chart2_ok : checkChart f2Archived56 2 0 1 f2Archived56Chart2 = true := by decide +kernel

end HlawkaSchatten.BelowExponent.FacetNumeric
