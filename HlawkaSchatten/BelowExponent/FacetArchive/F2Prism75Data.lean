/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.FacetNumeric

/-! Archived facet prism certificate data: `F2Prism75Data`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true

@[expose] public section

namespace HlawkaSchatten.BelowExponent.FacetNumeric

def f2Archived75 : Prism := {
  vertices := [⟨142400, 97600, 16000, 0⟩,
    ⟨137200, 103600, 15200, 0⟩,
    ⟨138800, 102800, 14400, 0⟩,
    ⟨142044, 97356, 15960, 640⟩,
    ⟨136857, 103341, 15162, 640⟩,
    ⟨138453, 102543, 14364, 640⟩]
  profileDen := 256000
  pi := [139217226, 180023898, 229095546, 525405154]
  slope := [198406209, 67090789, -288428517]
  radiusNum := 1
  radiusDen := 8
}

set_option maxRecDepth 40000
set_option maxHeartbeats 0

theorem f2Archived75_data_ok : dataOK f2Archived75 = true := by decide +kernel

def f2Archived75Chart0 : RowTree :=
  (.splitA
    (.splitB
      (.splitB
        (.splitA
          (.splitA
            (.splitB
              (.splitA
                (.splitB
                  (.splitB
                    (.splitA
                      (.splitA
                        (.splitB
                          (.box 128 127)
                          (.box 127 124)
                        )
                        (.box 124 125)
                      )
                      (.box 120 125)
                    )
                    (.splitA
                      (.splitB
                        (.box 125 120)
                        (.splitA
                          (.box 127 116)
                          (.box 124 116)
                        )
                      )
                      (.box 120 117)
                    )
                  )
                  (.splitA
                    (.splitB
                      (.box 125 111)
                      (.box 125 103)
                    )
                    (.splitB
                      (.box 119 111)
                      (.box 119 103)
                    )
                  )
                )
                (.splitB
                  (.box 111 121)
                  (.box 111 105)
                )
              )
              (.splitB
                (.splitA
                  (.box 121 92)
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
              (.box 88 161)
            )
            (.splitA
              (.box 113 193)
              (.splitB
                (.box 81 225)
                (.box 73 257)
              )
            )
          )
          (.splitB
            (.splitA
              (.box 161 161)
              (.box 193 161)
            )
            (.splitA
              (.splitA
                (.splitB
                  (.box 177 225)
                  (.splitB
                    (.box 177 257)
                    (.box 169 321)
                  )
                )
                (.splitB
                  (.box 145 225)
                  (.splitA
                    (.splitB
                      (.box 153 289)
                      (.splitB
                        (.box 153 353)
                        (.box 153 385)
                      )
                    )
                    (.splitB
                      (.box 137 289)
                      (.box 141 321)
                    )
                  )
                )
              )
              (.splitB
                (.box 129 225)
                (.splitA
                  (.box 129 321)
                  (.box 257 257)
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
            (.splitB
              (.box 73 257)
              (.box 81 161)
            )
          )
          (.box 97 75)
        )
        (.splitB
          (.splitA
            (.splitA
              (.splitB
                (.splitB
                  (.box 177 0)
                  (.box 177 225)
                )
                (.box 177 161)
              )
              (.splitB
                (.splitB
                  (.splitA
                    (.box 153 0)
                    (.box 137 0)
                  )
                  (.box 145 225)
                )
                (.box 145 161)
              )
            )
            (.splitB
              (.splitA
                (.box 129 0)
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
        (.box 0 84)
        (.box 0 129)
      )
      (.splitB
        (.box 0 129)
        (.box 0 65)
      )
    )
  )

theorem f2Archived75Chart0_ok : checkChart f2Archived75 0 1 2 f2Archived75Chart0 = true := by decide +kernel

def f2Archived75Chart1 : RowTree :=
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
            (.splitA
              (.splitB
                (.box 177 161)
                (.box 177 257)
              )
              (.splitB
                (.box 145 161)
                (.box 145 257)
              )
            )
            (.splitB
              (.box 193 161)
              (.box 129 257)
            )
          )
        )
      )
      (.splitB
        (.splitA
          (.splitB
            (.splitA
              (.box 113 193)
              (.splitB
                (.box 81 257)
                (.box 81 225)
              )
            )
            (.splitA
              (.splitA
                (.box 121 177)
                (.box 105 177)
              )
              (.box 89 161)
            )
          )
          (.splitB
            (.splitA
              (.splitA
                (.box 185 257)
                (.box 145 257)
              )
              (.box 129 257)
            )
            (.box 161 145)
          )
        )
        (.splitA
          (.splitA
            (.splitB
              (.splitB
                (.splitA
                  (.box 121 76)
                  (.box 108 76)
                )
                (.splitA
                  (.splitA
                    (.box 125 92)
                    (.box 119 92)
                  )
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
                        (.box 125 120)
                      )
                      (.splitA
                        (.splitB
                          (.box 127 124)
                          (.box 128 127)
                        )
                        (.box 124 125)
                      )
                    )
                    (.splitB
                      (.box 120 117)
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
      (.splitB
        (.box 65 97)
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
        (.box 0 84)
      )
    )
  )

theorem f2Archived75Chart1_ok : checkChart f2Archived75 1 0 2 f2Archived75Chart1 = true := by decide +kernel

def f2Archived75Chart2 : RowTree :=
  (.splitA
    (.splitB
      (.splitA
        (.box 97 129)
        (.splitB
          (.box 0 65)
          (.splitA
            (.box 161 0)
            (.box 193 193)
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
                (.box 89 65)
                (.box 73 177)
              )
            )
          )
          (.splitA
            (.splitB
              (.splitA
                (.box 115 92)
                (.splitB
                  (.box 99 81)
                  (.splitA
                    (.box 107 95)
                    (.box 101 92)
                  )
                )
              )
              (.splitA
                (.splitB
                  (.splitA
                    (.box 122 111)
                    (.splitB
                      (.box 114 105)
                      (.splitA
                        (.box 118 112)
                        (.box 115 111)
                      )
                    )
                  )
                  (.splitA
                    (.splitB
                      (.splitB
                        (.box 123 117)
                        (.box 125 120)
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
                          (.box 119 120)
                        )
                        (.splitB
                          (.box 116 115)
                          (.box 116 119)
                        )
                      )
                      (.splitA
                        (.box 121 123)
                        (.box 117 123)
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
                  (.splitB
                    (.splitA
                      (.splitB
                        (.box 111 115)
                        (.box 112 118)
                      )
                      (.box 105 114)
                    )
                    (.box 108 122)
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
              (.splitB
                (.splitA
                  (.splitB
                    (.box 92 101)
                    (.box 95 107)
                  )
                  (.box 81 99)
                )
                (.box 92 113)
              )
            )
          )
        )
        (.splitB
          (.splitA
            (.splitB
              (.box 161 225)
              (.splitB
                (.box 161 145)
                (.box 177 169)
              )
            )
            (.splitB
              (.splitB
                (.box 193 257)
                (.box 193 225)
              )
              (.box 193 160)
            )
          )
          (.splitB
            (.splitA
              (.splitB
                (.box 177 73)
                (.box 161 84)
              )
              (.box 193 81)
            )
            (.box 161 97)
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
          (.splitB
            (.box 193 193)
            (.box 129 145)
          )
          (.box 0 75)
        )
        (.box 97 129)
      )
    )
  )

theorem f2Archived75Chart2_ok : checkChart f2Archived75 2 0 1 f2Archived75Chart2 = true := by decide +kernel

end HlawkaSchatten.BelowExponent.FacetNumeric
