/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.FacetNumeric

/-! Archived facet prism certificate data: `F2Prism79Data`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true

@[expose] public section

namespace HlawkaSchatten.BelowExponent.FacetNumeric

def f2Archived79 : Prism := {
  vertices := [⟨168400, 67600, 20000, 0⟩,
    ⟨163200, 73600, 19200, 0⟩,
    ⟨169600, 70400, 16000, 0⟩,
    ⟨167979, 67431, 19950, 640⟩,
    ⟨162792, 73416, 19152, 640⟩,
    ⟨169176, 70224, 15960, 640⟩]
  profileDen := 256000
  pi := [108020008, 221598984, 219634590, 524488242]
  slope := [304185306, -41002299, -287948353]
  radiusNum := 1
  radiusDen := 8
}

set_option maxRecDepth 40000
set_option maxHeartbeats 0

theorem f2Archived79_data_ok : dataOK f2Archived79 = true := by decide +kernel

def f2Archived79Chart0 : RowTree :=
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
                        (.box 126 127)
                        (.box 125 124)
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
                  (.box 111 121)
                )
                (.splitA
                  (.splitB
                    (.splitA
                      (.box 125 111)
                      (.box 119 111)
                    )
                    (.splitA
                      (.box 125 104)
                      (.box 119 104)
                    )
                  )
                  (.box 111 106)
                )
              )
              (.splitB
                (.splitA
                  (.box 121 92)
                  (.box 108 92)
                )
                (.box 113 79)
              )
            )
            (.splitB
              (.splitB
                (.box 92 121)
                (.box 92 105)
              )
              (.splitB
                (.box 92 89)
                (.box 87 76)
              )
            )
          )
          (.splitB
            (.box 161 113)
            (.box 161 72)
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
                (.box 81 209)
                (.box 65 288)
              )
            )
          )
          (.splitB
            (.splitA
              (.splitA
                (.box 177 161)
                (.box 145 161)
              )
              (.box 193 129)
            )
            (.splitA
              (.splitB
                (.splitA
                  (.box 177 193)
                  (.box 145 194)
                )
                (.splitA
                  (.splitB
                    (.box 169 289)
                    (.box 161 353)
                  )
                  (.splitB
                    (.splitA
                      (.splitB
                        (.box 153 305)
                        (.box 149 273)
                      )
                      (.splitA
                        (.splitB
                          (.box 141 305)
                          (.box 141 273)
                        )
                        (.box 133 273)
                      )
                    )
                    (.splitA
                      (.splitB
                        (.box 149 353)
                        (.box 153 385)
                      )
                      (.splitA
                        (.splitB
                          (.box 141 353)
                          (.box 141 385)
                        )
                        (.box 133 353)
                      )
                    )
                  )
                )
              )
              (.splitB
                (.splitA
                  (.box 225 193)
                  (.box 257 225)
                )
                (.splitA
                  (.splitB
                    (.box 241 273)
                    (.box 241 353)
                  )
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
              (.box 70 0)
              (.box 81 161)
            )
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
        (.box 129 97)
        (.splitA
          (.box 0 193)
          (.box 97 129)
        )
      )
      (.splitB
        (.splitA
          (.box 0 193)
          (.box 97 129)
        )
        (.box 0 65)
      )
    )
  )

theorem f2Archived79Chart0_ok : checkChart f2Archived79 0 1 2 f2Archived79Chart0 = true := by decide +kernel

def f2Archived79Chart1 : RowTree :=
  (.splitA
    (.splitB
      (.splitA
        (.splitB
          (.box 97 75)
          (.splitA
            (.box 113 193)
            (.box 73 193)
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
              (.box 225 257)
            )
          )
        )
      )
      (.splitA
        (.splitB
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
              (.box 88 161)
            )
          )
          (.splitA
            (.splitB
              (.splitB
                (.splitA
                  (.box 121 76)
                  (.box 108 76)
                )
                (.splitA
                  (.box 121 92)
                  (.box 108 92)
                )
              )
              (.splitA
                (.splitB
                  (.splitA
                    (.splitB
                      (.box 125 103)
                      (.splitA
                        (.box 125 111)
                        (.box 125 110)
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
                          (.box 127 127)
                        )
                        (.box 124 125)
                      )
                    )
                    (.splitB
                      (.splitB
                        (.box 119 116)
                        (.box 119 120)
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
                    (.box 111 123)
                  )
                )
              )
            )
            (.splitB
              (.splitB
                (.box 87 76)
                (.box 87 89)
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
              (.splitB
                (.box 161 321)
                (.box 161 225)
              )
              (.box 225 257)
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
        (.box 129 97)
      )
    )
  )

theorem f2Archived79Chart1_ok : checkChart f2Archived79 1 0 2 f2Archived79Chart1 = true := by decide +kernel

def f2Archived79Chart2 : RowTree :=
  (.splitA
    (.splitB
      (.splitA
        (.box 81 129)
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
                      (.box 117 111)
                    )
                  )
                  (.splitA
                    (.splitB
                      (.splitB
                        (.box 124 117)
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
                          (.box 120 119)
                        )
                        (.splitB
                          (.box 116 115)
                          (.box 116 119)
                        )
                      )
                      (.splitA
                        (.box 120 125)
                        (.box 116 123)
                      )
                    )
                  )
                )
                (.splitB
                  (.splitA
                    (.splitB
                      (.box 109 103)
                      (.box 110 110)
                    )
                    (.splitB
                      (.box 103 101)
                      (.box 103 109)
                    )
                  )
                  (.splitB
                    (.splitA
                      (.box 111 116)
                      (.box 104 115)
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
                  (.box 92 89)
                )
                (.splitB
                  (.box 76 73)
                  (.box 76 89)
                )
              )
              (.splitB
                (.splitA
                  (.box 92 105)
                  (.box 79 99)
                )
                (.box 88 115)
              )
            )
          )
        )
        (.splitB
          (.splitA
            (.splitB
              (.box 161 193)
              (.splitA
                (.box 177 161)
                (.box 145 161)
              )
            )
            (.splitB
              (.box 193 194)
              (.box 193 161)
            )
          )
          (.splitB
            (.splitA
              (.box 177 80)
              (.box 193 81)
            )
            (.splitA
              (.box 161 105)
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
            (.box 193 193)
            (.box 161 129)
          )
        )
        (.box 75 65)
      )
      (.splitA
        (.splitB
          (.splitA
            (.box 257 193)
            (.box 161 129)
          )
          (.box 0 75)
        )
        (.box 97 65)
      )
    )
  )

theorem f2Archived79Chart2_ok : checkChart f2Archived79 2 0 1 f2Archived79Chart2 = true := by decide +kernel

end HlawkaSchatten.BelowExponent.FacetNumeric
