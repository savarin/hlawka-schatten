/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.FacetNumeric

/-! Archived facet prism certificate data: `F2Prism37Data`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true

@[expose] public section

namespace HlawkaSchatten.BelowExponent.FacetNumeric

def f2Archived37 : Prism := {
  vertices := [⟨386800, 93200, 32000, 0⟩,
    ⟨386400, 96800, 28800, 0⟩,
    ⟨392800, 93600, 25600, 0⟩,
    ⟨385833, 92967, 31920, 1280⟩,
    ⟨385434, 96558, 28728, 1280⟩,
    ⟨391818, 93366, 25536, 1280⟩]
  profileDen := 512000
  pi := [68880876, 231956827, 245167780, 527736341]
  slope := [391444667, -135901304, -273812512]
  radiusNum := 1
  radiusDen := 8
}

set_option maxRecDepth 40000
set_option maxHeartbeats 0

theorem f2Archived37_data_ok : dataOK f2Archived37 = true := by decide +kernel

def f2Archived37Chart0 : RowTree :=
  (.splitA
    (.splitB
      (.splitB
        (.splitA
          (.splitA
            (.splitB
              (.splitA
                (.splitB
                  (.splitA
                    (.splitB
                      (.splitA
                        (.splitB
                          (.box 127 127)
                          (.box 127 123)
                        )
                        (.box 124 125)
                      )
                      (.splitB
                        (.box 125 120)
                        (.splitA
                          (.box 127 116)
                          (.box 124 116)
                        )
                      )
                    )
                    (.splitB
                      (.splitA
                        (.box 121 125)
                        (.box 117 125)
                      )
                      (.splitB
                        (.box 120 119)
                        (.box 119 116)
                      )
                    )
                  )
                  (.splitB
                    (.splitA
                      (.splitA
                        (.box 126 111)
                        (.box 125 111)
                      )
                      (.box 119 111)
                    )
                    (.splitA
                      (.box 125 103)
                      (.box 119 103)
                    )
                  )
                )
                (.splitB
                  (.splitB
                    (.box 111 125)
                    (.box 111 117)
                  )
                  (.splitB
                    (.box 111 109)
                    (.box 108 103)
                  )
                )
              )
              (.splitB
                (.splitA
                  (.box 122 92)
                  (.box 108 92)
                )
                (.splitA
                  (.box 121 76)
                  (.box 108 76)
                )
              )
            )
            (.splitB
              (.splitB
                (.box 92 121)
                (.box 92 105)
              )
              (.splitB
                (.box 87 92)
                (.box 87 76)
              )
            )
          )
          (.splitB
            (.box 161 113)
            (.splitA
              (.box 161 81)
              (.box 193 81)
            )
          )
        )
        (.splitA
          (.splitB
            (.splitA
              (.splitB
                (.box 113 177)
                (.box 113 145)
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
              (.splitB
                (.box 161 177)
                (.box 161 145)
              )
              (.box 193 145)
            )
            (.splitA
              (.splitB
                (.box 161 225)
                (.splitA
                  (.box 177 257)
                  (.box 145 257)
                )
              )
              (.box 226 193)
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
              (.box 161 257)
              (.box 161 161)
            )
            (.box 226 193)
          )
          (.box 129 97)
        )
      )
    )
    (.splitB
      (.splitB
        (.box 129 97)
        (.splitB
          (.box 129 145)
          (.splitA
            (.box 0 193)
            (.box 97 193)
          )
        )
      )
      (.splitB
        (.splitA
          (.box 0 129)
          (.box 97 129)
        )
        (.box 65 97)
      )
    )
  )

theorem f2Archived37Chart0_ok : checkChart f2Archived37 0 1 2 f2Archived37Chart0 = true := by decide +kernel

def f2Archived37Chart1 : RowTree :=
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
              (.box 106 224)
              (.splitB
                (.box 81 257)
                (.box 81 225)
              )
            )
            (.splitA
              (.splitA
                (.box 118 176)
                (.splitB
                  (.box 105 145)
                  (.box 105 177)
                )
              )
              (.splitB
                (.box 81 145)
                (.box 88 177)
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
                  (.splitB
                    (.box 108 87)
                    (.box 108 93)
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
                        (.box 123 111)
                      )
                    )
                    (.splitB
                      (.box 119 103)
                      (.splitB
                        (.box 119 108)
                        (.box 119 112)
                      )
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
                          (.box 124 119)
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
                      (.splitB
                        (.box 119 115)
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
                    (.box 108 101)
                    (.box 108 109)
                  )
                  (.splitB
                    (.box 108 117)
                    (.box 108 125)
                  )
                )
              )
            )
            (.splitB
              (.splitB
                (.box 87 73)
                (.box 87 89)
              )
              (.splitB
                (.box 87 105)
                (.box 87 121)
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
              (.box 161 161)
            )
            (.splitB
              (.box 193 257)
              (.box 193 161)
            )
          )
          (.splitB
            (.splitA
              (.box 161 81)
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
          (.box 193 129)
        )
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

theorem f2Archived37Chart1_ok : checkChart f2Archived37 1 0 2 f2Archived37Chart1 = true := by decide +kernel

def f2Archived37Chart2 : RowTree :=
  (.splitA
    (.splitB
      (.splitA
        (.box 81 129)
        (.splitA
          (.splitB
            (.box 161 97)
            (.box 161 193)
          )
          (.splitB
            (.box 0 65)
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
            (.splitB
              (.box 113 193)
              (.box 105 65)
            )
            (.splitB
              (.box 81 129)
              (.splitA
                (.box 89 177)
                (.box 70 177)
              )
            )
          )
          (.splitA
            (.splitB
              (.splitA
                (.splitB
                  (.box 115 81)
                  (.box 118 95)
                )
                (.splitB
                  (.box 102 79)
                  (.splitA
                    (.box 107 92)
                    (.box 101 92)
                  )
                )
              )
              (.splitA
                (.splitB
                  (.splitA
                    (.splitB
                      (.box 122 105)
                      (.box 123 112)
                    )
                    (.splitB
                      (.box 115 104)
                      (.splitA
                        (.box 118 111)
                        (.box 115 111)
                      )
                    )
                  )
                  (.splitA
                    (.splitB
                      (.splitB
                        (.splitA
                          (.box 126 117)
                          (.box 122 116)
                        )
                        (.splitA
                          (.box 126 120)
                          (.box 123 120)
                        )
                      )
                      (.splitA
                        (.splitB
                          (.box 126 124)
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
                  (.splitA
                    (.splitB
                      (.splitB
                        (.box 111 113)
                        (.box 111 118)
                      )
                      (.box 112 122)
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
                    (.box 95 89)
                    (.box 87 89)
                  )
                )
                (.splitB
                  (.box 76 73)
                  (.box 76 89)
                )
              )
              (.splitA
                (.splitB
                  (.splitB
                    (.box 92 99)
                    (.box 92 107)
                  )
                  (.box 95 115)
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
                (.box 176 69)
                (.box 177 89)
              )
              (.box 161 105)
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
          (.box 0 75)
        )
        (.box 97 129)
      )
    )
  )

theorem f2Archived37Chart2_ok : checkChart f2Archived37 2 0 1 f2Archived37Chart2 = true := by decide +kernel

end HlawkaSchatten.BelowExponent.FacetNumeric
