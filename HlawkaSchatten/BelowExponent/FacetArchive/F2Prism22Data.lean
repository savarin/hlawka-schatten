/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.FacetNumeric

/-! Archived facet prism certificate data: `F2Prism22Data`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true

@[expose] public section

namespace HlawkaSchatten.BelowExponent.FacetNumeric

def f2Archived22 : Prism := {
  vertices := [⟨414000, 66000, 32000, 0⟩,
    ⟨413600, 69600, 28800, 0⟩,
    ⟨420000, 66400, 25600, 0⟩,
    ⟨412965, 65835, 31920, 1280⟩,
    ⟨412566, 69426, 28728, 1280⟩,
    ⟨418950, 66234, 25536, 1280⟩]
  profileDen := 512000
  pi := [53474572, 245144532, 246772526, 528350194]
  slope := [441789691, -185907062, -272924068]
  radiusNum := 1
  radiusDen := 8
}

set_option maxRecDepth 40000
set_option maxHeartbeats 0

theorem f2Archived22_data_ok : dataOK f2Archived22 = true := by decide +kernel

def f2Archived22Chart0 : RowTree :=
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
                        (.splitB
                          (.box 124 127)
                          (.box 124 123)
                        )
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
                        (.box 120 125)
                        (.box 117 125)
                      )
                      (.splitB
                        (.box 119 120)
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
                    (.box 108 125)
                    (.box 108 117)
                  )
                  (.splitB
                    (.box 108 111)
                    (.box 108 103)
                  )
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
              (.splitB
                (.box 87 121)
                (.box 87 105)
              )
              (.splitB
                (.box 87 92)
                (.box 87 73)
              )
            )
          )
          (.splitA
            (.splitB
              (.box 161 113)
              (.box 161 81)
            )
            (.box 225 97)
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
              (.box 225 161)
            )
            (.splitA
              (.splitB
                (.splitA
                  (.box 177 225)
                  (.box 145 225)
                )
                (.box 161 289)
              )
              (.splitB
                (.box 225 225)
                (.box 225 257)
              )
            )
          )
        )
      )
      (.splitA
        (.splitB
          (.splitB
            (.splitA
              (.box 104 0)
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
            (.box 225 193)
          )
          (.box 129 97)
        )
      )
    )
    (.splitB
      (.splitB
        (.box 129 81)
        (.splitB
          (.splitA
            (.box 193 161)
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
          (.box 0 193)
          (.box 97 129)
        )
        (.box 65 97)
      )
    )
  )

theorem f2Archived22Chart0_ok : checkChart f2Archived22 0 1 2 f2Archived22Chart0 = true := by decide +kernel

def f2Archived22Chart1 : RowTree :=
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
              (.splitA
                (.box 121 193)
                (.box 105 193)
              )
              (.splitB
                (.box 81 257)
                (.box 81 225)
              )
            )
            (.splitA
              (.splitA
                (.splitB
                  (.box 121 145)
                  (.box 121 177)
                )
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
                    (.box 104 89)
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
                        (.box 123 110)
                      )
                    )
                    (.splitB
                      (.box 117 103)
                      (.splitA
                        (.box 119 110)
                        (.box 116 109)
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
                          (.box 124 119)
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
                      (.box 111 103)
                      (.box 111 109)
                    )
                    (.box 104 105)
                  )
                  (.splitB
                    (.splitA
                      (.box 111 117)
                      (.box 104 117)
                    )
                    (.splitA
                      (.box 112 123)
                      (.box 105 123)
                    )
                  )
                )
              )
            )
            (.splitB
              (.splitA
                (.splitB
                  (.box 92 73)
                  (.box 92 89)
                )
                (.box 79 81)
              )
              (.splitB
                (.splitA
                  (.box 92 105)
                  (.box 81 102)
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
              (.box 177 81)
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

theorem f2Archived22Chart1_ok : checkChart f2Archived22 1 0 2 f2Archived22Chart1 = true := by decide +kernel

def f2Archived22Chart2 : RowTree :=
  (.splitA
    (.splitB
      (.splitA
        (.splitB
          (.box 75 65)
          (.box 81 193)
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
                  (.box 118 81)
                  (.splitA
                    (.box 122 95)
                    (.box 115 92)
                  )
                )
                (.splitB
                  (.box 105 79)
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
                        (.box 126 112)
                        (.box 122 111)
                      )
                    )
                    (.splitB
                      (.box 117 104)
                      (.splitA
                        (.box 119 111)
                        (.box 115 110)
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
                        (.box 109 115)
                      )
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
                  (.splitA
                    (.box 95 105)
                    (.box 89 102)
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
              (.splitA
                (.box 185 81)
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
          (.box 129 81)
        )
        (.box 97 129)
      )
    )
  )

theorem f2Archived22Chart2_ok : checkChart f2Archived22 2 0 1 f2Archived22Chart2 = true := by decide +kernel

end HlawkaSchatten.BelowExponent.FacetNumeric
