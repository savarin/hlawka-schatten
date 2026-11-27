/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.FacetNumeric

/-! Archived facet prism certificate data: `F2Prism29Data`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true

@[expose] public section

namespace HlawkaSchatten.BelowExponent.FacetNumeric

def f2Archived29 : Prism := {
  vertices := [⟨204800, 25600, 25600, 0⟩,
    ⟨204000, 32800, 19200, 0⟩,
    ⟨210800, 26000, 19200, 0⟩,
    ⟨204288, 25536, 25536, 640⟩,
    ⟨203490, 32718, 19152, 640⟩,
    ⟨210273, 25935, 19152, 640⟩]
  profileDen := 256000
  pi := [57258519, 240835450, 249110347, 526537508]
  slope := [429259960, -213912820, -236013951]
  radiusNum := 1
  radiusDen := 8
}

set_option maxRecDepth 40000
set_option maxHeartbeats 0

theorem f2Archived29_data_ok : dataOK f2Archived29 = true := by decide +kernel

def f2Archived29Chart0 : RowTree :=
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
                        (.box 124 125)
                      )
                      (.splitB
                        (.box 125 120)
                        (.box 125 116)
                      )
                    )
                    (.splitB
                      (.splitA
                        (.box 120 125)
                        (.box 116 125)
                      )
                      (.splitB
                        (.box 118 120)
                        (.box 119 116)
                      )
                    )
                  )
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
                )
                (.splitB
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
                  (.splitB
                    (.box 108 109)
                    (.box 108 103)
                  )
                )
              )
              (.splitB
                (.splitA
                  (.box 121 92)
                  (.box 108 92)
                )
                (.box 113 76)
              )
            )
            (.splitB
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
        )
        (.splitB
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
                    (.box 153 145)
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
                  (.box 161 225)
                  (.splitB
                    (.splitA
                      (.box 153 241)
                      (.box 133 233)
                    )
                    (.splitA
                      (.box 153 209)
                      (.splitB
                        (.box 133 217)
                        (.box 133 201)
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
                  (.splitA
                    (.splitB
                      (.splitA
                        (.box 249 233)
                        (.box 233 233)
                      )
                      (.splitA
                        (.splitB
                          (.box 249 217)
                          (.box 249 201)
                        )
                        (.splitB
                          (.box 233 217)
                          (.box 233 201)
                        )
                      )
                    )
                    (.splitB
                      (.box 209 233)
                      (.box 217 209)
                    )
                  )
                  (.box 193 225)
                )
                (.splitA
                  (.splitA
                    (.splitB
                      (.box 241 305)
                      (.box 241 321)
                    )
                    (.splitB
                      (.box 209 305)
                      (.box 209 321)
                    )
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
          (.splitA
            (.box 113 193)
            (.box 81 193)
          )
          (.box 84 65)
        )
        (.splitB
          (.splitA
            (.splitB
              (.box 161 0)
              (.box 161 161)
            )
            (.splitB
              (.box 194 0)
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

theorem f2Archived29Chart0_ok : checkChart f2Archived29 0 1 2 f2Archived29Chart0 = true := by decide +kernel

def f2Archived29Chart1 : RowTree :=
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
              (.box 161 193)
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
              (.splitA
                (.box 88 176)
                (.box 73 162)
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
                          (.box 124 123)
                          (.box 124 126)
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
                  (.splitA
                    (.splitB
                      (.box 111 117)
                      (.box 112 123)
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
                (.box 79 81)
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
              (.box 177 161)
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
            (.box 129 97)
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
          (.box 129 97)
          (.box 65 65)
        )
      )
    )
  )

theorem f2Archived29Chart1_ok : checkChart f2Archived29 1 0 2 f2Archived29Chart1 = true := by decide +kernel

def f2Archived29Chart2 : RowTree :=
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
                (.box 72 176)
              )
            )
          )
          (.splitA
            (.splitB
              (.splitA
                (.splitB
                  (.box 118 79)
                  (.splitA
                    (.box 122 95)
                    (.box 117 92)
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
                      (.box 123 104)
                      (.splitA
                        (.box 126 112)
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
                      (.box 110 117)
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
                  (.splitB
                    (.box 92 101)
                    (.box 92 109)
                  )
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
              (.splitB
                (.box 177 73)
                (.box 177 89)
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

theorem f2Archived29Chart2_ok : checkChart f2Archived29 2 0 1 f2Archived29Chart2 = true := by decide +kernel

end HlawkaSchatten.BelowExponent.FacetNumeric
