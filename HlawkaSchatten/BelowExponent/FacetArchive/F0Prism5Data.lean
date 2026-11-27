/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.FacetNumeric

/-! Archived facet prism certificate data: `F0Prism5Data`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true

@[expose] public section

namespace HlawkaSchatten.BelowExponent.FacetNumeric

def f0Archived5 : Prism := {
  vertices := [⟨142400, 24800, 24800, 0⟩,
    ⟨145200, 27600, 19200, 0⟩,
    ⟨136800, 36000, 19200, 0⟩,
    ⟨142044, 24738, 24738, 480⟩,
    ⟨144837, 27531, 19152, 480⟩,
    ⟨136458, 35910, 19152, 480⟩]
  profileDen := 192000
  pi := [79616291, 225450611, 245362430, 523312492]
  slope := [369813526, -183180071, -213750300]
  radiusNum := 1
  radiusDen := 8
}

set_option maxRecDepth 40000
set_option maxHeartbeats 0

theorem f0Archived5_data_ok : dataOK f0Archived5 = true := by decide +kernel

def f0Archived5Chart0 : RowTree :=
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
                        (.box 127 125)
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
                        (.box 117 125)
                      )
                      (.splitB
                        (.box 119 120)
                        (.box 119 116)
                      )
                    )
                  )
                  (.splitA
                    (.splitB
                      (.box 125 112)
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
                    (.box 108 125)
                    (.box 108 117)
                  )
                  (.splitB
                    (.box 108 111)
                    (.box 108 103)
                  )
                )
              )
              (.splitA
                (.splitB
                  (.box 121 92)
                  (.box 118 81)
                )
                (.splitB
                  (.box 108 92)
                  (.box 105 79)
                )
              )
            )
            (.splitB
              (.splitB
                (.box 87 121)
                (.box 87 105)
              )
              (.splitB
                (.box 87 89)
                (.box 87 73)
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
              (.box 73 193)
            )
          )
        )
        (.splitB
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
          (.splitB
            (.splitA
              (.splitA
                (.box 161 160)
                (.box 145 144)
              )
              (.splitA
                (.splitB
                  (.box 225 177)
                  (.box 225 129)
                )
                (.box 257 145)
              )
            )
            (.splitA
              (.splitB
                (.splitA
                  (.box 177 225)
                  (.splitB
                    (.box 137 241)
                    (.splitA
                      (.box 153 209)
                      (.splitB
                        (.box 137 217)
                        (.box 133 201)
                      )
                    )
                  )
                )
                (.splitA
                  (.box 177 257)
                  (.splitB
                    (.splitA
                      (.box 153 289)
                      (.box 133 305)
                    )
                    (.box 145 257)
                  )
                )
              )
              (.splitB
                (.splitA
                  (.splitA
                    (.splitB
                      (.box 241 241)
                      (.splitB
                        (.box 241 217)
                        (.splitA
                          (.box 249 201)
                          (.box 233 201)
                        )
                      )
                    )
                    (.splitB
                      (.box 209 241)
                      (.box 225 202)
                    )
                  )
                  (.box 193 225)
                )
                (.splitA
                  (.splitA
                    (.splitB
                      (.splitA
                        (.box 249 305)
                        (.box 233 305)
                      )
                      (.box 241 321)
                    )
                    (.splitB
                      (.box 225 305)
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
          (.box 81 193)
          (.box 84 65)
        )
        (.splitB
          (.splitA
            (.splitB
              (.box 161 0)
              (.box 161 161)
            )
            (.splitB
              (.splitA
                (.box 225 0)
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
        (.splitA
          (.box 0 81)
          (.box 97 97)
        )
        (.splitB
          (.splitA
            (.box 193 161)
            (.box 97 161)
          )
          (.splitA
            (.splitA
              (.box 0 193)
              (.box 161 193)
            )
            (.box 97 193)
          )
        )
      )
      (.splitB
        (.splitA
          (.splitA
            (.box 0 193)
            (.box 161 129)
          )
          (.box 97 129)
        )
        (.box 65 97)
      )
    )
  )

theorem f0Archived5Chart0_ok : checkChart f0Archived5 0 1 2 f0Archived5Chart0 = true := by decide +kernel

def f0Archived5Chart1 : RowTree :=
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
            (.box 193 193)
          )
        )
      )
      (.splitA
        (.splitB
          (.splitB
            (.splitA
              (.box 113 193)
              (.box 81 193)
            )
            (.splitA
              (.splitA
                (.box 121 161)
                (.box 105 161)
              )
              (.splitA
                (.box 89 161)
                (.box 73 161)
              )
            )
          )
          (.splitA
            (.splitB
              (.splitA
                (.splitB
                  (.box 118 79)
                  (.box 121 92)
                )
                (.splitB
                  (.box 105 79)
                  (.splitA
                    (.box 111 92)
                    (.box 103 92)
                  )
                )
              )
              (.splitA
                (.splitB
                  (.splitA
                    (.splitB
                      (.box 123 105)
                      (.box 125 111)
                    )
                    (.splitB
                      (.box 117 104)
                      (.box 117 111)
                    )
                  )
                  (.splitA
                    (.splitB
                      (.splitB
                        (.splitA
                          (.box 126 117)
                          (.box 123 116)
                        )
                        (.box 125 120)
                      )
                      (.splitA
                        (.box 127 125)
                        (.box 124 125)
                      )
                    )
                    (.splitB
                      (.splitB
                        (.splitA
                          (.box 120 116)
                          (.box 116 116)
                        )
                        (.splitA
                          (.box 120 120)
                          (.box 116 119)
                        )
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
                      (.box 109 117)
                      (.box 108 117)
                    )
                    (.box 108 124)
                  )
                )
              )
            )
            (.splitB
              (.splitB
                (.splitA
                  (.box 92 76)
                  (.box 76 76)
                )
                (.splitA
                  (.box 92 92)
                  (.box 79 89)
                )
              )
              (.splitB
                (.splitA
                  (.box 92 105)
                  (.box 81 102)
                )
                (.box 87 119)
              )
            )
          )
        )
        (.splitB
          (.splitA
            (.splitB
              (.box 161 193)
              (.box 161 161)
            )
            (.splitB
              (.box 193 193)
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
        (.box 193 129)
        (.box 97 65)
      )
      (.splitB
        (.splitA
          (.box 193 129)
          (.box 65 0)
        )
        (.box 129 97)
      )
    )
  )

theorem f0Archived5Chart1_ok : checkChart f0Archived5 1 0 2 f0Archived5Chart1 = true := by decide +kernel

def f0Archived5Chart2 : RowTree :=
  (.splitA
    (.splitB
      (.splitA
        (.splitB
          (.box 97 97)
          (.box 97 193)
        )
        (.splitB
          (.box 129 97)
          (.splitA
            (.box 161 193)
            (.box 193 193)
          )
        )
      )
      (.splitA
        (.splitB
          (.splitB
            (.splitA
              (.box 113 193)
              (.box 81 193)
            )
            (.splitA
              (.box 113 177)
              (.splitA
                (.box 89 161)
                (.box 73 161)
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
                  (.box 105 79)
                  (.box 105 92)
                )
              )
              (.splitA
                (.splitB
                  (.splitA
                    (.splitB
                      (.box 123 105)
                      (.box 125 112)
                    )
                    (.splitB
                      (.box 117 104)
                      (.box 117 111)
                    )
                  )
                  (.splitA
                    (.splitB
                      (.splitB
                        (.splitA
                          (.box 126 117)
                          (.box 123 116)
                        )
                        (.box 125 120)
                      )
                      (.splitA
                        (.box 127 125)
                        (.box 123 125)
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
                        (.box 117 124)
                      )
                    )
                  )
                )
                (.splitB
                  (.splitA
                    (.splitB
                      (.box 109 104)
                      (.box 111 109)
                    )
                    (.box 104 105)
                  )
                  (.splitA
                    (.splitB
                      (.box 111 117)
                      (.box 112 123)
                    )
                    (.box 105 118)
                  )
                )
              )
            )
            (.splitB
              (.splitA
                (.splitB
                  (.box 89 79)
                  (.box 92 89)
                )
                (.box 79 81)
              )
              (.splitA
                (.splitB
                  (.box 92 105)
                  (.box 95 118)
                )
                (.box 81 107)
              )
            )
          )
        )
        (.splitB
          (.splitA
            (.splitB
              (.box 161 193)
              (.box 177 161)
            )
            (.splitB
              (.box 193 193)
              (.box 193 161)
            )
          )
          (.splitA
            (.splitB
              (.box 177 81)
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
          (.box 193 193)
        )
        (.box 97 65)
      )
      (.splitB
        (.splitA
          (.splitA
            (.box 0 193)
            (.box 161 129)
          )
          (.box 75 0)
        )
        (.box 129 97)
      )
    )
  )

theorem f0Archived5Chart2_ok : checkChart f0Archived5 2 0 1 f0Archived5Chart2 = true := by decide +kernel

end HlawkaSchatten.BelowExponent.FacetNumeric
