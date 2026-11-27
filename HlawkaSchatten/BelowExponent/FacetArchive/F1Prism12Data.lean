/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.FacetNumeric

/-! Archived facet prism certificate data: `F1Prism12Data`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true

@[expose] public section

namespace HlawkaSchatten.BelowExponent.FacetNumeric

def f1Archived12 : Prism := {
  vertices := [⟨76400, 42800, 8800, 0⟩,
    ⟨69600, 47200, 11200, 0⟩,
    ⟨71200, 48800, 8000, 0⟩,
    ⟨76209, 42693, 8778, 320⟩,
    ⟨69426, 47082, 11172, 320⟩,
    ⟨71022, 48678, 7980, 320⟩]
  profileDen := 128000
  pi := [127226252, 188262041, 232990337, 525263194]
  slope := [218578258, 28949508, -270743207]
  radiusNum := 1
  radiusDen := 8
}

set_option maxRecDepth 40000
set_option maxHeartbeats 0

theorem f1Archived12_data_ok : dataOK f1Archived12 = true := by decide +kernel

def f1Archived12Chart0 : RowTree :=
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
                          (.box 127 127)
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
                      (.box 125 104)
                    )
                    (.splitB
                      (.box 119 111)
                      (.box 119 104)
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
              (.splitB
                (.box 92 89)
                (.box 87 76)
              )
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
                    (.box 169 289)
                    (.splitA
                      (.box 185 321)
                      (.box 161 321)
                    )
                  )
                )
                (.splitB
                  (.box 145 225)
                  (.splitB
                    (.splitA
                      (.box 153 257)
                      (.box 137 257)
                    )
                    (.splitA
                      (.splitB
                        (.splitA
                          (.box 157 353)
                          (.box 149 337)
                        )
                        (.splitA
                          (.box 157 385)
                          (.box 149 321)
                        )
                      )
                      (.splitB
                        (.box 141 337)
                        (.box 141 321)
                      )
                    )
                  )
                )
              )
              (.splitB
                (.box 225 225)
                (.splitB
                  (.splitA
                    (.box 129 289)
                    (.box 257 289)
                  )
                  (.splitA
                    (.box 129 321)
                    (.box 257 321)
                  )
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
          (.box 97 65)
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
        (.box 0 75)
        (.box 0 193)
      )
      (.splitB
        (.box 0 193)
        (.box 0 65)
      )
    )
  )

theorem f1Archived12Chart0_ok : checkChart f1Archived12 0 1 2 f1Archived12Chart0 = true := by decide +kernel

def f1Archived12Chart1 : RowTree :=
  (.splitA
    (.splitB
      (.splitA
        (.splitB
          (.box 84 75)
          (.splitA
            (.box 113 193)
            (.splitB
              (.box 81 161)
              (.box 73 257)
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
              (.box 225 257)
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
                (.box 81 321)
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
                (.splitB
                  (.box 177 257)
                  (.box 177 225)
                )
                (.splitB
                  (.box 145 257)
                  (.box 145 225)
                )
              )
              (.box 225 257)
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
              (.splitB
                (.box 87 76)
                (.box 92 89)
              )
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
        (.box 65 65)
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

theorem f1Archived12Chart1_ok : checkChart f1Archived12 1 0 2 f1Archived12Chart1 = true := by decide +kernel

def f1Archived12Chart2 : RowTree :=
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
                    (.box 122 111)
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
                          (.box 120 119)
                        )
                        (.splitB
                          (.box 116 115)
                          (.box 116 119)
                        )
                      )
                      (.splitA
                        (.box 121 123)
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
                        (.box 111 109)
                        (.box 110 109)
                      )
                    )
                    (.splitB
                      (.box 103 101)
                      (.box 103 109)
                    )
                  )
                  (.splitB
                    (.splitA
                      (.box 111 116)
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
                  (.splitB
                    (.box 89 89)
                    (.box 92 93)
                  )
                )
                (.splitB
                  (.box 76 73)
                  (.box 76 89)
                )
              )
              (.splitB
                (.splitA
                  (.box 92 105)
                  (.box 81 99)
                )
                (.box 87 115)
              )
            )
          )
        )
        (.splitB
          (.splitA
            (.splitB
              (.box 161 193)
              (.splitB
                (.box 161 145)
                (.box 177 177)
              )
            )
            (.splitB
              (.splitB
                (.box 193 257)
                (.box 193 225)
              )
              (.box 193 161)
            )
          )
          (.splitB
            (.splitA
              (.splitB
                (.box 177 73)
                (.box 161 85)
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
          (.splitB
            (.box 129 161)
            (.box 193 193)
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

theorem f1Archived12Chart2_ok : checkChart f1Archived12 2 0 1 f1Archived12Chart2 = true := by decide +kernel

end HlawkaSchatten.BelowExponent.FacetNumeric
