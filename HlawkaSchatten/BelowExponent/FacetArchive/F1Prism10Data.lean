/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.FacetNumeric

/-! Archived facet prism certificate data: `F1Prism10Data`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true

@[expose] public section

namespace HlawkaSchatten.BelowExponent.FacetNumeric

def f1Archived10 : Prism := {
  vertices := [⟨69600, 47200, 11200, 0⟩,
    ⟨64400, 53200, 10400, 0⟩,
    ⟨71200, 48800, 8000, 0⟩,
    ⟨69426, 47082, 11172, 320⟩,
    ⟨64239, 53067, 10374, 320⟩,
    ⟨71022, 48678, 7980, 320⟩]
  profileDen := 128000
  pi := [141541140, 189383228, 218804166, 524013290]
  slope := [209600358, 60561922, -295877530]
  radiusNum := 1
  radiusDen := 8
}

set_option maxRecDepth 40000
set_option maxHeartbeats 0

theorem f1Archived10_data_ok : dataOK f1Archived10 = true := by decide +kernel

def f1Archived10Chart0 : RowTree :=
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
                      (.box 125 103)
                      (.box 119 103)
                    )
                  )
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
                (.box 121 161)
                (.box 105 161)
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
                  (.splitB
                    (.splitA
                      (.box 153 257)
                      (.box 137 257)
                    )
                    (.splitA
                      (.splitB
                        (.box 149 336)
                        (.box 150 417)
                      )
                      (.splitB
                        (.box 141 337)
                        (.box 141 417)
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
                    (.box 241 321)
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
              (.box 72 0)
              (.box 81 161)
            )
          )
          (.box 84 75)
        )
        (.splitB
          (.splitA
            (.splitB
              (.splitA
                (.box 169 0)
                (.splitB
                  (.box 145 0)
                  (.box 145 225)
                )
              )
              (.box 161 161)
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
        (.box 0 193)
      )
      (.splitB
        (.box 0 193)
        (.box 0 65)
      )
    )
  )

theorem f1Archived10Chart0_ok : checkChart f1Archived10 0 1 2 f1Archived10Chart0 = true := by decide +kernel

def f1Archived10Chart1 : RowTree :=
  (.splitA
    (.splitB
      (.splitA
        (.splitB
          (.box 97 75)
          (.splitA
            (.box 113 193)
            (.splitB
              (.box 81 161)
              (.box 70 0)
            )
          )
        )
        (.splitB
          (.box 129 97)
          (.splitA
            (.splitB
              (.box 161 161)
              (.splitA
                (.splitB
                  (.box 177 225)
                  (.box 177 0)
                )
                (.splitB
                  (.box 145 225)
                  (.splitA
                    (.box 145 0)
                    (.splitB
                      (.box 137 289)
                      (.box 137 0)
                    )
                  )
                )
              )
            )
            (.splitB
              (.box 193 161)
              (.splitA
                (.splitB
                  (.box 225 225)
                  (.splitB
                    (.box 225 289)
                    (.box 241 0)
                  )
                )
                (.box 257 257)
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
              (.splitB
                (.box 81 321)
                (.box 81 225)
              )
            )
            (.splitA
              (.splitA
                (.box 121 161)
                (.box 105 161)
              )
              (.box 89 161)
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
                      (.box 125 104)
                      (.box 125 111)
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
                          (.box 128 125)
                          (.box 128 126)
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
        )
        (.splitB
          (.splitB
            (.splitA
              (.splitB
                (.splitA
                  (.box 161 321)
                  (.splitA
                    (.splitB
                      (.splitB
                        (.box 149 385)
                        (.box 153 353)
                      )
                      (.box 153 289)
                    )
                    (.splitA
                      (.splitB
                        (.splitB
                          (.box 141 449)
                          (.box 141 353)
                        )
                        (.box 141 289)
                      )
                      (.splitB
                        (.splitB
                          (.box 133 449)
                          (.box 133 353)
                        )
                        (.box 133 289)
                      )
                    )
                  )
                )
                (.box 161 225)
              )
              (.splitA
                (.splitB
                  (.splitB
                    (.splitA
                      (.box 129 385)
                      (.box 209 321)
                    )
                    (.box 225 289)
                  )
                  (.box 225 225)
                )
                (.box 257 257)
              )
            )
            (.splitA
              (.box 161 161)
              (.box 193 161)
            )
          )
          (.splitB
            (.box 161 81)
            (.box 65 113)
          )
        )
      )
    )
    (.splitB
      (.splitB
        (.box 65 65)
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
        (.box 0 84)
      )
    )
  )

theorem f1Archived10Chart1_ok : checkChart f1Archived10 1 0 2 f1Archived10Chart1 = true := by decide +kernel

def f1Archived10Chart2 : RowTree :=
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
                (.box 89 161)
                (.box 73 161)
              )
            )
          )
          (.splitA
            (.splitB
              (.splitA
                (.box 115 92)
                (.splitB
                  (.box 102 81)
                  (.box 105 92)
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
                          (.box 116 116)
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
                      (.box 111 109)
                    )
                    (.splitB
                      (.box 103 101)
                      (.box 103 109)
                    )
                  )
                  (.splitB
                    (.splitA
                      (.box 111 117)
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
                  (.box 89 79)
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
              (.box 161 193)
              (.splitA
                (.box 177 161)
                (.box 145 161)
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
              (.box 177 81)
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
        (.box 65 65)
      )
      (.splitA
        (.splitB
          (.splitA
            (.box 0 193)
            (.box 161 129)
          )
          (.box 0 75)
        )
        (.box 97 129)
      )
    )
  )

theorem f1Archived10Chart2_ok : checkChart f1Archived10 2 0 1 f1Archived10Chart2 = true := by decide +kernel

end HlawkaSchatten.BelowExponent.FacetNumeric
