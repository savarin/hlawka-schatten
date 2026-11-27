/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.FacetNumeric

/-! Archived facet prism certificate data: `F0Prism1Data`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true

@[expose] public section

namespace HlawkaSchatten.BelowExponent.FacetNumeric

def f0Archived1 : Prism := {
  vertices := [⟨48800, 32000, 15200, 0⟩,
    ⟨51600, 34800, 9600, 0⟩,
    ⟨43200, 43200, 9600, 0⟩,
    ⟨48678, 31920, 15162, 240⟩,
    ⟨51471, 34713, 9576, 240⟩,
    ⟨43092, 43092, 9576, 240⟩]
  profileDen := 96000
  pi := [149982431, 172139664, 230771553, 520848176]
  slope := [194071069, 18447140, -244563685]
  radiusNum := 1
  radiusDen := 8
}

set_option maxRecDepth 40000
set_option maxHeartbeats 0

theorem f0Archived1_data_ok : dataOK f0Archived1 = true := by decide +kernel

def f0Archived1Chart0 : RowTree :=
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
                        (.box 128 125)
                        (.box 124 125)
                      )
                      (.splitB
                        (.box 125 120)
                        (.box 125 116)
                      )
                    )
                    (.splitB
                      (.box 120 125)
                      (.box 120 117)
                    )
                  )
                  (.splitA
                    (.splitB
                      (.box 125 111)
                      (.box 123 105)
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
              (.splitA
                (.splitB
                  (.box 121 92)
                  (.box 118 79)
                )
                (.splitB
                  (.box 108 92)
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
            (.splitA
              (.box 113 177)
              (.box 81 177)
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
          (.splitB
            (.box 65 113)
            (.box 161 81)
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
                  (.box 161 257)
                )
                (.splitB
                  (.box 145 225)
                  (.splitB
                    (.splitA
                      (.box 153 289)
                      (.box 137 289)
                    )
                    (.splitA
                      (.box 153 321)
                      (.splitB
                        (.splitA
                          (.box 141 353)
                          (.box 133 353)
                        )
                        (.splitA
                          (.box 141 385)
                          (.box 133 385)
                        )
                      )
                    )
                  )
                )
              )
              (.splitB
                (.box 225 225)
                (.splitA
                  (.splitA
                    (.splitB
                      (.box 241 289)
                      (.splitB
                        (.box 249 353)
                        (.box 249 385)
                      )
                    )
                    (.box 225 321)
                  )
                  (.box 257 321)
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
            (.box 65 193)
          )
          (.box 75 65)
        )
        (.splitB
          (.splitA
            (.splitB
              (.splitA
                (.box 177 0)
                (.box 138 0)
              )
              (.box 161 161)
            )
            (.splitB
              (.splitA
                (.box 241 0)
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
        (.box 0 75)
        (.box 0 193)
      )
      (.splitB
        (.box 0 193)
        (.box 0 65)
      )
    )
  )

theorem f0Archived1Chart0_ok : checkChart f0Archived1 0 1 2 f0Archived1Chart0 = true := by decide +kernel

def f0Archived1Chart1 : RowTree :=
  (.splitA
    (.splitB
      (.splitA
        (.splitB
          (.box 84 65)
          (.splitA
            (.box 113 129)
            (.box 65 193)
          )
        )
        (.splitB
          (.box 129 97)
          (.splitA
            (.splitB
              (.box 161 161)
              (.box 145 0)
            )
            (.splitB
              (.box 193 161)
              (.box 225 0)
            )
          )
        )
      )
      (.splitA
        (.splitB
          (.splitB
            (.splitA
              (.box 113 193)
              (.box 74 193)
            )
            (.splitA
              (.box 113 177)
              (.box 81 177)
            )
          )
          (.splitA
            (.splitB
              (.splitA
                (.splitB
                  (.box 118 81)
                  (.box 121 92)
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
                      (.box 123 105)
                      (.box 125 111)
                    )
                    (.splitB
                      (.box 119 104)
                      (.box 119 111)
                    )
                  )
                  (.splitA
                    (.splitB
                      (.splitB
                        (.box 125 116)
                        (.box 125 120)
                      )
                      (.splitA
                        (.box 128 125)
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
        )
        (.splitB
          (.splitB
            (.splitA
              (.splitA
                (.box 185 257)
                (.box 145 257)
              )
              (.box 225 257)
            )
            (.splitA
              (.box 161 161)
              (.box 193 161)
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

theorem f0Archived1Chart1_ok : checkChart f0Archived1 1 0 2 f0Archived1Chart1 = true := by decide +kernel

def f0Archived1Chart2 : RowTree :=
  (.splitA
    (.splitB
      (.splitA
        (.box 97 129)
        (.splitB
          (.box 0 65)
          (.splitA
            (.box 161 129)
            (.box 193 193)
          )
        )
      )
      (.splitA
        (.splitB
          (.splitA
            (.box 113 161)
            (.splitB
              (.box 81 193)
              (.box 81 177)
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
                    (.box 122 111)
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
                        (.box 128 125)
                        (.box 123 125)
                      )
                    )
                    (.splitB
                      (.splitA
                        (.splitB
                          (.box 119 116)
                          (.box 120 119)
                        )
                        (.box 117 117)
                      )
                      (.splitA
                        (.box 120 125)
                        (.box 117 123)
                      )
                    )
                  )
                )
                (.splitB
                  (.splitA
                    (.splitB
                      (.box 109 104)
                      (.box 111 111)
                    )
                    (.splitB
                      (.box 103 103)
                      (.box 104 109)
                    )
                  )
                  (.splitB
                    (.splitA
                      (.box 111 117)
                      (.box 105 115)
                    )
                    (.box 108 123)
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
                  (.box 76 76)
                  (.box 79 89)
                )
              )
              (.splitB
                (.splitA
                  (.box 92 105)
                  (.box 81 102)
                )
                (.box 92 115)
              )
            )
          )
        )
        (.splitB
          (.splitB
            (.splitA
              (.box 161 193)
              (.box 193 193)
            )
            (.splitA
              (.box 161 177)
              (.box 193 161)
            )
          )
          (.splitB
            (.splitA
              (.box 177 81)
              (.box 193 81)
            )
            (.box 161 105)
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
            (.box 0 194)
            (.box 161 129)
          )
          (.box 65 0)
        )
        (.box 129 97)
      )
    )
  )

theorem f0Archived1Chart2_ok : checkChart f0Archived1 2 0 1 f0Archived1Chart2 = true := by decide +kernel

end HlawkaSchatten.BelowExponent.FacetNumeric
