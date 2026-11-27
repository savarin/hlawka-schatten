/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.FacetNumeric

/-! Archived facet prism certificate data: `F1Prism11Data`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true

@[expose] public section

namespace HlawkaSchatten.BelowExponent.FacetNumeric

def f1Archived11 : Prism := {
  vertices := [⟨69600, 47200, 11200, 0⟩,
    ⟨57600, 57600, 12800, 0⟩,
    ⟨64400, 53200, 10400, 0⟩,
    ⟨69426, 47082, 11172, 320⟩,
    ⟨57456, 57456, 12768, 320⟩,
    ⟨64239, 53067, 10374, 320⟩]
  profileDen := 128000
  pi := [147454681, 178723538, 225605989, 521957616]
  slope := [196697240, 51898150, -278421988]
  radiusNum := 1
  radiusDen := 8
}

set_option maxRecDepth 40000
set_option maxHeartbeats 0

theorem f1Archived11_data_ok : dataOK f1Archived11 = true := by decide +kernel

def f1Archived11Chart0 : RowTree :=
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
              (.splitA
                (.splitB
                  (.box 121 92)
                  (.box 121 79)
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
                  (.splitB
                    (.box 177 289)
                    (.box 177 321)
                  )
                )
                (.splitB
                  (.box 145 225)
                  (.splitA
                    (.splitB
                      (.box 153 289)
                      (.box 145 321)
                    )
                    (.splitB
                      (.box 137 289)
                      (.splitB
                        (.box 137 337)
                        (.splitA
                          (.box 141 417)
                          (.box 133 417)
                        )
                      )
                    )
                  )
                )
              )
              (.splitB
                (.box 225 225)
                (.splitA
                  (.splitB
                    (.box 241 289)
                    (.splitB
                      (.box 242 337)
                      (.box 242 417)
                    )
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
              (.box 65 0)
              (.box 81 161)
            )
          )
          (.box 84 65)
        )
        (.splitB
          (.splitA
            (.splitB
              (.splitA
                (.box 177 0)
                (.splitA
                  (.box 153 0)
                  (.box 137 0)
                )
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
        (.box 0 84)
        (.box 0 193)
      )
      (.splitB
        (.box 0 193)
        (.box 0 65)
      )
    )
  )

theorem f1Archived11Chart0_ok : checkChart f1Archived11 0 1 2 f1Archived11Chart0 = true := by decide +kernel

def f1Archived11Chart1 : RowTree :=
  (.splitA
    (.splitB
      (.splitA
        (.splitB
          (.box 84 65)
          (.splitA
            (.box 113 193)
            (.box 65 193)
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
                    (.box 153 0)
                    (.box 137 0)
                  )
                )
              )
            )
            (.splitB
              (.box 193 161)
              (.splitA
                (.splitB
                  (.box 225 225)
                  (.splitA
                    (.box 241 0)
                    (.box 209 0)
                  )
                )
                (.box 193 257)
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
                (.box 81 257)
                (.box 81 225)
              )
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
                  (.box 121 79)
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
                  (.box 177 321)
                  (.splitB
                    (.splitA
                      (.box 153 385)
                      (.splitA
                        (.box 141 385)
                        (.box 133 385)
                      )
                    )
                    (.box 145 289)
                  )
                )
                (.box 161 193)
              )
              (.splitA
                (.splitB
                  (.splitB
                    (.splitA
                      (.box 249 385)
                      (.box 209 321)
                    )
                    (.box 225 257)
                  )
                  (.box 225 225)
                )
                (.box 193 257)
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
        (.box 65 97)
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

theorem f1Archived11Chart1_ok : checkChart f1Archived11 1 0 2 f1Archived11Chart1 = true := by decide +kernel

def f1Archived11Chart2 : RowTree :=
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
            (.box 105 161)
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
                        (.splitB
                          (.box 116 116)
                          (.box 116 119)
                        )
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
                      (.box 111 109)
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
                  (.box 76 76)
                  (.box 79 89)
                )
              )
              (.splitB
                (.splitA
                  (.box 92 105)
                  (.box 81 102)
                )
                (.box 92 113)
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
        (.box 97 65)
      )
    )
  )

theorem f1Archived11Chart2_ok : checkChart f1Archived11 2 0 1 f1Archived11Chart2 = true := by decide +kernel

end HlawkaSchatten.BelowExponent.FacetNumeric
