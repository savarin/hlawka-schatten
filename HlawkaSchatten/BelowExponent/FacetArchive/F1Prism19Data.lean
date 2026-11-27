/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.FacetNumeric

/-! Archived facet prism certificate data: `F1Prism19Data`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true

@[expose] public section

namespace HlawkaSchatten.BelowExponent.FacetNumeric

def f1Archived19 : Prism := {
  vertices := [⟨46000, 12400, 5600, 0⟩,
    ⟨40000, 17600, 6400, 0⟩,
    ⟨40800, 18400, 4800, 0⟩,
    ⟨45885, 12369, 5586, 160⟩,
    ⟨39900, 17556, 6384, 160⟩,
    ⟨40698, 18354, 4788, 160⟩]
  profileDen := 64000
  pi := [81282636, 162133088, 303581338, 526744762]
  slope := [297362433, -142198584, -175416154]
  radiusNum := 1
  radiusDen := 8
}

set_option maxRecDepth 40000
set_option maxHeartbeats 0

theorem f1Archived19_data_ok : dataOK f1Archived19 = true := by decide +kernel

def f1Archived19Chart0 : RowTree :=
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
                      (.splitA
                        (.splitB
                          (.box 127 120)
                          (.box 127 116)
                        )
                        (.splitB
                          (.box 124 120)
                          (.box 124 116)
                        )
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
                (.box 92 86)
                (.box 87 76)
              )
            )
          )
          (.splitB
            (.splitA
              (.box 112 177)
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
          (.splitB
            (.box 161 113)
            (.box 161 73)
          )
          (.splitA
            (.splitB
              (.box 161 161)
              (.splitB
                (.box 161 225)
                (.splitA
                  (.box 177 257)
                  (.box 145 257)
                )
              )
            )
            (.splitB
              (.box 193 161)
              (.box 225 193)
            )
          )
        )
      )
      (.splitA
        (.splitB
          (.splitA
            (.box 113 193)
            (.box 73 193)
          )
          (.box 84 65)
        )
        (.splitB
          (.splitA
            (.splitA
              (.splitB
                (.box 177 0)
                (.box 177 161)
              )
              (.splitB
                (.box 145 0)
                (.box 145 161)
              )
            )
            (.box 225 193)
          )
          (.box 129 97)
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
        (.box 65 97)
      )
    )
  )

theorem f1Archived19Chart0_ok : checkChart f1Archived19 0 1 2 f1Archived19Chart0 = true := by decide +kernel

def f1Archived19Chart1 : RowTree :=
  (.splitA
    (.splitB
      (.splitA
        (.splitB
          (.box 97 65)
          (.splitA
            (.box 113 193)
            (.box 81 193)
          )
        )
        (.splitB
          (.box 129 97)
          (.splitA
            (.box 161 193)
            (.box 193 129)
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
                (.box 105 161)
              )
            )
            (.splitB
              (.box 81 193)
              (.box 89 161)
            )
          )
          (.splitA
            (.splitB
              (.splitA
                (.splitB
                  (.box 121 76)
                  (.splitA
                    (.box 125 92)
                    (.box 119 92)
                  )
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
                      (.splitA
                        (.box 127 111)
                        (.box 124 111)
                      )
                    )
                    (.splitB
                      (.box 119 104)
                      (.box 119 111)
                    )
                  )
                  (.splitA
                    (.splitB
                      (.splitA
                        (.splitB
                          (.box 127 116)
                          (.box 127 120)
                        )
                        (.splitB
                          (.box 124 116)
                          (.box 124 120)
                        )
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
                      (.box 119 118)
                      (.splitA
                        (.box 121 125)
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
                  (.box 109 121)
                )
              )
            )
            (.splitB
              (.splitB
                (.box 87 76)
                (.box 87 92)
              )
              (.splitA
                (.box 97 113)
                (.box 81 113)
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
            (.box 161 161)
          )
          (.splitA
            (.box 65 97)
            (.box 193 97)
          )
        )
      )
    )
    (.splitB
      (.box 129 129)
      (.splitB
        (.box 129 129)
        (.box 129 97)
      )
    )
  )

theorem f1Archived19Chart1_ok : checkChart f1Archived19 1 0 2 f1Archived19Chart1 = true := by decide +kernel

def f1Archived19Chart2 : RowTree :=
  (.splitA
    (.splitB
      (.splitA
        (.box 81 129)
        (.splitB
          (.box 0 65)
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
              (.box 113 65)
            )
            (.splitB
              (.box 81 193)
              (.splitA
                (.box 89 177)
                (.box 73 176)
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
                    (.splitB
                      (.box 122 105)
                      (.box 123 112)
                    )
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
                        (.box 124 117)
                        (.splitA
                          (.box 126 120)
                          (.box 123 120)
                        )
                      )
                      (.splitA
                        (.splitB
                          (.box 127 124)
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
                  (.splitB
                    (.splitA
                      (.splitB
                        (.box 111 115)
                        (.box 111 118)
                      )
                      (.box 104 115)
                    )
                    (.splitA
                      (.box 112 122)
                      (.box 105 121)
                    )
                  )
                )
              )
            )
            (.splitB
              (.splitA
                (.splitB
                  (.box 89 76)
                  (.splitB
                    (.box 89 88)
                    (.box 92 91)
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
                    (.box 92 107)
                  )
                  (.box 79 102)
                )
                (.splitA
                  (.box 95 115)
                  (.box 81 113)
                )
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
              (.splitB
                (.box 161 153)
                (.splitA
                  (.box 177 177)
                  (.box 145 177)
                )
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
                (.box 177 73)
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
      (.splitB
        (.splitA
          (.splitA
            (.splitB
              (.box 193 257)
              (.box 193 161)
            )
            (.box 161 129)
          )
          (.box 75 0)
        )
        (.box 129 65)
      )
    )
  )

theorem f1Archived19Chart2_ok : checkChart f1Archived19 2 0 1 f1Archived19Chart2 = true := by decide +kernel

end HlawkaSchatten.BelowExponent.FacetNumeric
