/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.FacetNumeric

/-! Archived facet prism certificate data: `F0Prism7Data`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true

@[expose] public section

namespace HlawkaSchatten.BelowExponent.FacetNumeric

def f0Archived7 : Prism := {
  vertices := [⟨65600, 15200, 15200, 0⟩,
    ⟨71200, 12400, 12400, 0⟩,
    ⟨68400, 18000, 9600, 0⟩,
    ⟨65436, 15162, 15162, 240⟩,
    ⟨71022, 12369, 12369, 240⟩,
    ⟨68229, 17955, 9576, 240⟩]
  profileDen := 96000
  pi := [85126198, 227703810, 238486556, 522425260]
  slope := [341401166, -167556664, -202735810]
  radiusNum := 1
  radiusDen := 8
}

set_option maxRecDepth 40000
set_option maxHeartbeats 0

theorem f0Archived7_data_ok : dataOK f0Archived7 = true := by decide +kernel

def f0Archived7Chart0 : RowTree :=
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
                        (.box 125 117)
                      )
                    )
                    (.splitB
                      (.splitA
                        (.box 120 125)
                        (.box 117 125)
                      )
                      (.splitA
                        (.box 120 119)
                        (.box 116 119)
                      )
                    )
                  )
                  (.splitA
                    (.splitB
                      (.box 125 109)
                      (.box 125 108)
                    )
                    (.box 118 108)
                  )
                )
                (.splitB
                  (.splitB
                    (.box 108 125)
                    (.box 108 119)
                  )
                  (.splitB
                    (.box 108 111)
                    (.box 108 104)
                  )
                )
              )
              (.splitA
                (.splitB
                  (.box 121 95)
                  (.box 121 79)
                )
                (.splitB
                  (.box 105 95)
                  (.box 105 79)
                )
              )
            )
            (.splitB
              (.splitB
                (.box 87 121)
                (.box 87 106)
              )
              (.splitB
                (.box 87 89)
                (.box 81 79)
              )
            )
          )
          (.splitB
            (.splitA
              (.box 113 161)
              (.box 81 161)
            )
            (.splitA
              (.box 113 193)
              (.box 81 193)
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
                (.box 177 161)
                (.box 137 146)
              )
              (.splitA
                (.splitB
                  (.box 225 177)
                  (.box 225 129)
                )
                (.box 289 145)
              )
            )
            (.splitA
              (.splitB
                (.splitA
                  (.box 177 225)
                  (.splitB
                    (.box 129 241)
                    (.box 129 209)
                  )
                )
                (.splitA
                  (.box 177 257)
                  (.box 129 289)
                )
              )
              (.splitA
                (.splitB
                  (.splitB
                    (.splitA
                      (.box 233 233)
                      (.splitA
                        (.box 217 233)
                        (.box 201 241)
                      )
                    )
                    (.splitA
                      (.splitB
                        (.box 233 217)
                        (.box 233 201)
                      )
                      (.splitA
                        (.splitB
                          (.box 217 217)
                          (.box 217 201)
                        )
                        (.box 201 210)
                      )
                    )
                  )
                  (.splitA
                    (.box 233 289)
                    (.splitB
                      (.box 209 193)
                      (.box 209 321)
                    )
                  )
                )
                (.splitB
                  (.splitB
                    (.box 289 241)
                    (.box 289 209)
                  )
                  (.box 289 289)
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
        (.splitA
          (.splitB
            (.splitB
              (.box 161 0)
              (.box 161 161)
            )
            (.box 161 97)
          )
          (.splitB
            (.splitA
              (.splitB
                (.box 225 0)
                (.box 225 161)
              )
              (.splitB
                (.box 257 0)
                (.box 257 161)
              )
            )
            (.box 193 97)
          )
        )
      )
    )
    (.splitB
      (.splitB
        (.splitA
          (.box 193 97)
          (.box 97 97)
        )
        (.splitB
          (.splitA
            (.splitA
              (.box 0 161)
              (.box 161 161)
            )
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
      (.splitA
        (.splitB
          (.splitA
            (.box 0 193)
            (.box 161 129)
          )
          (.box 0 65)
        )
        (.box 97 65)
      )
    )
  )

theorem f0Archived7Chart0_ok : checkChart f0Archived7 0 1 2 f0Archived7Chart0 = true := by decide +kernel

def f0Archived7Chart1 : RowTree :=
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
                  (.box 121 92)
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
                        (.box 116 125)
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
                      (.box 111 117)
                      (.box 105 115)
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
                (.box 87 118)
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
        (.splitB
          (.box 129 97)
          (.box 193 129)
        )
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

theorem f0Archived7Chart1_ok : checkChart f0Archived7 1 0 2 f0Archived7Chart1 = true := by decide +kernel

def f0Archived7Chart2 : RowTree :=
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
              (.box 81 176)
            )
          )
          (.splitA
            (.splitB
              (.splitA
                (.splitB
                  (.box 118 81)
                  (.box 121 95)
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
                      (.splitA
                        (.splitB
                          (.box 126 117)
                          (.box 127 120)
                        )
                        (.splitB
                          (.box 123 116)
                          (.box 123 120)
                        )
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
                    (.box 104 105)
                  )
                  (.splitB
                    (.splitA
                      (.box 111 117)
                      (.box 105 115)
                    )
                    (.box 109 123)
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
              (.splitB
                (.splitA
                  (.box 92 105)
                  (.box 81 102)
                )
                (.box 87 118)
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
        (.box 65 65)
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

theorem f0Archived7Chart2_ok : checkChart f0Archived7 2 0 1 f0Archived7Chart2 = true := by decide +kernel

end HlawkaSchatten.BelowExponent.FacetNumeric
