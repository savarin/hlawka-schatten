/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.FacetNumeric

/-! Archived facet prism certificate data: `F2Prism82Data`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true

@[expose] public section

namespace HlawkaSchatten.BelowExponent.FacetNumeric

def f2Archived82 : Prism := {
  vertices := [⟨47600, 11600, 4800, 0⟩,
    ⟨46000, 12400, 5600, 0⟩,
    ⟨44000, 16800, 3200, 0⟩,
    ⟨47481, 11571, 4788, 160⟩,
    ⟨45885, 12369, 5586, 160⟩,
    ⟨43890, 16758, 3192, 160⟩]
  profileDen := 64000
  pi := [64950861, 143212716, 335535242, 530043005]
  slope := [345110461, -199401541, -159364741]
  radiusNum := 1
  radiusDen := 8
}

set_option maxRecDepth 40000
set_option maxHeartbeats 0

theorem f2Archived82_data_ok : dataOK f2Archived82 = true := by decide +kernel

def f2Archived82Chart0 : RowTree :=
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
                          (.box 127 123)
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
                      (.splitA
                        (.box 127 111)
                        (.box 124 111)
                      )
                      (.box 125 103)
                    )
                    (.splitB
                      (.box 119 111)
                      (.box 119 103)
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
                  (.splitA
                    (.box 125 92)
                    (.box 119 92)
                  )
                  (.box 121 76)
                )
                (.splitB
                  (.box 108 92)
                  (.box 108 76)
                )
              )
            )
            (.splitB
              (.box 92 113)
              (.box 92 81)
            )
          )
          (.splitA
            (.splitB
              (.splitA
                (.box 121 177)
                (.box 105 177)
              )
              (.splitB
                (.box 113 225)
                (.box 113 257)
              )
            )
            (.splitB
              (.splitA
                (.box 89 161)
                (.box 73 161)
              )
              (.splitA
                (.box 89 193)
                (.box 73 193)
              )
            )
          )
        )
        (.splitB
          (.splitA
            (.box 161 97)
            (.box 193 97)
          )
          (.splitB
            (.splitA
              (.box 161 161)
              (.box 193 161)
            )
            (.splitA
              (.splitA
                (.box 177 193)
                (.box 145 193)
              )
              (.box 193 193)
            )
          )
        )
      )
      (.splitA
        (.splitB
          (.splitA
            (.box 113 193)
            (.splitB
              (.box 83 0)
              (.box 81 161)
            )
          )
          (.box 97 75)
        )
        (.splitB
          (.splitA
            (.splitB
              (.box 161 0)
              (.box 161 161)
            )
            (.box 193 193)
          )
          (.box 129 97)
        )
      )
    )
    (.splitB
      (.splitA
        (.box 0 65)
        (.box 97 65)
      )
      (.box 129 129)
    )
  )

theorem f2Archived82Chart0_ok : checkChart f2Archived82 0 1 2 f2Archived82Chart0 = true := by decide +kernel

def f2Archived82Chart1 : RowTree :=
  (.splitA
    (.splitB
      (.splitA
        (.splitB
          (.box 97 75)
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
              (.splitA
                (.box 121 193)
                (.box 105 193)
              )
              (.splitA
                (.splitB
                  (.box 121 145)
                  (.box 121 177)
                )
                (.box 109 161)
              )
            )
            (.splitB
              (.box 82 193)
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
                      (.box 125 103)
                      (.splitA
                        (.box 127 111)
                        (.box 124 111)
                      )
                    )
                    (.splitB
                      (.box 119 103)
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
                          (.box 127 123)
                          (.box 127 127)
                        )
                        (.box 124 125)
                      )
                    )
                    (.splitB
                      (.box 119 117)
                      (.box 119 125)
                    )
                  )
                )
                (.splitB
                  (.box 110 105)
                  (.box 111 120)
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
            (.box 161 257)
            (.box 161 161)
          )
          (.box 161 97)
        )
      )
    )
    (.splitB
      (.box 129 129)
      (.splitA
        (.box 0 65)
        (.box 97 65)
      )
    )
  )

theorem f2Archived82Chart1_ok : checkChart f2Archived82 1 0 2 f2Archived82Chart1 = true := by decide +kernel

def f2Archived82Chart2 : RowTree :=
  (.splitA
    (.splitB
      (.splitA
        (.box 81 129)
        (.splitB
          (.box 129 97)
          (.splitA
            (.box 129 193)
            (.splitB
              (.box 193 161)
              (.splitA
                (.box 225 257)
                (.box 257 257)
              )
            )
          )
        )
      )
      (.splitA
        (.splitB
          (.splitA
            (.splitB
              (.box 113 193)
              (.box 113 177)
            )
            (.splitB
              (.box 81 129)
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
                  (.box 113 81)
                  (.box 118 95)
                )
                (.splitB
                  (.box 99 81)
                  (.splitA
                    (.box 106 95)
                    (.splitB
                      (.box 98 89)
                      (.box 101 95)
                    )
                  )
                )
              )
              (.splitA
                (.splitB
                  (.splitA
                    (.splitB
                      (.box 121 105)
                      (.box 123 112)
                    )
                    (.splitB
                      (.box 115 105)
                      (.splitA
                        (.box 118 112)
                        (.splitB
                          (.box 114 109)
                          (.box 115 112)
                        )
                      )
                    )
                  )
                  (.splitA
                    (.splitB
                      (.splitA
                        (.splitB
                          (.box 125 117)
                          (.box 126 120)
                        )
                        (.splitB
                          (.box 122 117)
                          (.box 123 120)
                        )
                      )
                      (.splitA
                        (.splitB
                          (.box 126 124)
                          (.splitA
                            (.box 128 127)
                            (.box 126 127)
                          )
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
                          (.splitA
                            (.box 119 116)
                            (.box 118 116)
                          )
                          (.box 119 119)
                        )
                        (.splitB
                          (.splitA
                            (.box 116 116)
                            (.box 114 115)
                          )
                          (.box 116 118)
                        )
                      )
                      (.splitA
                        (.splitB
                          (.box 120 122)
                          (.box 120 126)
                        )
                        (.box 116 123)
                      )
                    )
                  )
                )
                (.splitB
                  (.splitA
                    (.splitB
                      (.splitA
                        (.box 110 104)
                        (.box 107 103)
                      )
                      (.splitA
                        (.splitB
                          (.box 111 108)
                          (.box 111 112)
                        )
                        (.splitB
                          (.box 107 109)
                          (.box 107 110)
                        )
                      )
                    )
                    (.splitB
                      (.splitB
                        (.box 101 100)
                        (.box 103 102)
                      )
                      (.box 103 107)
                    )
                  )
                  (.splitB
                    (.splitA
                      (.splitB
                        (.splitA
                          (.box 111 114)
                          (.box 110 114)
                        )
                        (.box 111 118)
                      )
                      (.box 104 114)
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
                  (.splitA
                    (.box 91 79)
                    (.box 85 76)
                  )
                  (.splitA
                    (.splitB
                      (.box 93 87)
                      (.box 93 95)
                    )
                    (.splitB
                      (.box 87 85)
                      (.box 88 91)
                    )
                  )
                )
                (.splitB
                  (.splitB
                    (.box 73 72)
                    (.box 76 75)
                  )
                  (.box 76 86)
                )
              )
              (.splitB
                (.splitA
                  (.splitB
                    (.box 92 100)
                    (.box 92 106)
                  )
                  (.box 79 99)
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
          (.splitB
            (.splitA
              (.splitB
                (.box 161 257)
                (.splitA
                  (.box 177 225)
                  (.box 145 225)
                )
              )
              (.splitA
                (.splitB
                  (.box 225 257)
                  (.box 225 225)
                )
                (.splitB
                  (.box 257 257)
                  (.box 257 225)
                )
              )
            )
            (.splitA
              (.splitA
                (.splitB
                  (.box 177 145)
                  (.box 177 177)
                )
                (.splitB
                  (.box 145 145)
                  (.box 145 177)
                )
              )
              (.box 225 146)
            )
          )
          (.splitA
            (.splitB
              (.splitB
                (.splitA
                  (.box 177 73)
                  (.box 145 73)
                )
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
              (.splitB
                (.box 193 225)
                (.box 257 257)
              )
            )
            (.box 161 129)
          )
        )
        (.splitB
          (.box 84 97)
          (.box 97 129)
        )
      )
      (.splitB
        (.splitA
          (.splitA
            (.splitB
              (.box 257 257)
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

theorem f2Archived82Chart2_ok : checkChart f2Archived82 2 0 1 f2Archived82Chart2 = true := by decide +kernel

end HlawkaSchatten.BelowExponent.FacetNumeric
