/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.FacetNumeric

/-! Archived facet prism certificate data: `F1Prism6Data`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true

@[expose] public section

namespace HlawkaSchatten.BelowExponent.FacetNumeric

def f1Archived6 : Prism := {
  vertices := [⟨132000, 109600, 14400, 0⟩,
    ⟨128800, 106400, 20800, 0⟩,
    ⟨125200, 114000, 16800, 0⟩,
    ⟨131670, 109326, 14364, 640⟩,
    ⟨128478, 106134, 20748, 640⟩,
    ⟨124887, 113715, 16758, 640⟩]
  profileDen := 256000
  pi := [147616949, 171710538, 229128216, 525286121]
  slope := [170076129, 86259907, -279505622]
  radiusNum := 1
  radiusDen := 8
}

set_option maxRecDepth 40000
set_option maxHeartbeats 0

theorem f1Archived6_data_ok : dataOK f1Archived6 = true := by decide +kernel

def f1Archived6Chart0 : RowTree :=
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
                      (.splitA
                        (.splitB
                          (.box 128 127)
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
                  (.box 111 121)
                )
                (.splitA
                  (.splitA
                    (.splitB
                      (.box 125 111)
                      (.box 125 103)
                    )
                    (.splitB
                      (.box 120 111)
                      (.box 120 103)
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
          (.splitA
            (.box 65 97)
            (.box 193 97)
          )
        )
        (.splitA
          (.splitB
            (.splitA
              (.splitA
                (.box 121 177)
                (.box 105 177)
              )
              (.box 89 161)
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
                  (.box 177 321)
                )
                (.splitB
                  (.box 145 225)
                  (.box 145 321)
                )
              )
              (.box 129 257)
            )
          )
        )
      )
      (.splitA
        (.splitB
          (.splitB
            (.splitA
              (.box 102 0)
              (.box 73 257)
            )
            (.box 97 161)
          )
          (.box 97 75)
        )
        (.splitB
          (.splitA
            (.splitA
              (.splitB
                (.box 169 257)
                (.box 177 161)
              )
              (.splitB
                (.box 153 257)
                (.box 145 161)
              )
            )
            (.splitB
              (.box 129 0)
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
        (.box 0 129)
      )
      (.splitB
        (.box 0 129)
        (.box 0 65)
      )
    )
  )

theorem f1Archived6Chart0_ok : checkChart f1Archived6 0 1 2 f1Archived6Chart0 = true := by decide +kernel

def f1Archived6Chart1 : RowTree :=
  (.splitA
    (.splitB
      (.splitA
        (.splitB
          (.box 97 75)
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
                (.splitB
                  (.box 177 225)
                  (.box 177 0)
                )
              )
              (.splitB
                (.box 145 161)
                (.splitB
                  (.box 145 225)
                  (.box 145 0)
                )
              )
            )
            (.splitB
              (.box 193 161)
              (.splitA
                (.box 129 257)
                (.box 257 193)
              )
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
                  (.box 177 321)
                  (.box 177 225)
                )
                (.splitB
                  (.box 145 321)
                  (.box 145 225)
                )
              )
              (.splitA
                (.box 129 257)
                (.box 257 193)
              )
            )
            (.splitA
              (.box 161 161)
              (.box 193 161)
            )
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
                  (.box 121 93)
                  (.box 108 92)
                )
              )
              (.splitA
                (.splitB
                  (.splitA
                    (.splitB
                      (.box 125 103)
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
              (.box 92 81)
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
        (.box 0 65)
        (.box 0 129)
      )
      (.splitB
        (.box 0 129)
        (.box 0 84)
      )
    )
  )

theorem f1Archived6Chart1_ok : checkChart f1Archived6 1 0 2 f1Archived6Chart1 = true := by decide +kernel

def f1Archived6Chart2 : RowTree :=
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
            (.box 97 162)
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
                  (.box 99 81)
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
                        (.box 124 121)
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
                          (.box 119 120)
                        )
                        (.splitB
                          (.box 116 115)
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
                      (.splitA
                        (.box 111 111)
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
                        (.box 112 118)
                      )
                      (.box 105 114)
                    )
                    (.box 111 121)
                  )
                )
              )
            )
            (.splitB
              (.splitA
                (.splitB
                  (.box 89 76)
                  (.splitA
                    (.box 93 92)
                    (.box 88 89)
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
                    (.box 95 106)
                  )
                  (.box 81 99)
                )
                (.box 92 115)
              )
            )
          )
        )
        (.splitB
          (.splitA
            (.splitB
              (.box 161 225)
              (.splitB
                (.box 161 145)
                (.box 177 169)
              )
            )
            (.splitB
              (.splitB
                (.box 193 257)
                (.box 193 225)
              )
              (.box 193 160)
            )
          )
          (.splitB
            (.splitA
              (.splitB
                (.box 177 73)
                (.box 161 84)
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
          (.splitA
            (.box 193 193)
            (.box 161 129)
          )
        )
        (.box 75 65)
      )
      (.splitA
        (.splitB
          (.splitA
            (.splitB
              (.box 193 193)
              (.box 193 161)
            )
            (.box 161 129)
          )
          (.box 0 65)
        )
        (.box 97 129)
      )
    )
  )

theorem f1Archived6Chart2_ok : checkChart f1Archived6 2 0 1 f1Archived6Chart2 = true := by decide +kernel

end HlawkaSchatten.BelowExponent.FacetNumeric
