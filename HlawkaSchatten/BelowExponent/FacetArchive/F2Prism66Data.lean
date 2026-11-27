/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.FacetNumeric

/-! Archived facet prism certificate data: `F2Prism66Data`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true

@[expose] public section

namespace HlawkaSchatten.BelowExponent.FacetNumeric

def f2Archived66 : Prism := {
  vertices := [⟨277600, 205600, 28800, 0⟩,
    ⟨270400, 216000, 25600, 0⟩,
    ⟨277200, 209200, 25600, 0⟩,
    ⟨276906, 205086, 28728, 1280⟩,
    ⟨269724, 215460, 25536, 1280⟩,
    ⟨276507, 208677, 25536, 1280⟩]
  profileDen := 512000
  pi := [134613379, 169138879, 242414797, 527574769]
  slope := [187092134, 75652196, -281336618]
  radiusNum := 1
  radiusDen := 8
}

set_option maxRecDepth 40000
set_option maxHeartbeats 0

theorem f2Archived66_data_ok : dataOK f2Archived66 = true := by decide +kernel

def f2Archived66Chart0 : RowTree :=
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
                        (.splitA
                          (.box 127 120)
                          (.box 124 120)
                        )
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
                      (.splitA
                        (.box 127 111)
                        (.box 124 111)
                      )
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
                  (.splitA
                    (.box 125 92)
                    (.box 119 92)
                  )
                  (.box 111 92)
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
          (.box 161 96)
        )
        (.splitA
          (.splitB
            (.splitA
              (.splitA
                (.box 121 176)
                (.box 105 176)
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
                  (.box 177 257)
                )
                (.box 145 257)
              )
              (.box 129 193)
            )
          )
        )
      )
      (.splitA
        (.splitB
          (.splitA
            (.box 113 193)
            (.splitB
              (.box 73 257)
              (.box 81 161)
            )
          )
          (.box 97 75)
        )
        (.splitB
          (.splitA
            (.splitA
              (.splitB
                (.box 177 257)
                (.box 177 161)
              )
              (.splitB
                (.box 145 257)
                (.box 145 161)
              )
            )
            (.box 129 193)
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
      (.box 0 129)
    )
  )

theorem f2Archived66Chart0_ok : checkChart f2Archived66 0 1 2 f2Archived66Chart0 = true := by decide +kernel

def f2Archived66Chart1 : RowTree :=
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
                (.box 177 257)
              )
              (.splitB
                (.box 145 161)
                (.box 145 257)
              )
            )
            (.box 129 193)
          )
        )
      )
      (.splitB
        (.splitA
          (.splitB
            (.splitA
              (.box 113 193)
              (.splitB
                (.box 73 257)
                (.box 81 225)
              )
            )
            (.splitA
              (.splitA
                (.box 117 176)
                (.box 109 162)
              )
              (.box 89 161)
            )
          )
          (.splitB
            (.splitA
              (.splitA
                (.box 177 257)
                (.box 145 257)
              )
              (.box 129 193)
            )
            (.box 161 161)
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
                  (.splitA
                    (.box 125 92)
                    (.box 119 92)
                  )
                  (.box 111 89)
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
                      (.box 120 111)
                    )
                  )
                  (.splitA
                    (.splitB
                      (.splitB
                        (.splitA
                          (.box 127 116)
                          (.box 124 116)
                        )
                        (.splitA
                          (.box 127 120)
                          (.box 124 120)
                        )
                      )
                      (.splitA
                        (.splitB
                          (.box 127 124)
                          (.box 128 127)
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
          (.box 161 96)
        )
      )
    )
    (.splitB
      (.box 0 129)
      (.splitA
        (.splitB
          (.box 129 193)
          (.box 0 7)
        )
        (.box 97 65)
      )
    )
  )

theorem f2Archived66Chart1_ok : checkChart f2Archived66 1 0 2 f2Archived66Chart1 = true := by decide +kernel

def f2Archived66Chart2 : RowTree :=
  (.splitA
    (.splitB
      (.splitA
        (.box 97 129)
        (.splitB
          (.box 0 65)
          (.splitA
            (.box 161 0)
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
            (.box 97 161)
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
                    (.box 106 95)
                    (.box 101 92)
                  )
                )
              )
              (.splitA
                (.splitB
                  (.splitA
                    (.box 122 111)
                    (.splitB
                      (.box 114 105)
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
                        (.splitA
                          (.box 126 121)
                          (.box 123 120)
                        )
                      )
                      (.splitA
                        (.splitB
                          (.box 126 124)
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
                        (.box 110 111)
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
                    (.box 110 121)
                  )
                )
              )
            )
            (.splitB
              (.splitA
                (.splitB
                  (.box 89 76)
                  (.splitA
                    (.box 91 92)
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
                (.box 92 113)
              )
            )
          )
        )
        (.splitB
          (.splitA
            (.splitB
              (.box 161 225)
              (.splitA
                (.splitB
                  (.box 177 145)
                  (.box 177 177)
                )
                (.box 145 161)
              )
            )
            (.splitB
              (.splitB
                (.box 193 257)
                (.box 193 225)
              )
              (.box 225 161)
            )
          )
          (.splitB
            (.splitA
              (.splitB
                (.box 177 73)
                (.box 65 81)
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
      (.splitA
        (.splitB
          (.splitA
            (.splitB
              (.box 193 257)
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

theorem f2Archived66Chart2_ok : checkChart f2Archived66 2 0 1 f2Archived66Chart2 = true := by decide +kernel

end HlawkaSchatten.BelowExponent.FacetNumeric
