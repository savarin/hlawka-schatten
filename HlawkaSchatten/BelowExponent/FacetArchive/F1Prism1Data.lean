/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.FacetNumeric

/-! Archived facet prism certificate data: `F1Prism1Data`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true

@[expose] public section

namespace HlawkaSchatten.BelowExponent.FacetNumeric

def f1Archived1 : Prism := {
  vertices := [⟨64400, 53200, 10400, 0⟩,
    ⟨57600, 57600, 12800, 0⟩,
    ⟨60800, 60800, 6400, 0⟩,
    ⟨64239, 53067, 10374, 320⟩,
    ⟨57456, 57456, 12768, 320⟩,
    ⟨60648, 60648, 6384, 320⟩]
  profileDen := 128000
  pi := [150589067, 153572052, 242779869, 526800836]
  slope := [116004328, 123520739, -259665224]
  radiusNum := 1
  radiusDen := 8
}

set_option maxRecDepth 40000
set_option maxHeartbeats 0

theorem f1Archived1_data_ok : dataOK f1Archived1 = true := by decide +kernel

def f1Archived1Chart0 : RowTree :=
  (.splitA
    (.splitB
      (.splitB
        (.splitA
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
                      (.box 120 111)
                      (.box 120 103)
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
                  (.splitA
                    (.box 125 92)
                    (.box 119 92)
                  )
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
                (.box 81 257)
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
                (.splitB
                  (.box 145 225)
                  (.box 145 257)
                )
              )
              (.box 129 257)
            )
          )
        )
      )
      (.splitA
        (.splitB
          (.splitA
            (.box 113 193)
            (.splitB
              (.box 81 257)
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
                (.box 145 0)
                (.box 145 161)
              )
            )
            (.splitB
              (.box 129 257)
              (.box 193 161)
            )
          )
          (.box 129 97)
        )
      )
    )
    (.splitB
      (.splitA
        (.splitB
          (.box 0 7)
          (.box 0 129)
        )
        (.box 97 65)
      )
      (.box 0 129)
    )
  )

theorem f1Archived1Chart0_ok : checkChart f1Archived1 0 1 2 f1Archived1Chart0 = true := by decide +kernel

def f1Archived1Chart1 : RowTree :=
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
                (.box 81 321)
                (.box 81 225)
              )
            )
            (.splitA
              (.splitA
                (.box 121 176)
                (.box 105 176)
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
                  (.splitA
                    (.box 125 92)
                    (.box 119 92)
                  )
                  (.box 111 92)
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
                      (.box 120 103)
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
                          (.box 128 123)
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

theorem f1Archived1Chart1_ok : checkChart f1Archived1 1 0 2 f1Archived1Chart1 = true := by decide +kernel

def f1Archived1Chart2 : RowTree :=
  (.splitA
    (.splitB
      (.splitB
        (.box 129 97)
        (.splitA
          (.box 65 0)
          (.splitA
            (.box 161 0)
            (.box 257 193)
          )
        )
      )
      (.splitB
        (.splitA
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
              (.box 161 225)
              (.splitB
                (.box 161 145)
                (.splitA
                  (.box 177 177)
                  (.box 145 177)
                )
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
        )
        (.splitA
          (.splitB
            (.splitA
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
            )
            (.splitA
              (.splitB
                (.splitA
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
                      (.box 109 103)
                      (.splitB
                        (.box 109 108)
                        (.box 111 110)
                      )
                    )
                    (.splitB
                      (.box 103 101)
                      (.box 103 109)
                    )
                  )
                )
                (.splitA
                  (.splitB
                    (.splitA
                      (.splitB
                        (.box 123 117)
                        (.box 124 120)
                      )
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
                    )
                    (.splitA
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
                      (.splitA
                        (.box 120 124)
                        (.box 117 123)
                      )
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
                    (.box 111 122)
                  )
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
          (.splitB
            (.splitA
              (.splitB
                (.box 177 73)
                (.box 65 89)
              )
              (.box 193 81)
            )
            (.box 161 97)
          )
        )
      )
    )
    (.splitB
      (.splitB
        (.splitA
          (.box 129 97)
          (.box 84 84)
        )
        (.splitA
          (.splitB
            (.box 129 161)
            (.splitA
              (.box 193 257)
              (.box 161 193)
            )
          )
          (.box 97 129)
        )
      )
      (.splitA
        (.splitB
          (.splitB
            (.box 193 257)
            (.box 0 161)
          )
          (.box 0 75)
        )
        (.box 97 129)
      )
    )
  )

theorem f1Archived1Chart2_ok : checkChart f1Archived1 2 0 1 f1Archived1Chart2 = true := by decide +kernel

end HlawkaSchatten.BelowExponent.FacetNumeric
