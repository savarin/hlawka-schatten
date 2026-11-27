/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.FacetNumeric

/-! Archived facet prism certificate data: `F2Prism1Data`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true

@[expose] public section

namespace HlawkaSchatten.BelowExponent.FacetNumeric

def f2Archived1 : Prism := {
  vertices := [⟨454400, 28800, 28800, 0⟩,
    ⟨454000, 32400, 25600, 0⟩,
    ⟨460800, 25600, 25600, 0⟩,
    ⟨453264, 28728, 28728, 1280⟩,
    ⟨452865, 32319, 25536, 1280⟩,
    ⟨459648, 25536, 25536, 1280⟩]
  profileDen := 512000
  pi := [30682546, 256227412, 256227412, 530604454]
  slope := [515757129, -260930067, -267359980]
  radiusNum := 1
  radiusDen := 8
}

set_option maxRecDepth 40000
set_option maxHeartbeats 0

theorem f2Archived1_data_ok : dataOK f2Archived1 = true := by decide +kernel

def f2Archived1Chart0 : RowTree :=
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
                        (.splitB
                          (.box 124 127)
                          (.box 123 123)
                        )
                      )
                      (.splitB
                        (.splitA
                          (.box 127 120)
                          (.box 123 120)
                        )
                        (.splitA
                          (.box 127 116)
                          (.box 123 116)
                        )
                      )
                    )
                    (.splitB
                      (.splitA
                        (.splitB
                          (.box 120 127)
                          (.box 120 123)
                        )
                        (.splitB
                          (.box 116 127)
                          (.box 116 123)
                        )
                      )
                      (.splitA
                        (.splitB
                          (.box 120 120)
                          (.box 120 116)
                        )
                        (.splitB
                          (.box 116 120)
                          (.box 116 116)
                        )
                      )
                    )
                  )
                  (.splitB
                    (.splitA
                      (.splitA
                        (.box 126 111)
                        (.box 124 111)
                      )
                      (.box 118 110)
                    )
                    (.splitA
                      (.box 125 103)
                      (.box 117 103)
                    )
                  )
                )
                (.splitB
                  (.splitA
                    (.splitB
                      (.splitA
                        (.box 111 125)
                        (.box 110 125)
                      )
                      (.box 110 118)
                    )
                    (.splitB
                      (.box 103 125)
                      (.box 103 117)
                    )
                  )
                  (.splitA
                    (.splitB
                      (.box 111 111)
                      (.box 111 103)
                    )
                    (.splitB
                      (.box 103 111)
                      (.box 103 103)
                    )
                  )
                )
              )
              (.splitB
                (.splitA
                  (.splitA
                    (.box 125 92)
                    (.box 117 92)
                  )
                  (.splitA
                    (.box 109 92)
                    (.box 103 92)
                  )
                )
                (.splitA
                  (.box 121 76)
                  (.box 105 76)
                )
              )
            )
            (.splitB
              (.splitA
                (.splitB
                  (.splitB
                    (.box 92 125)
                    (.box 92 117)
                  )
                  (.splitB
                    (.box 92 109)
                    (.box 92 103)
                  )
                )
                (.splitB
                  (.box 76 121)
                  (.box 76 105)
                )
              )
              (.splitA
                (.splitB
                  (.box 92 89)
                  (.box 89 76)
                )
                (.splitB
                  (.box 76 89)
                  (.box 73 76)
                )
              )
            )
          )
          (.splitB
            (.splitA
              (.splitB
                (.box 113 177)
                (.box 113 145)
              )
              (.splitB
                (.splitA
                  (.box 89 177)
                  (.box 73 177)
                )
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
          (.splitA
            (.splitB
              (.splitA
                (.box 177 113)
                (.box 145 113)
              )
              (.splitA
                (.splitB
                  (.box 177 89)
                  (.box 177 73)
                )
                (.box 145 81)
              )
            )
            (.splitB
              (.box 193 113)
              (.splitA
                (.box 225 81)
                (.box 257 81)
              )
            )
          )
          (.splitA
            (.splitB
              (.splitA
                (.splitB
                  (.box 177 177)
                  (.box 177 145)
                )
                (.splitB
                  (.box 145 177)
                  (.splitA
                    (.box 153 145)
                    (.box 137 145)
                  )
                )
              )
              (.splitB
                (.splitA
                  (.box 177 225)
                  (.splitB
                    (.box 145 241)
                    (.box 145 209)
                  )
                )
                (.splitA
                  (.box 177 257)
                  (.box 145 257)
                )
              )
            )
            (.splitB
              (.splitA
                (.splitB
                  (.box 225 177)
                  (.splitA
                    (.box 241 145)
                    (.box 209 145)
                  )
                )
                (.splitB
                  (.box 257 177)
                  (.box 257 145)
                )
              )
              (.splitA
                (.splitB
                  (.splitA
                    (.box 241 225)
                    (.box 209 225)
                  )
                  (.box 225 257)
                )
                (.splitB
                  (.box 257 225)
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
              (.box 81 193)
              (.box 81 161)
            )
          )
          (.box 84 75)
        )
        (.splitB
          (.splitA
            (.splitB
              (.box 161 257)
              (.box 161 161)
            )
            (.splitB
              (.box 193 257)
              (.box 193 161)
            )
          )
          (.box 129 97)
        )
      )
    )
    (.splitB
      (.splitB
        (.splitA
          (.splitB
            (.box 193 113)
            (.splitA
              (.box 193 81)
              (.box 161 81)
            )
          )
          (.box 75 84)
        )
        (.splitA
          (.splitB
            (.splitA
              (.box 257 161)
              (.box 161 161)
            )
            (.splitA
              (.box 257 193)
              (.box 161 193)
            )
          )
          (.box 97 129)
        )
      )
      (.splitA
        (.splitB
          (.box 193 193)
          (.box 0 75)
        )
        (.box 97 129)
      )
    )
  )

theorem f2Archived1Chart0_ok : checkChart f2Archived1 0 1 2 f2Archived1Chart0 = true := by decide +kernel

def f2Archived1Chart1 : RowTree :=
  (.splitA
    (.splitB
      (.splitA
        (.splitB
          (.box 84 75)
          (.splitA
            (.box 113 193)
            (.splitB
              (.box 81 161)
              (.box 81 257)
            )
          )
        )
        (.splitB
          (.splitA
            (.box 161 97)
            (.box 193 97)
          )
          (.splitA
            (.splitB
              (.box 161 161)
              (.splitA
                (.box 177 257)
                (.box 145 257)
              )
            )
            (.splitA
              (.splitB
                (.box 225 161)
                (.box 225 257)
              )
              (.splitB
                (.box 257 161)
                (.box 257 193)
              )
            )
          )
        )
      )
      (.splitA
        (.splitB
          (.splitA
            (.splitB
              (.splitA
                (.box 121 193)
                (.box 105 225)
              )
              (.splitA
                (.splitB
                  (.box 121 145)
                  (.box 121 177)
                )
                (.splitB
                  (.box 105 145)
                  (.box 105 177)
                )
              )
            )
            (.splitB
              (.splitB
                (.box 81 257)
                (.splitA
                  (.box 89 225)
                  (.box 73 225)
                )
              )
              (.splitA
                (.splitB
                  (.box 89 145)
                  (.box 89 177)
                )
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
                  (.splitA
                    (.box 123 76)
                    (.box 115 76)
                  )
                  (.splitA
                    (.box 123 92)
                    (.splitB
                      (.box 117 88)
                      (.box 117 95)
                    )
                  )
                )
                (.splitB
                  (.splitA
                    (.box 109 76)
                    (.box 101 76)
                  )
                  (.splitA
                    (.splitB
                      (.box 109 87)
                      (.box 109 95)
                    )
                    (.splitB
                      (.box 101 87)
                      (.box 101 95)
                    )
                  )
                )
              )
              (.splitA
                (.splitB
                  (.splitA
                    (.splitB
                      (.splitA
                        (.box 126 103)
                        (.box 122 103)
                      )
                      (.splitA
                        (.splitB
                          (.box 126 110)
                          (.box 126 111)
                        )
                        (.splitB
                          (.box 123 108)
                          (.box 123 112)
                        )
                      )
                    )
                    (.splitB
                      (.splitA
                        (.box 119 103)
                        (.box 115 103)
                      )
                      (.splitA
                        (.splitB
                          (.box 119 108)
                          (.box 119 112)
                        )
                        (.splitB
                          (.box 115 108)
                          (.box 115 112)
                        )
                      )
                    )
                  )
                  (.splitA
                    (.splitB
                      (.splitA
                        (.splitB
                          (.splitA
                            (.box 128 116)
                            (.box 126 116)
                          )
                          (.box 127 120)
                        )
                        (.splitB
                          (.splitA
                            (.box 124 116)
                            (.box 122 116)
                          )
                          (.box 123 120)
                        )
                      )
                      (.splitA
                        (.splitB
                          (.box 127 123)
                          (.splitA
                            (.box 128 127)
                            (.box 126 127)
                          )
                        )
                        (.splitB
                          (.box 123 123)
                          (.box 123 127)
                        )
                      )
                    )
                    (.splitB
                      (.splitA
                        (.splitB
                          (.splitA
                            (.box 120 116)
                            (.box 118 115)
                          )
                          (.box 120 119)
                        )
                        (.splitB
                          (.box 116 115)
                          (.box 116 119)
                        )
                      )
                      (.splitA
                        (.splitB
                          (.box 120 123)
                          (.box 120 126)
                        )
                        (.splitB
                          (.box 116 123)
                          (.box 116 126)
                        )
                      )
                    )
                  )
                )
                (.splitB
                  (.splitA
                    (.splitB
                      (.splitA
                        (.box 111 103)
                        (.box 108 101)
                      )
                      (.splitA
                        (.box 112 109)
                        (.box 108 109)
                      )
                    )
                    (.splitB
                      (.box 103 101)
                      (.box 103 109)
                    )
                  )
                  (.splitA
                    (.splitB
                      (.splitA
                        (.box 112 117)
                        (.box 108 117)
                      )
                      (.splitA
                        (.box 112 123)
                        (.box 108 123)
                      )
                    )
                    (.splitB
                      (.box 103 117)
                      (.box 103 123)
                    )
                  )
                )
              )
            )
            (.splitB
              (.splitA
                (.splitB
                  (.splitA
                    (.box 93 76)
                    (.box 87 73)
                  )
                  (.splitA
                    (.box 95 89)
                    (.box 87 89)
                  )
                )
                (.splitB
                  (.box 76 73)
                  (.box 76 89)
                )
              )
              (.splitA
                (.splitB
                  (.splitA
                    (.box 95 105)
                    (.box 87 105)
                  )
                  (.splitA
                    (.box 96 118)
                    (.box 88 118)
                  )
                )
                (.splitB
                  (.box 76 105)
                  (.box 76 118)
                )
              )
            )
          )
        )
        (.splitB
          (.splitA
            (.splitB
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
              (.splitA
                (.splitB
                  (.box 177 145)
                  (.box 177 177)
                )
                (.box 145 161)
              )
            )
            (.splitB
              (.splitA
                (.splitB
                  (.box 225 257)
                  (.box 225 225)
                )
                (.box 257 193)
              )
              (.splitA
                (.box 225 161)
                (.box 257 161)
              )
            )
          )
          (.splitA
            (.splitB
              (.splitA
                (.box 185 81)
                (.box 145 81)
              )
              (.splitA
                (.box 177 113)
                (.box 145 113)
              )
            )
            (.splitB
              (.box 225 81)
              (.box 193 113)
            )
          )
        )
      )
    )
    (.splitB
      (.splitA
        (.splitB
          (.splitA
            (.box 193 97)
            (.box 161 97)
          )
          (.splitA
            (.splitB
              (.box 193 161)
              (.box 257 193)
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
          (.splitB
            (.splitA
              (.box 257 193)
              (.box 161 193)
            )
            (.box 193 161)
          )
          (.box 193 97)
        )
        (.box 97 129)
      )
    )
  )

theorem f2Archived1Chart1_ok : checkChart f2Archived1 1 0 2 f2Archived1Chart1 = true := by decide +kernel

def f2Archived1Chart2 : RowTree :=
  (.splitA
    (.splitB
      (.splitA
        (.splitB
          (.box 97 75)
          (.splitA
            (.box 113 193)
            (.splitB
              (.box 81 161)
              (.box 81 257)
            )
          )
        )
        (.splitB
          (.splitA
            (.box 161 97)
            (.box 193 97)
          )
          (.splitA
            (.splitB
              (.box 161 161)
              (.splitA
                (.box 177 193)
                (.box 145 257)
              )
            )
            (.splitA
              (.splitB
                (.box 225 161)
                (.box 225 257)
              )
              (.splitB
                (.box 257 161)
                (.box 257 193)
              )
            )
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
                (.splitB
                  (.box 105 145)
                  (.box 105 177)
                )
              )
            )
            (.splitB
              (.splitB
                (.box 81 257)
                (.splitA
                  (.box 89 225)
                  (.box 73 225)
                )
              )
              (.splitA
                (.splitB
                  (.box 89 145)
                  (.box 89 177)
                )
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
                  (.box 120 76)
                  (.splitA
                    (.box 123 92)
                    (.splitB
                      (.box 117 88)
                      (.box 117 95)
                    )
                  )
                )
                (.splitB
                  (.splitA
                    (.box 109 76)
                    (.box 101 76)
                  )
                  (.splitA
                    (.splitB
                      (.box 109 87)
                      (.box 109 95)
                    )
                    (.splitB
                      (.box 101 87)
                      (.box 101 95)
                    )
                  )
                )
              )
              (.splitA
                (.splitB
                  (.splitA
                    (.splitB
                      (.splitA
                        (.box 126 103)
                        (.box 122 103)
                      )
                      (.splitA
                        (.splitB
                          (.box 126 110)
                          (.box 126 111)
                        )
                        (.splitB
                          (.box 123 108)
                          (.box 123 112)
                        )
                      )
                    )
                    (.splitB
                      (.splitA
                        (.box 119 103)
                        (.box 115 103)
                      )
                      (.splitA
                        (.splitB
                          (.box 119 108)
                          (.box 119 112)
                        )
                        (.splitB
                          (.box 115 108)
                          (.box 115 112)
                        )
                      )
                    )
                  )
                  (.splitA
                    (.splitB
                      (.splitA
                        (.splitB
                          (.splitA
                            (.box 128 116)
                            (.box 126 116)
                          )
                          (.box 127 120)
                        )
                        (.splitB
                          (.splitA
                            (.box 124 116)
                            (.box 122 116)
                          )
                          (.box 123 120)
                        )
                      )
                      (.splitA
                        (.splitB
                          (.box 127 123)
                          (.splitA
                            (.box 128 127)
                            (.box 126 127)
                          )
                        )
                        (.splitB
                          (.box 123 123)
                          (.box 123 127)
                        )
                      )
                    )
                    (.splitB
                      (.splitA
                        (.splitB
                          (.splitA
                            (.box 120 116)
                            (.box 118 115)
                          )
                          (.box 119 119)
                        )
                        (.splitB
                          (.box 116 115)
                          (.box 116 119)
                        )
                      )
                      (.splitA
                        (.splitB
                          (.box 120 123)
                          (.box 120 126)
                        )
                        (.splitB
                          (.box 116 123)
                          (.box 116 126)
                        )
                      )
                    )
                  )
                )
                (.splitB
                  (.splitA
                    (.splitB
                      (.splitA
                        (.box 111 103)
                        (.box 108 101)
                      )
                      (.splitA
                        (.box 112 109)
                        (.box 108 109)
                      )
                    )
                    (.splitB
                      (.box 103 101)
                      (.box 103 109)
                    )
                  )
                  (.splitA
                    (.splitB
                      (.splitA
                        (.box 112 117)
                        (.box 108 117)
                      )
                      (.splitA
                        (.box 112 123)
                        (.box 108 123)
                      )
                    )
                    (.splitB
                      (.box 103 117)
                      (.box 103 123)
                    )
                  )
                )
              )
            )
            (.splitB
              (.splitA
                (.splitB
                  (.splitA
                    (.box 93 76)
                    (.box 87 73)
                  )
                  (.splitA
                    (.box 95 89)
                    (.box 87 89)
                  )
                )
                (.splitB
                  (.box 76 73)
                  (.box 76 89)
                )
              )
              (.splitA
                (.splitB
                  (.splitA
                    (.box 95 105)
                    (.box 87 105)
                  )
                  (.splitA
                    (.box 96 118)
                    (.box 88 118)
                  )
                )
                (.splitB
                  (.box 76 105)
                  (.box 76 118)
                )
              )
            )
          )
        )
        (.splitB
          (.splitA
            (.splitB
              (.splitB
                (.splitA
                  (.box 177 257)
                  (.box 145 257)
                )
                (.splitA
                  (.box 177 225)
                  (.box 145 225)
                )
              )
              (.splitA
                (.splitB
                  (.box 177 145)
                  (.box 177 177)
                )
                (.box 145 161)
              )
            )
            (.splitB
              (.splitA
                (.splitB
                  (.box 225 257)
                  (.box 225 225)
                )
                (.box 257 193)
              )
              (.splitA
                (.box 225 161)
                (.box 257 161)
              )
            )
          )
          (.splitA
            (.splitB
              (.splitA
                (.box 185 81)
                (.box 145 81)
              )
              (.splitA
                (.box 177 113)
                (.box 145 113)
              )
            )
            (.splitB
              (.box 225 81)
              (.box 193 113)
            )
          )
        )
      )
    )
    (.splitB
      (.splitA
        (.splitB
          (.splitA
            (.box 193 97)
            (.box 161 97)
          )
          (.splitA
            (.splitB
              (.box 193 161)
              (.box 257 193)
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
          (.splitB
            (.splitA
              (.box 257 193)
              (.box 161 193)
            )
            (.box 193 161)
          )
          (.box 193 97)
        )
        (.box 97 129)
      )
    )
  )

theorem f2Archived1Chart2_ok : checkChart f2Archived1 2 0 1 f2Archived1Chart2 = true := by decide +kernel

end HlawkaSchatten.BelowExponent.FacetNumeric
