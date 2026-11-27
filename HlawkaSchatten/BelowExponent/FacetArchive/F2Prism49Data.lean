/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.FacetNumeric

/-! Archived facet prism certificate data: `F2Prism49Data`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true

@[expose] public section

namespace HlawkaSchatten.BelowExponent.FacetNumeric

def f2Archived49 : Prism := {
  vertices := [⟨98800, 18000, 11200, 0⟩,
    ⟨95200, 23200, 9600, 0⟩,
    ⟨98400, 21600, 8000, 0⟩,
    ⟨98553, 17955, 11172, 320⟩,
    ⟨94962, 23142, 9576, 320⟩,
    ⟨98154, 21546, 7980, 320⟩]
  profileDen := 128000
  pi := [74601280, 249559831, 224013578, 525567135]
  slope := [393317644, -141713179, -274212023]
  radiusNum := 1
  radiusDen := 8
}

set_option maxRecDepth 40000
set_option maxHeartbeats 0

theorem f2Archived49_data_ok : dataOK f2Archived49 = true := by decide +kernel

def f2Archived49Chart0 : RowTree :=
  (.splitA
    (.splitB
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
                          (.box 127 127)
                          (.box 124 127)
                        )
                        (.box 125 124)
                      )
                      (.splitA
                        (.box 120 125)
                        (.box 117 125)
                      )
                    )
                    (.splitA
                      (.splitB
                        (.box 125 120)
                        (.box 125 116)
                      )
                      (.splitB
                        (.box 119 120)
                        (.box 119 116)
                      )
                    )
                  )
                  (.splitB
                    (.box 108 125)
                    (.box 108 117)
                  )
                )
                (.splitA
                  (.splitB
                    (.splitA
                      (.box 125 111)
                      (.box 119 111)
                    )
                    (.box 121 104)
                  )
                  (.splitB
                    (.box 108 111)
                    (.box 108 103)
                  )
                )
              )
              (.splitB
                (.box 87 121)
                (.box 87 105)
              )
            )
            (.splitA
              (.splitB
                (.splitA
                  (.box 121 92)
                  (.box 108 92)
                )
                (.box 113 76)
              )
              (.splitB
                (.box 87 89)
                (.box 87 73)
              )
            )
          )
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
        )
        (.splitA
          (.splitB
            (.splitA
              (.splitA
                (.box 121 161)
                (.box 105 161)
              )
              (.splitB
                (.box 81 177)
                (.box 81 145)
              )
            )
            (.splitA
              (.box 113 193)
              (.splitB
                (.box 81 224)
                (.box 81 289)
              )
            )
          )
          (.splitB
            (.splitA
              (.splitA
                (.splitB
                  (.box 177 177)
                  (.box 177 145)
                )
                (.splitB
                  (.box 145 177)
                  (.box 145 137)
                )
              )
              (.splitA
                (.splitB
                  (.box 225 177)
                  (.box 225 137)
                )
                (.box 193 145)
              )
            )
            (.splitA
              (.splitB
                (.splitA
                  (.box 169 210)
                  (.splitB
                    (.splitA
                      (.box 153 241)
                      (.box 137 233)
                    )
                    (.splitA
                      (.box 153 202)
                      (.splitB
                        (.box 137 217)
                        (.splitA
                          (.box 141 201)
                          (.box 133 201)
                        )
                      )
                    )
                  )
                )
                (.splitA
                  (.splitA
                    (.box 185 257)
                    (.box 161 288)
                  )
                  (.splitA
                    (.splitB
                      (.box 146 304)
                      (.box 153 321)
                    )
                    (.splitB
                      (.splitA
                        (.splitB
                          (.box 141 305)
                          (.box 141 273)
                        )
                        (.splitB
                          (.box 133 305)
                          (.box 133 273)
                        )
                      )
                      (.box 137 257)
                    )
                  )
                )
              )
              (.splitB
                (.splitA
                  (.splitB
                    (.splitA
                      (.box 241 233)
                      (.box 209 233)
                    )
                    (.splitA
                      (.splitB
                        (.splitA
                          (.box 249 217)
                          (.box 233 217)
                        )
                        (.splitA
                          (.box 249 201)
                          (.box 233 201)
                        )
                      )
                      (.box 217 208)
                    )
                  )
                  (.splitB
                    (.box 193 241)
                    (.box 193 209)
                  )
                )
                (.splitA
                  (.splitA
                    (.splitB
                      (.splitA
                        (.splitB
                          (.box 249 305)
                          (.box 249 273)
                        )
                        (.box 233 304)
                      )
                      (.box 241 257)
                    )
                    (.splitB
                      (.box 209 306)
                      (.box 209 321)
                    )
                  )
                  (.box 193 289)
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
              (.box 75 0)
              (.box 81 161)
            )
          )
          (.box 84 75)
        )
        (.splitB
          (.splitA
            (.splitB
              (.box 161 0)
              (.box 161 161)
            )
            (.splitB
              (.box 225 0)
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
          (.box 0 81)
          (.box 97 97)
        )
        (.splitB
          (.splitA
            (.box 193 145)
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
      (.splitB
        (.splitA
          (.splitA
            (.box 0 193)
            (.box 161 129)
          )
          (.box 97 129)
        )
        (.box 65 97)
      )
    )
  )

theorem f2Archived49Chart0_ok : checkChart f2Archived49 0 1 2 f2Archived49Chart0 = true := by decide +kernel

def f2Archived49Chart1 : RowTree :=
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
            (.splitB
              (.box 161 161)
              (.box 161 257)
            )
            (.splitB
              (.box 193 161)
              (.box 225 257)
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
              (.splitA
                (.box 121 177)
                (.box 105 177)
              )
              (.splitA
                (.box 89 176)
                (.box 73 161)
              )
            )
          )
          (.splitA
            (.splitB
              (.splitB
                (.splitA
                  (.box 121 76)
                  (.box 105 76)
                )
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
              )
              (.splitA
                (.splitB
                  (.splitA
                    (.splitB
                      (.box 125 103)
                      (.splitA
                        (.box 127 111)
                        (.box 123 111)
                      )
                    )
                    (.splitB
                      (.box 117 103)
                      (.splitA
                        (.box 119 111)
                        (.box 116 111)
                      )
                    )
                  )
                  (.splitA
                    (.splitB
                      (.splitB
                        (.splitA
                          (.box 127 116)
                          (.box 123 116)
                        )
                        (.splitA
                          (.box 127 120)
                          (.box 123 120)
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
                      (.splitB
                        (.splitA
                          (.box 120 116)
                          (.box 116 116)
                        )
                        (.splitA
                          (.box 120 119)
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
                      (.box 103 103)
                    )
                    (.splitA
                      (.box 111 111)
                      (.box 104 109)
                    )
                  )
                  (.splitB
                    (.splitA
                      (.box 111 117)
                      (.box 104 117)
                    )
                    (.splitA
                      (.box 112 123)
                      (.box 105 123)
                    )
                  )
                )
              )
            )
            (.splitB
              (.splitA
                (.splitB
                  (.box 92 76)
                  (.box 92 92)
                )
                (.box 79 81)
              )
              (.splitB
                (.splitA
                  (.box 92 105)
                  (.box 81 102)
                )
                (.splitA
                  (.box 95 118)
                  (.box 81 118)
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
                (.box 161 225)
              )
              (.box 225 257)
            )
            (.splitA
              (.box 177 161)
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
        (.box 97 65)
      )
      (.splitB
        (.splitA
          (.box 193 193)
          (.box 75 0)
        )
        (.box 129 97)
      )
    )
  )

theorem f2Archived49Chart1_ok : checkChart f2Archived49 1 0 2 f2Archived49Chart1 = true := by decide +kernel

def f2Archived49Chart2 : RowTree :=
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
          (.splitA
            (.splitB
              (.box 113 193)
              (.box 113 177)
            )
            (.splitB
              (.box 81 193)
              (.splitA
                (.box 89 177)
                (.box 73 177)
              )
            )
          )
          (.splitA
            (.splitB
              (.splitA
                (.splitB
                  (.box 118 81)
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
                      (.box 123 105)
                      (.box 124 112)
                    )
                    (.splitB
                      (.box 117 104)
                      (.splitA
                        (.box 118 112)
                        (.box 115 111)
                      )
                    )
                  )
                  (.splitA
                    (.splitB
                      (.splitA
                        (.splitB
                          (.box 126 117)
                          (.box 126 120)
                        )
                        (.splitB
                          (.box 123 116)
                          (.box 123 120)
                        )
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
                          (.box 116 115)
                          (.box 116 119)
                        )
                      )
                      (.splitA
                        (.box 120 125)
                        (.box 116 124)
                      )
                    )
                  )
                )
                (.splitB
                  (.splitA
                    (.splitB
                      (.box 109 104)
                      (.box 110 110)
                    )
                    (.splitB
                      (.box 103 101)
                      (.box 103 109)
                    )
                  )
                  (.splitA
                    (.splitB
                      (.box 111 116)
                      (.box 111 123)
                    )
                    (.box 104 118)
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
              (.splitA
                (.splitB
                  (.box 92 105)
                  (.box 95 118)
                )
                (.box 79 107)
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
              (.splitA
                (.box 225 193)
                (.box 257 193)
              )
              (.box 193 161)
            )
          )
          (.splitA
            (.splitB
              (.splitA
                (.box 177 81)
                (.box 145 81)
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
            (.box 193 193)
            (.box 161 129)
          )
        )
        (.box 75 65)
      )
      (.splitA
        (.splitB
          (.splitA
            (.box 257 194)
            (.box 161 129)
          )
          (.box 0 75)
        )
        (.box 97 65)
      )
    )
  )

theorem f2Archived49Chart2_ok : checkChart f2Archived49 2 0 1 f2Archived49Chart2 = true := by decide +kernel

end HlawkaSchatten.BelowExponent.FacetNumeric
