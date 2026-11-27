/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.FacetNumeric

/-! Archived facet prism certificate data: `F2Prism39Data`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true

@[expose] public section

namespace HlawkaSchatten.BelowExponent.FacetNumeric

def f2Archived39 : Prism := {
  vertices := [⟨380800, 92800, 38400, 0⟩,
    ⟨380000, 100000, 32000, 0⟩,
    ⟨386800, 93200, 32000, 0⟩,
    ⟨379848, 92568, 38304, 1280⟩,
    ⟨379050, 99750, 31920, 1280⟩,
    ⟨385833, 92967, 31920, 1280⟩]
  profileDen := 512000
  pi := [78619143, 242942972, 226362856, 525816853]
  slope := [379816672, -118419383, -283505409]
  radiusNum := 1
  radiusDen := 8
}

set_option maxRecDepth 40000
set_option maxHeartbeats 0

theorem f2Archived39_data_ok : dataOK f2Archived39 = true := by decide +kernel

def f2Archived39Chart0 : RowTree :=
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
                        (.box 126 123)
                      )
                      (.splitA
                        (.box 121 125)
                        (.box 117 125)
                      )
                    )
                    (.splitA
                      (.splitB
                        (.box 125 120)
                        (.splitA
                          (.box 126 116)
                          (.box 125 116)
                        )
                      )
                      (.splitB
                        (.box 119 120)
                        (.box 119 116)
                      )
                    )
                  )
                  (.splitB
                    (.box 111 123)
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
                (.box 92 118)
                (.box 87 105)
              )
            )
            (.splitA
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
              (.splitB
                (.box 87 92)
                (.box 87 73)
              )
            )
          )
          (.splitA
            (.splitB
              (.box 161 113)
              (.box 161 81)
            )
            (.box 129 81)
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
                (.box 81 210)
                (.box 65 289)
              )
            )
          )
          (.splitB
            (.splitA
              (.splitA
                (.box 185 146)
                (.box 145 145)
              )
              (.box 225 145)
            )
            (.splitA
              (.splitB
                (.splitA
                  (.box 169 209)
                  (.splitA
                    (.splitB
                      (.box 153 241)
                      (.box 153 201)
                    )
                    (.splitB
                      (.box 137 241)
                      (.splitA
                        (.box 141 201)
                        (.box 133 201)
                      )
                    )
                  )
                )
                (.splitA
                  (.splitB
                    (.box 161 289)
                    (.box 177 257)
                  )
                  (.splitB
                    (.splitA
                      (.splitB
                        (.box 145 305)
                        (.box 153 289)
                      )
                      (.splitB
                        (.splitA
                          (.box 141 305)
                          (.box 133 305)
                        )
                        (.box 137 281)
                      )
                    )
                    (.splitA
                      (.box 153 257)
                      (.box 137 257)
                    )
                  )
                )
              )
              (.splitB
                (.splitA
                  (.splitB
                    (.box 225 225)
                    (.splitA
                      (.box 249 201)
                      (.box 209 209)
                    )
                  )
                  (.box 257 225)
                )
                (.splitA
                  (.splitB
                    (.splitA
                      (.splitB
                        (.box 249 305)
                        (.box 129 282)
                      )
                      (.box 209 289)
                    )
                    (.box 241 257)
                  )
                  (.box 193 257)
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
              (.splitA
                (.box 177 0)
                (.box 145 0)
              )
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
        (.box 129 81)
        (.splitB
          (.splitA
            (.box 0 161)
            (.box 97 161)
          )
          (.splitA
            (.box 0 193)
            (.box 97 193)
          )
        )
      )
      (.splitB
        (.splitA
          (.box 0 193)
          (.box 97 129)
        )
        (.box 65 97)
      )
    )
  )

theorem f2Archived39Chart0_ok : checkChart f2Archived39 0 1 2 f2Archived39Chart0 = true := by decide +kernel

def f2Archived39Chart1 : RowTree :=
  (.splitA
    (.splitB
      (.splitA
        (.splitB
          (.box 84 75)
          (.splitA
            (.box 113 193)
            (.box 73 193)
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
              (.box 225 193)
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
                (.box 105 176)
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
                    (.box 123 92)
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
                        (.box 126 111)
                        (.box 123 111)
                      )
                    )
                    (.splitB
                      (.box 119 103)
                      (.splitA
                        (.box 120 111)
                        (.box 116 111)
                      )
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
                          (.box 124 119)
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
                        (.box 118 115)
                        (.splitA
                          (.box 119 119)
                          (.box 118 119)
                        )
                      )
                      (.splitA
                        (.box 120 125)
                        (.box 117 125)
                      )
                    )
                  )
                )
                (.splitB
                  (.splitB
                    (.box 108 101)
                    (.box 108 109)
                  )
                  (.splitB
                    (.box 108 117)
                    (.box 108 125)
                  )
                )
              )
            )
            (.splitB
              (.splitB
                (.box 87 73)
                (.box 87 90)
              )
              (.splitB
                (.box 88 105)
                (.box 87 121)
              )
            )
          )
        )
        (.splitB
          (.splitA
            (.splitB
              (.splitB
                (.box 161 257)
                (.box 161 225)
              )
              (.box 161 161)
            )
            (.splitB
              (.box 225 193)
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
          (.box 0 65)
          (.box 193 193)
        )
        (.box 97 65)
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

theorem f2Archived39Chart1_ok : checkChart f2Archived39 1 0 2 f2Archived39Chart1 = true := by decide +kernel

def f2Archived39Chart2 : RowTree :=
  (.splitA
    (.splitB
      (.splitA
        (.box 82 129)
        (.splitA
          (.splitB
            (.box 161 97)
            (.box 161 193)
          )
          (.splitB
            (.box 0 65)
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
                      (.splitA
                        (.splitB
                          (.box 126 117)
                          (.box 126 120)
                        )
                        (.splitB
                          (.box 122 117)
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
                        (.box 116 123)
                      )
                    )
                  )
                )
                (.splitB
                  (.splitA
                    (.splitB
                      (.box 109 103)
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
                      (.box 112 122)
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
                  (.box 95 115)
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
            (.splitB
              (.box 193 193)
              (.box 193 161)
            )
            (.box 161 129)
          )
          (.box 0 75)
        )
        (.box 97 129)
      )
    )
  )

theorem f2Archived39Chart2_ok : checkChart f2Archived39 2 0 1 f2Archived39Chart2 = true := by decide +kernel

end HlawkaSchatten.BelowExponent.FacetNumeric
