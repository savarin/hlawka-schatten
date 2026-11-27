/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.FacetNumeric

/-! Archived facet prism certificate data: `F2Prism8Data`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true

@[expose] public section

namespace HlawkaSchatten.BelowExponent.FacetNumeric

def f2Archived8 : Prism := {
  vertices := [⟨434400, 45600, 32000, 0⟩,
    ⟨433600, 52800, 25600, 0⟩,
    ⟨440400, 46000, 25600, 0⟩,
    ⟨433314, 45486, 31920, 1280⟩,
    ⟨432516, 52668, 25536, 1280⟩,
    ⟨439299, 45885, 25536, 1280⟩]
  profileDen := 512000
  pi := [41991483, 253188263, 249128547, 529433531]
  slope := [471516939, -217221799, -269169905]
  radiusNum := 1
  radiusDen := 8
}

set_option maxRecDepth 40000
set_option maxHeartbeats 0

theorem f2Archived8_data_ok : dataOK f2Archived8 = true := by decide +kernel

def f2Archived8Chart0 : RowTree :=
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
                        (.splitA
                          (.box 127 124)
                          (.box 124 123)
                        )
                      )
                      (.splitA
                        (.box 120 125)
                        (.box 117 125)
                      )
                    )
                    (.splitA
                      (.splitB
                        (.splitA
                          (.box 126 120)
                          (.box 125 120)
                        )
                        (.splitA
                          (.box 127 116)
                          (.box 124 116)
                        )
                      )
                      (.splitB
                        (.splitA
                          (.box 119 120)
                          (.box 118 120)
                        )
                        (.box 119 116)
                      )
                    )
                  )
                  (.splitB
                    (.splitA
                      (.box 112 125)
                      (.box 104 125)
                    )
                    (.splitA
                      (.box 112 117)
                      (.box 104 117)
                    )
                  )
                )
                (.splitA
                  (.splitB
                    (.splitA
                      (.splitA
                        (.box 126 111)
                        (.box 125 110)
                      )
                      (.box 119 110)
                    )
                    (.splitA
                      (.box 125 103)
                      (.box 119 103)
                    )
                  )
                  (.splitB
                    (.box 108 109)
                    (.box 108 103)
                  )
                )
              )
              (.splitB
                (.splitA
                  (.box 95 121)
                  (.box 79 121)
                )
                (.splitA
                  (.box 95 105)
                  (.box 79 105)
                )
              )
            )
            (.splitA
              (.splitB
                (.splitA
                  (.box 121 92)
                  (.box 105 92)
                )
                (.splitA
                  (.box 121 76)
                  (.box 105 76)
                )
              )
              (.splitB
                (.splitA
                  (.box 92 92)
                  (.box 79 89)
                )
                (.splitA
                  (.box 92 76)
                  (.box 76 76)
                )
              )
            )
          )
          (.splitA
            (.splitB
              (.box 161 112)
              (.splitA
                (.box 177 81)
                (.box 145 81)
              )
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
              (.splitB
                (.box 113 177)
                (.box 113 145)
              )
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
          (.splitB
            (.splitA
              (.splitB
                (.box 161 177)
                (.splitA
                  (.box 177 145)
                  (.box 145 145)
                )
              )
              (.splitB
                (.box 193 161)
                (.box 225 137)
              )
            )
            (.splitA
              (.splitB
                (.splitA
                  (.box 177 225)
                  (.box 145 225)
                )
                (.splitA
                  (.box 177 257)
                  (.box 145 257)
                )
              )
              (.splitB
                (.splitA
                  (.box 225 225)
                  (.box 257 225)
                )
                (.box 225 289)
              )
            )
          )
        )
      )
      (.splitA
        (.splitB
          (.splitB
            (.splitA
              (.box 107 0)
              (.box 81 257)
            )
            (.box 97 161)
          )
          (.box 97 75)
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
          (.box 193 97)
          (.box 65 84)
        )
        (.splitA
          (.splitB
            (.box 193 161)
            (.box 193 193)
          )
          (.box 97 129)
        )
      )
      (.splitB
        (.splitA
          (.box 193 193)
          (.box 65 0)
        )
        (.box 65 65)
      )
    )
  )

theorem f2Archived8Chart0_ok : checkChart f2Archived8 0 1 2 f2Archived8Chart0 = true := by decide +kernel

def f2Archived8Chart1 : RowTree :=
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
          (.box 129 65)
          (.splitA
            (.splitB
              (.box 161 161)
              (.splitA
                (.box 177 257)
                (.box 145 257)
              )
            )
            (.splitB
              (.box 193 161)
              (.splitA
                (.box 225 193)
                (.box 257 193)
              )
            )
          )
        )
      )
      (.splitA
        (.splitB
          (.splitB
            (.splitA
              (.splitA
                (.box 121 193)
                (.box 105 193)
              )
              (.splitB
                (.box 81 257)
                (.box 81 225)
              )
            )
            (.splitA
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
                  (.box 121 76)
                  (.splitA
                    (.box 123 92)
                    (.splitB
                      (.box 117 88)
                      (.box 117 95)
                    )
                  )
                )
                (.splitB
                  (.box 105 76)
                  (.splitA
                    (.splitB
                      (.box 109 88)
                      (.box 109 95)
                    )
                    (.box 103 89)
                  )
                )
              )
              (.splitA
                (.splitB
                  (.splitA
                    (.splitB
                      (.box 125 103)
                      (.splitA
                        (.box 127 110)
                        (.splitB
                          (.box 123 108)
                          (.box 123 112)
                        )
                      )
                    )
                    (.splitB
                      (.box 117 103)
                      (.splitA
                        (.splitB
                          (.box 119 108)
                          (.box 119 112)
                        )
                        (.box 116 109)
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
                        (.splitB
                          (.box 124 123)
                          (.box 124 127)
                        )
                      )
                    )
                    (.splitB
                      (.splitA
                        (.splitB
                          (.box 120 115)
                          (.box 120 119)
                        )
                        (.box 116 117)
                      )
                      (.splitA
                        (.box 120 125)
                        (.box 116 125)
                      )
                    )
                  )
                )
                (.splitB
                  (.splitA
                    (.splitB
                      (.box 111 101)
                      (.box 111 109)
                    )
                    (.box 103 105)
                  )
                  (.splitA
                    (.splitB
                      (.box 111 117)
                      (.box 111 125)
                    )
                    (.box 104 121)
                  )
                )
              )
            )
            (.splitB
              (.splitA
                (.splitB
                  (.box 92 73)
                  (.box 92 89)
                )
                (.box 76 81)
              )
              (.splitA
                (.splitB
                  (.box 92 105)
                  (.box 92 121)
                )
                (.box 79 113)
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
              (.box 177 81)
              (.box 177 113)
            )
            (.box 129 82)
          )
        )
      )
    )
    (.splitB
      (.splitA
        (.splitB
          (.box 129 65)
          (.splitA
            (.box 257 193)
            (.box 161 129)
          )
        )
        (.box 75 65)
      )
      (.splitB
        (.splitA
          (.splitA
            (.box 0 193)
            (.box 161 129)
          )
          (.box 75 0)
        )
        (.splitA
          (.box 129 82)
          (.box 65 75)
        )
      )
    )
  )

theorem f2Archived8Chart1_ok : checkChart f2Archived8 1 0 2 f2Archived8Chart1 = true := by decide +kernel

def f2Archived8Chart2 : RowTree :=
  (.splitA
    (.splitB
      (.splitA
        (.splitB
          (.box 84 65)
          (.splitA
            (.box 113 193)
            (.box 81 193)
          )
        )
        (.splitA
          (.splitB
            (.box 161 97)
            (.splitB
              (.box 161 161)
              (.box 161 257)
            )
          )
          (.splitB
            (.box 193 97)
            (.splitA
              (.box 225 193)
              (.box 257 193)
            )
          )
        )
      )
      (.splitA
        (.splitB
          (.splitA
            (.splitB
              (.box 113 193)
              (.splitA
                (.box 121 177)
                (.box 105 177)
              )
            )
            (.splitB
              (.splitA
                (.box 89 193)
                (.box 73 193)
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
                  (.box 118 79)
                  (.splitA
                    (.box 123 92)
                    (.box 115 92)
                  )
                )
                (.splitB
                  (.box 105 76)
                  (.splitA
                    (.splitB
                      (.box 109 88)
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
                      (.box 123 104)
                      (.splitA
                        (.box 126 111)
                        (.box 122 111)
                      )
                    )
                    (.splitB
                      (.box 117 103)
                      (.splitA
                        (.box 119 110)
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
                          (.box 126 116)
                          (.box 127 120)
                        )
                        (.splitB
                          (.box 123 116)
                          (.box 123 120)
                        )
                      )
                      (.splitA
                        (.splitB
                          (.box 127 123)
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
                          (.box 120 119)
                        )
                        (.splitB
                          (.box 116 115)
                          (.box 116 119)
                        )
                      )
                      (.splitA
                        (.splitB
                          (.box 120 122)
                          (.box 120 126)
                        )
                        (.splitB
                          (.box 116 122)
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
                        (.box 109 103)
                        (.box 109 102)
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
                      (.box 111 123)
                    )
                    (.splitB
                      (.box 103 115)
                      (.box 104 122)
                    )
                  )
                )
              )
            )
            (.splitB
              (.splitA
                (.splitB
                  (.box 89 76)
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
                    (.box 89 102)
                  )
                  (.box 92 118)
                )
                (.splitB
                  (.box 76 102)
                  (.box 79 115)
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
                (.box 225 193)
                (.box 257 193)
              )
              (.box 225 145)
            )
          )
          (.splitA
            (.splitB
              (.splitA
                (.box 185 81)
                (.box 145 81)
              )
              (.box 177 113)
            )
            (.box 225 82)
          )
        )
      )
    )
    (.splitB
      (.splitA
        (.splitB
          (.box 129 65)
          (.splitA
            (.splitB
              (.box 193 161)
              (.box 193 257)
            )
            (.box 161 129)
          )
        )
        (.splitB
          (.box 84 97)
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
          (.box 193 97)
        )
        (.box 97 129)
      )
    )
  )

theorem f2Archived8Chart2_ok : checkChart f2Archived8 2 0 1 f2Archived8Chart2 = true := by decide +kernel

end HlawkaSchatten.BelowExponent.FacetNumeric
