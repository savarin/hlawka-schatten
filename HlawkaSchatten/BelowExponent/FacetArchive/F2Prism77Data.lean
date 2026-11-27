/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.FacetNumeric

/-! Archived facet prism certificate data: `F2Prism77Data`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true

@[expose] public section

namespace HlawkaSchatten.BelowExponent.FacetNumeric

def f2Archived77 : Prism := {
  vertices := [⟨81600, 36800, 9600, 0⟩,
    ⟨76400, 42800, 8800, 0⟩,
    ⟨74400, 47200, 6400, 0⟩,
    ⟨81396, 36708, 9576, 320⟩,
    ⟨76209, 42693, 8778, 320⟩,
    ⟨74214, 47082, 6384, 320⟩]
  profileDen := 128000
  pi := [59541700, 82299124, 397230570, 534670430]
  slope := [155413952, -90141549, -69673370]
  radiusNum := 1
  radiusDen := 8
}

set_option maxRecDepth 40000
set_option maxHeartbeats 0

theorem f2Archived77_data_ok : dataOK f2Archived77 = true := by decide +kernel

def f2Archived77Chart0 : RowTree :=
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
                          (.splitA
                            (.splitB
                              (.box 128 128)
                              (.box 128 126)
                            )
                            (.box 127 127)
                          )
                          (.splitA
                            (.splitB
                              (.box 128 124)
                              (.box 128 122)
                            )
                            (.box 127 123)
                          )
                        )
                        (.box 125 125)
                      )
                      (.splitA
                        (.splitB
                          (.splitA
                            (.box 128 120)
                            (.box 127 120)
                          )
                          (.splitA
                            (.box 128 116)
                            (.box 127 116)
                          )
                        )
                        (.box 125 117)
                      )
                    )
                    (.box 121 121)
                  )
                  (.splitA
                    (.splitB
                      (.splitA
                        (.splitB
                          (.box 128 111)
                          (.box 128 110)
                        )
                        (.box 125 111)
                      )
                      (.box 126 103)
                    )
                    (.box 121 105)
                  )
                )
                (.box 113 113)
              )
              (.splitA
                (.splitB
                  (.splitA
                    (.box 126 92)
                    (.box 121 92)
                  )
                  (.box 124 76)
                )
                (.box 113 81)
              )
            )
            (.box 97 97)
          )
          (.splitA
            (.splitB
              (.splitA
                (.splitB
                  (.box 121 177)
                  (.box 121 145)
                )
                (.box 105 161)
              )
              (.splitA
                (.box 121 193)
                (.box 105 193)
              )
            )
            (.splitB
              (.box 81 161)
              (.box 81 193)
            )
          )
        )
        (.splitB
          (.box 65 97)
          (.box 161 129)
        )
      )
      (.splitA
        (.splitA
          (.splitB
            (.box 113 193)
            (.box 113 75)
          )
          (.splitB
            (.box 81 193)
            (.box 92 75)
          )
        )
        (.box 161 129)
      )
    )
    (.splitB
      (.box 0 65)
      (.box 0 65)
    )
  )

theorem f2Archived77Chart0_ok : checkChart f2Archived77 0 1 2 f2Archived77Chart0 = true := by decide +kernel

def f2Archived77Chart1 : RowTree :=
  (.splitA
    (.splitB
      (.splitA
        (.splitA
          (.splitB
            (.box 113 75)
            (.box 113 193)
          )
          (.splitB
            (.box 92 75)
            (.box 81 193)
          )
        )
        (.box 65 129)
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
                (.box 105 162)
              )
            )
            (.splitB
              (.box 81 193)
              (.box 81 161)
            )
          )
          (.splitA
            (.splitB
              (.splitA
                (.splitB
                  (.splitA
                    (.box 125 76)
                    (.box 121 76)
                  )
                  (.splitA
                    (.splitA
                      (.box 127 92)
                      (.box 124 92)
                    )
                    (.box 121 92)
                  )
                )
                (.box 113 81)
              )
              (.splitA
                (.splitB
                  (.splitA
                    (.splitB
                      (.box 126 103)
                      (.splitA
                        (.splitA
                          (.box 128 111)
                          (.box 127 111)
                        )
                        (.box 125 111)
                      )
                    )
                    (.box 121 105)
                  )
                  (.splitA
                    (.splitB
                      (.splitA
                        (.splitB
                          (.splitA
                            (.box 128 116)
                            (.box 127 116)
                          )
                          (.splitA
                            (.box 128 120)
                            (.box 127 120)
                          )
                        )
                        (.box 125 117)
                      )
                      (.splitA
                        (.splitB
                          (.splitA
                            (.splitB
                              (.box 128 122)
                              (.box 128 124)
                            )
                            (.box 127 123)
                          )
                          (.splitA
                            (.splitB
                              (.box 128 126)
                              (.box 128 128)
                            )
                            (.box 127 127)
                          )
                        )
                        (.box 125 125)
                      )
                    )
                    (.box 121 121)
                  )
                )
                (.box 113 113)
              )
            )
            (.box 97 97)
          )
        )
        (.splitB
          (.box 65 129)
          (.box 65 97)
        )
      )
    )
    (.splitB
      (.box 0 7)
      (.box 0 7)
    )
  )

theorem f2Archived77Chart1_ok : checkChart f2Archived77 1 0 2 f2Archived77Chart1 = true := by decide +kernel

def f2Archived77Chart2 : RowTree :=
  (.splitA
    (.splitB
      (.splitA
        (.box 65 129)
        (.splitB
          (.box 0 65)
          (.splitB
            (.box 193 161)
            (.splitA
              (.box 161 193)
              (.splitA
                (.box 225 257)
                (.splitB
                  (.box 257 225)
                  (.splitA
                    (.box 257 321)
                    (.splitA
                      (.splitB
                        (.box 353 289)
                        (.splitB
                          (.box 353 353)
                          (.box 321 449)
                        )
                      )
                      (.splitB
                        (.box 385 289)
                        (.splitB
                          (.box 385 353)
                          (.splitA
                            (.splitB
                              (.box 417 417)
                              (.splitA
                                (.box 417 513)
                                (.splitB
                                  (.box 401 481)
                                  (.box 394 577)
                                )
                              )
                            )
                            (.splitB
                              (.box 449 417)
                              (.splitA
                                (.splitB
                                  (.box 481 481)
                                  (.box 385 577)
                                )
                                (.box 513 513)
                              )
                            )
                          )
                        )
                      )
                    )
                  )
                )
              )
            )
          )
        )
      )
      (.splitA
        (.splitB
          (.splitA
            (.box 97 161)
            (.splitB
              (.box 81 129)
              (.splitA
                (.box 89 177)
                (.splitB
                  (.box 73 145)
                  (.box 69 185)
                )
              )
            )
          )
          (.splitA
            (.splitB
              (.splitA
                (.box 113 92)
                (.splitB
                  (.box 97 81)
                  (.splitA
                    (.box 105 95)
                    (.splitB
                      (.box 97 89)
                      (.box 99 95)
                    )
                  )
                )
              )
              (.splitA
                (.splitB
                  (.splitA
                    (.box 121 111)
                    (.splitB
                      (.box 113 105)
                      (.splitA
                        (.box 117 112)
                        (.splitB
                          (.box 113 109)
                          (.box 114 112)
                        )
                      )
                    )
                  )
                  (.splitA
                    (.splitB
                      (.splitA
                        (.box 125 120)
                        (.splitB
                          (.box 121 117)
                          (.splitA
                            (.box 123 120)
                            (.splitB
                              (.box 122 119)
                              (.box 122 120)
                            )
                          )
                        )
                      )
                      (.splitA
                        (.splitB
                          (.splitA
                            (.box 127 124)
                            (.splitB
                              (.box 125 123)
                              (.box 126 124)
                            )
                          )
                          (.splitA
                            (.splitB
                              (.splitA
                                (.box 128 126)
                                (.splitB
                                  (.box 128 126)
                                  (.box 128 127)
                                )
                              )
                              (.splitA
                                (.splitB
                                  (.box 128 128)
                                  (.box 1 128)
                                )
                                (.splitB
                                  (.box 128 127)
                                  (.box 128 128)
                                )
                              )
                            )
                            (.splitB
                              (.splitA
                                (.box 127 126)
                                (.box 126 126)
                              )
                              (.splitA
                                (.box 127 128)
                                (.box 126 128)
                              )
                            )
                          )
                        )
                        (.splitB
                          (.splitA
                            (.splitB
                              (.box 124 122)
                              (.box 124 124)
                            )
                            (.splitB
                              (.box 122 122)
                              (.box 122 124)
                            )
                          )
                          (.splitA
                            (.splitB
                              (.box 124 126)
                              (.box 124 127)
                            )
                            (.box 123 126)
                          )
                        )
                      )
                    )
                    (.splitB
                      (.splitA
                        (.splitB
                          (.splitB
                            (.box 118 115)
                            (.box 118 117)
                          )
                          (.splitA
                            (.splitB
                              (.box 120 118)
                              (.box 120 120)
                            )
                            (.box 118 119)
                          )
                        )
                        (.splitB
                          (.splitA
                            (.splitB
                              (.box 116 115)
                              (.box 116 116)
                            )
                            (.box 114 115)
                          )
                          (.splitA
                            (.box 117 118)
                            (.box 115 118)
                          )
                        )
                      )
                      (.splitA
                        (.splitB
                          (.splitA
                            (.box 121 122)
                            (.box 120 122)
                          )
                          (.box 121 125)
                        )
                        (.box 117 122)
                      )
                    )
                  )
                )
                (.splitB
                  (.splitA
                    (.splitB
                      (.splitA
                        (.box 109 104)
                        (.box 107 103)
                      )
                      (.splitA
                        (.splitB
                          (.box 110 108)
                          (.splitB
                            (.box 111 110)
                            (.box 112 112)
                          )
                        )
                        (.splitB
                          (.box 107 108)
                          (.box 108 110)
                        )
                      )
                    )
                    (.splitB
                      (.splitA
                        (.splitB
                          (.box 102 100)
                          (.box 103 104)
                        )
                        (.box 99 101)
                      )
                      (.splitA
                        (.box 104 108)
                        (.box 101 106)
                      )
                    )
                  )
                  (.splitB
                    (.splitA
                      (.splitB
                        (.splitA
                          (.box 112 114)
                          (.box 109 113)
                        )
                        (.box 112 117)
                      )
                      (.box 105 113)
                    )
                    (.box 111 121)
                  )
                )
              )
            )
            (.splitB
              (.splitA
                (.splitB
                  (.splitA
                    (.box 89 79)
                    (.box 83 76)
                  )
                  (.splitA
                    (.splitB
                      (.box 91 88)
                      (.splitB
                        (.box 93 92)
                        (.box 95 94)
                      )
                    )
                    (.splitB
                      (.box 85 86)
                      (.box 87 91)
                    )
                  )
                )
                (.splitB
                  (.splitA
                    (.splitB
                      (.box 75 72)
                      (.box 77 79)
                    )
                    (.box 69 73)
                  )
                  (.splitA
                    (.box 80 86)
                    (.box 73 83)
                  )
                )
              )
              (.splitB
                (.splitA
                  (.splitB
                    (.splitA
                      (.box 95 99)
                      (.box 89 97)
                    )
                    (.box 95 105)
                  )
                  (.box 81 97)
                )
                (.box 92 113)
              )
            )
          )
        )
        (.splitB
          (.splitA
            (.splitB
              (.splitB
                (.box 161 193)
                (.splitA
                  (.box 177 225)
                  (.box 145 225)
                )
              )
              (.splitA
                (.splitB
                  (.box 177 153)
                  (.splitA
                    (.box 185 177)
                    (.box 169 177)
                  )
                )
                (.splitB
                  (.splitB
                    (.box 145 137)
                    (.box 145 153)
                  )
                  (.box 145 169)
                )
              )
            )
            (.splitB
              (.splitA
                (.splitB
                  (.box 225 257)
                  (.box 225 225)
                )
                (.splitB
                  (.splitB
                    (.splitA
                      (.box 289 385)
                      (.splitA
                        (.splitB
                          (.box 321 449)
                          (.box 353 353)
                        )
                        (.splitB
                          (.splitA
                            (.splitB
                              (.splitA
                                (.box 433 0)
                                (.box 401 0)
                              )
                              (.box 417 417)
                            )
                            (.splitB
                              (.box 481 0)
                              (.box 449 417)
                            )
                          )
                          (.box 385 353)
                        )
                      )
                    )
                    (.box 257 289)
                  )
                  (.box 257 225)
                )
              )
              (.splitA
                (.box 241 146)
                (.box 257 129)
              )
            )
          )
          (.splitA
            (.splitB
              (.splitB
                (.splitA
                  (.box 185 73)
                  (.box 145 73)
                )
                (.box 177 89)
              )
              (.box 65 97)
            )
            (.box 193 80)
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
              (.splitA
                (.splitB
                  (.box 257 225)
                  (.splitA
                    (.splitB
                      (.box 321 289)
                      (.splitA
                        (.splitB
                          (.box 385 353)
                          (.box 0 449)
                        )
                        (.box 353 321)
                      )
                    )
                    (.box 289 257)
                  )
                )
                (.box 225 193)
              )
            )
            (.splitB
              (.box 161 161)
              (.box 161 193)
            )
          )
        )
        (.splitB
          (.splitA
            (.box 87 84)
            (.box 107 97)
          )
          (.box 81 161)
        )
      )
      (.splitA
        (.splitB
          (.splitA
            (.splitB
              (.splitB
                (.splitA
                  (.splitA
                    (.splitB
                      (.splitA
                        (.splitB
                          (.box 0 0)
                          (.box 385 353)
                        )
                        (.box 0 0)
                      )
                      (.box 321 289)
                    )
                    (.box 289 257)
                  )
                  (.box 225 257)
                )
                (.box 193 193)
              )
              (.box 193 161)
            )
            (.box 161 0)
          )
          (.box 0 65)
        )
        (.box 97 129)
      )
    )
  )

theorem f2Archived77Chart2_ok : checkChart f2Archived77 2 0 1 f2Archived77Chart2 = true := by decide +kernel

end HlawkaSchatten.BelowExponent.FacetNumeric
