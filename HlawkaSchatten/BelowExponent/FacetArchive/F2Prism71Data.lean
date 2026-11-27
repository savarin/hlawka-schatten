/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.FacetNumeric

/-! Archived facet prism certificate data: `F2Prism71Data`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true

@[expose] public section

namespace HlawkaSchatten.BelowExponent.FacetNumeric

def f2Archived71 : Prism := {
  vertices := [⟨253600, 231200, 27200, 0⟩,
    ⟨243200, 243200, 25600, 0⟩,
    ⟨250000, 236400, 25600, 0⟩,
    ⟨252966, 230622, 27132, 1280⟩,
    ⟨242592, 242592, 25536, 1280⟩,
    ⟨249375, 235809, 25536, 1280⟩]
  profileDen := 512000
  pi := [158118463, 163628656, 218672122, 533322583]
  slope := [234749993, 86177653, -328024308]
  radiusNum := 1
  radiusDen := 16
}

set_option maxRecDepth 40000
set_option maxHeartbeats 0

theorem f2Archived71_data_ok : dataOK f2Archived71 = true := by decide +kernel

def f2Archived71Chart0 : RowTree :=
  (.splitA
    (.splitB
      (.splitB
        (.splitA
          (.splitA
            (.splitB
              (.splitA
                (.splitB
                  (.splitB
                    (.splitA
                      (.splitB
                        (.splitA
                          (.splitB
                            (.splitA
                              (.box 128 128)
                              (.box 127 128)
                            )
                            (.splitA
                              (.box 128 126)
                              (.box 127 126)
                            )
                          )
                          (.box 124 127)
                        )
                        (.splitA
                          (.splitB
                            (.box 127 124)
                            (.splitA
                              (.box 128 122)
                              (.box 127 122)
                            )
                          )
                          (.box 124 123)
                        )
                      )
                      (.box 120 125)
                    )
                    (.splitA
                      (.splitA
                        (.splitB
                          (.splitA
                            (.box 128 120)
                            (.box 126 120)
                          )
                          (.box 127 116)
                        )
                        (.splitB
                          (.box 124 120)
                          (.box 124 116)
                        )
                      )
                      (.box 120 117)
                    )
                  )
                  (.splitB
                    (.splitA
                      (.splitA
                        (.box 127 111)
                        (.box 124 111)
                      )
                      (.box 119 111)
                    )
                    (.splitA
                      (.box 125 103)
                      (.box 119 103)
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
              (.splitB
                (.box 113 177)
                (.box 113 145)
              )
              (.box 89 161)
            )
            (.splitA
              (.box 113 193)
              (.splitB
                (.box 81 225)
                (.box 74 321)
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
                  (.splitB
                    (.box 177 257)
                    (.splitA
                      (.box 185 385)
                      (.splitB
                        (.box 169 321)
                        (.splitB
                          (.box 165 385)
                          (.box 165 481)
                        )
                      )
                    )
                  )
                )
                (.splitB
                  (.box 145 225)
                  (.splitA
                    (.splitB
                      (.box 153 289)
                      (.splitA
                        (.splitB
                          (.box 157 353)
                          (.splitB
                            (.splitA
                              (.box 159 385)
                              (.box 155 385)
                            )
                            (.splitA
                              (.box 159 481)
                              (.box 155 481)
                            )
                          )
                        )
                        (.splitB
                          (.box 149 353)
                          (.splitB
                            (.box 151 385)
                            (.box 151 481)
                          )
                        )
                      )
                    )
                    (.splitB
                      (.box 137 289)
                      (.splitB
                        (.box 137 353)
                        (.box 145 385)
                      )
                    )
                  )
                )
              )
              (.splitB
                (.box 193 193)
                (.splitB
                  (.box 225 289)
                  (.splitA
                    (.box 129 321)
                    (.box 257 321)
                  )
                )
              )
            )
          )
        )
      )
      (.splitA
        (.splitB
          (.splitB
            (.splitA
              (.box 113 193)
              (.splitA
                (.box 89 257)
                (.box 65 257)
              )
            )
            (.box 97 161)
          )
          (.box 97 75)
        )
        (.splitB
          (.splitA
            (.splitA
              (.splitB
                (.splitB
                  (.splitA
                    (.box 185 0)
                    (.box 169 0)
                  )
                  (.box 177 225)
                )
                (.box 177 161)
              )
              (.splitB
                (.splitB
                  (.splitA
                    (.box 153 0)
                    (.box 137 0)
                  )
                  (.box 145 225)
                )
                (.box 145 161)
              )
            )
            (.splitB
              (.splitB
                (.box 225 0)
                (.box 193 225)
              )
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

theorem f2Archived71Chart0_ok : checkChart f2Archived71 0 1 2 f2Archived71Chart0 = true := by decide +kernel

def f2Archived71Chart1 : RowTree :=
  (.splitA
    (.splitB
      (.splitA
        (.splitB
          (.box 97 75)
          (.splitB
            (.box 97 161)
            (.splitA
              (.box 113 193)
              (.splitA
                (.box 89 257)
                (.splitB
                  (.box 73 225)
                  (.box 70 0)
                )
              )
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
                  (.splitA
                    (.box 185 0)
                    (.box 165 0)
                  )
                )
              )
              (.splitB
                (.box 145 161)
                (.splitB
                  (.box 145 225)
                  (.splitA
                    (.splitA
                      (.box 157 0)
                      (.box 149 0)
                    )
                    (.box 137 0)
                  )
                )
              )
            )
            (.splitB
              (.box 193 161)
              (.splitA
                (.splitB
                  (.box 225 225)
                  (.box 225 0)
                )
                (.box 257 257)
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
                (.splitA
                  (.box 89 257)
                  (.box 73 321)
                )
                (.box 81 225)
              )
            )
            (.splitA
              (.splitB
                (.box 113 145)
                (.box 113 177)
              )
              (.box 89 161)
            )
          )
          (.splitB
            (.splitA
              (.splitA
                (.splitB
                  (.splitB
                    (.splitA
                      (.box 185 385)
                      (.splitB
                        (.splitB
                          (.splitA
                            (.box 173 449)
                            (.box 163 449)
                          )
                          (.splitA
                            (.box 173 417)
                            (.box 165 385)
                          )
                        )
                        (.box 169 321)
                      )
                    )
                    (.box 177 257)
                  )
                  (.box 177 225)
                )
                (.splitB
                  (.splitB
                    (.splitA
                      (.splitA
                        (.splitB
                          (.splitB
                            (.splitA
                              (.splitB
                                (.box 159 513)
                                (.box 159 481)
                              )
                              (.splitB
                                (.box 155 513)
                                (.box 155 481)
                              )
                            )
                            (.box 157 385)
                          )
                          (.box 157 353)
                        )
                        (.splitB
                          (.splitB
                            (.box 153 449)
                            (.box 149 385)
                          )
                          (.box 149 353)
                        )
                      )
                      (.box 145 385)
                    )
                    (.box 145 257)
                  )
                  (.box 145 225)
                )
              )
              (.splitB
                (.splitA
                  (.box 129 321)
                  (.box 257 257)
                )
                (.box 193 193)
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
                  (.splitA
                    (.box 125 92)
                    (.box 119 92)
                  )
                  (.box 108 92)
                )
              )
              (.splitA
                (.splitB
                  (.splitB
                    (.splitA
                      (.box 125 103)
                      (.box 119 103)
                    )
                    (.splitA
                      (.splitA
                        (.box 127 111)
                        (.box 124 111)
                      )
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
                        (.splitA
                          (.splitA
                            (.box 128 120)
                            (.box 126 120)
                          )
                          (.box 124 120)
                        )
                      )
                      (.splitA
                        (.splitB
                          (.splitB
                            (.splitA
                              (.box 128 122)
                              (.box 127 122)
                            )
                            (.box 127 124)
                          )
                          (.splitA
                            (.splitB
                              (.box 128 126)
                              (.box 128 128)
                            )
                            (.box 127 127)
                          )
                        )
                        (.splitB
                          (.box 124 123)
                          (.box 124 127)
                        )
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

theorem f2Archived71Chart1_ok : checkChart f2Archived71 1 0 2 f2Archived71Chart1 = true := by decide +kernel

def f2Archived71Chart2 : RowTree :=
  (.splitA
    (.splitB
      (.splitB
        (.box 129 97)
        (.splitA
          (.box 75 0)
          (.splitA
            (.box 161 0)
            (.box 193 193)
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
                (.box 89 177)
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
                    (.box 122 110)
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
                      (.splitA
                        (.box 126 119)
                        (.splitB
                          (.box 122 117)
                          (.splitA
                            (.box 124 120)
                            (.box 122 120)
                          )
                        )
                      )
                      (.splitA
                        (.splitB
                          (.splitB
                            (.box 126 123)
                            (.box 126 125)
                          )
                          (.splitB
                            (.splitA
                              (.box 128 126)
                              (.box 126 126)
                            )
                            (.splitA
                              (.box 128 128)
                              (.box 126 128)
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
                          (.box 119 116)
                          (.splitB
                            (.box 119 119)
                            (.box 120 120)
                          )
                        )
                        (.splitB
                          (.box 116 115)
                          (.box 116 119)
                        )
                      )
                      (.splitB
                        (.splitA
                          (.splitB
                            (.box 120 122)
                            (.box 120 124)
                          )
                          (.box 117 122)
                        )
                        (.box 119 126)
                      )
                    )
                  )
                )
                (.splitB
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
              (.splitB
                (.splitA
                  (.splitB
                    (.box 92 101)
                    (.box 95 107)
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
                (.box 176 168)
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
      (.splitB
        (.splitA
          (.box 129 97)
          (.box 84 84)
        )
        (.splitA
          (.splitA
            (.box 193 193)
            (.box 161 129)
          )
          (.box 97 129)
        )
      )
      (.splitA
        (.splitB
          (.splitB
            (.box 193 193)
            (.box 0 161)
          )
          (.box 0 75)
        )
        (.box 97 129)
      )
    )
  )

theorem f2Archived71Chart2_ok : checkChart f2Archived71 2 0 1 f2Archived71Chart2 = true := by decide +kernel

end HlawkaSchatten.BelowExponent.FacetNumeric
