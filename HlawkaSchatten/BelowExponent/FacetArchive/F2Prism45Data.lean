/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.FacetArchive.NearCover

/-! Archived facet prism certificate data: `F2Prism45Data`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.FacetNumeric

def f2Archived45 : Prism := {
  vertices := [⟨95200, 23200, 9600, 0⟩,
    ⟨91600, 28400, 8000, 0⟩,
    ⟨94800, 26800, 6400, 0⟩,
    ⟨94962, 23142, 9576, 320⟩,
    ⟨91371, 28329, 7980, 320⟩,
    ⟨94563, 26733, 6384, 320⟩]
  profileDen := 128000
  pi := [76706650, 223468699, 237617585, 535948890]
  slope := [381971171, -115880202, -267935018]
  radiusNum := 1
  radiusDen := 8
}

set_option maxRecDepth 40000
set_option maxHeartbeats 0

theorem f2Archived45_data_ok : dataOK f2Archived45 = true := by decide +kernel

def f2Archived45Chart0 : RowTree :=
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
                          (.splitA
                            (.splitB
                              (.splitA
                                (.splitB
                                  (.splitA
                                    (.splitB
                                      (.box 10000 0)
                                      (.box 10000 0)
                                    )
                                    (.splitB
                                      (.box 10000 0)
                                      (.box 10000 0)
                                    )
                                  )
                                  (.splitB
                                    (.splitA
                                      (.box 10000 0)
                                      (.box 10000 0)
                                    )
                                    (.box 10000 0)
                                  )
                                )
                                (.splitB
                                  (.splitA
                                    (.box 10000 0)
                                    (.box 10000 0)
                                  )
                                  (.box 10000 0)
                                )
                              )
                              (.splitB
                                (.splitA
                                  (.splitA
                                    (.box 10000 0)
                                    (.box 10000 0)
                                  )
                                  (.box 10000 0)
                                )
                                (.splitA
                                  (.box 10000 0)
                                  (.box 128 126)
                                )
                              )
                            )
                            (.splitB
                              (.splitB
                                (.splitA
                                  (.box 127 1)
                                  (.box 126 1)
                                )
                                (.splitA
                                  (.box 127 128)
                                  (.box 126 128)
                                )
                              )
                              (.splitA
                                (.box 127 126)
                                (.box 126 126)
                              )
                            )
                          )
                          (.splitB
                            (.splitA
                              (.splitA
                                (.box 10000 0)
                                (.box 128 124)
                              )
                              (.box 126 124)
                            )
                            (.splitA
                              (.box 128 122)
                              (.box 127 122)
                            )
                          )
                        )
                        (.splitB
                          (.splitB
                            (.box 124 128)
                            (.box 124 126)
                          )
                          (.splitB
                            (.box 124 124)
                            (.box 124 122)
                          )
                        )
                      )
                      (.splitB
                        (.splitA
                          (.splitA
                            (.box 128 120)
                            (.box 126 120)
                          )
                          (.box 124 120)
                        )
                        (.splitA
                          (.box 127 116)
                          (.box 124 116)
                        )
                      )
                    )
                    (.splitB
                      (.splitB
                        (.box 120 127)
                        (.box 120 123)
                      )
                      (.splitB
                        (.box 119 120)
                        (.box 119 116)
                      )
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
                  (.splitB
                    (.box 111 125)
                    (.box 111 117)
                  )
                  (.splitB
                    (.box 108 111)
                    (.box 108 103)
                  )
                )
              )
              (.splitB
                (.splitA
                  (.box 122 92)
                  (.box 108 92)
                )
                (.splitA
                  (.box 121 76)
                  (.box 108 76)
                )
              )
            )
            (.splitB
              (.splitB
                (.box 92 121)
                (.box 92 105)
              )
              (.splitB
                (.box 87 92)
                (.box 87 76)
              )
            )
          )
          (.splitA
            (.splitB
              (.box 65 113)
              (.box 161 81)
            )
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
                (.box 161 145)
              )
              (.box 193 145)
            )
            (.splitA
              (.splitB
                (.box 161 225)
                (.splitA
                  (.box 177 257)
                  (.box 145 257)
                )
              )
              (.splitA
                (.box 129 193)
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
              (.box 103 0)
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
              (.box 193 0)
              (.box 193 161)
            )
          )
          (.box 129 97)
        )
      )
    )
    (.splitB
      (.splitB
        (.box 129 97)
        (.splitB
          (.box 129 145)
          (.splitA
            (.box 0 193)
            (.box 97 193)
          )
        )
      )
      (.splitB
        (.splitA
          (.box 0 129)
          (.box 97 129)
        )
        (.box 65 97)
      )
    )
  )

theorem f2Archived45Chart0_ok : checkMixedChart f2Archived45 0 f2Archived45Chart0 = true := by decide +kernel

def f2Archived45Chart1 : RowTree :=
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
          (.box 129 97)
          (.splitA
            (.splitB
              (.box 161 161)
              (.box 161 257)
            )
            (.box 225 193)
          )
        )
      )
      (.splitA
        (.splitB
          (.splitB
            (.splitA
              (.box 106 225)
              (.splitB
                (.box 81 257)
                (.box 81 225)
              )
            )
            (.splitA
              (.splitA
                (.box 118 176)
                (.splitB
                  (.box 105 145)
                  (.box 105 177)
                )
              )
              (.splitB
                (.box 81 145)
                (.box 89 177)
              )
            )
          )
          (.splitA
            (.splitB
              (.splitA
                (.splitB
                  (.box 121 76)
                  (.splitA
                    (.box 125 92)
                    (.box 117 92)
                  )
                )
                (.splitB
                  (.box 108 76)
                  (.splitB
                    (.box 108 87)
                    (.box 108 95)
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
                      (.box 119 103)
                      (.box 118 110)
                    )
                  )
                  (.splitA
                    (.splitB
                      (.splitA
                        (.splitB
                          (.box 127 116)
                          (.splitA
                            (.box 128 120)
                            (.box 126 120)
                          )
                        )
                        (.splitB
                          (.box 124 116)
                          (.splitA
                            (.box 124 119)
                            (.box 123 119)
                          )
                        )
                      )
                      (.splitA
                        (.splitB
                          (.splitA
                            (.splitB
                              (.box 128 122)
                              (.splitA
                                (.splitB
                                  (.box 1 124)
                                  (.box 10000 0)
                                )
                                (.splitB
                                  (.box 128 124)
                                  (.box 10000 0)
                                )
                              )
                            )
                            (.splitB
                              (.box 126 122)
                              (.splitA
                                (.box 127 124)
                                (.box 126 124)
                              )
                            )
                          )
                          (.splitA
                            (.splitB
                              (.splitA
                                (.splitB
                                  (.box 10000 0)
                                  (.splitA
                                    (.box 10000 0)
                                    (.box 10000 0)
                                  )
                                )
                                (.splitB
                                  (.box 10000 0)
                                  (.splitA
                                    (.box 10000 0)
                                    (.box 10000 0)
                                  )
                                )
                              )
                              (.splitA
                                (.splitB
                                  (.splitA
                                    (.splitB
                                      (.box 10000 0)
                                      (.box 10000 0)
                                    )
                                    (.splitB
                                      (.box 10000 0)
                                      (.box 10000 0)
                                    )
                                  )
                                  (.splitA
                                    (.splitB
                                      (.box 10000 0)
                                      (.box 10000 0)
                                    )
                                    (.splitB
                                      (.box 10000 0)
                                      (.box 10000 0)
                                    )
                                  )
                                )
                                (.splitB
                                  (.splitA
                                    (.box 10000 0)
                                    (.box 10000 0)
                                  )
                                  (.splitA
                                    (.box 10000 0)
                                    (.box 10000 0)
                                  )
                                )
                              )
                            )
                            (.splitB
                              (.splitB
                                (.splitA
                                  (.box 127 126)
                                  (.box 126 126)
                                )
                                (.splitA
                                  (.box 10000 0)
                                  (.box 126 127)
                                )
                              )
                              (.splitB
                                (.splitA
                                  (.box 127 128)
                                  (.box 126 128)
                                )
                                (.splitA
                                  (.box 127 128)
                                  (.box 126 128)
                                )
                              )
                            )
                          )
                        )
                        (.splitB
                          (.splitB
                            (.box 124 122)
                            (.box 124 124)
                          )
                          (.splitB
                            (.box 124 126)
                            (.box 124 128)
                          )
                        )
                      )
                    )
                    (.splitB
                      (.splitB
                        (.box 119 116)
                        (.box 119 119)
                      )
                      (.splitB
                        (.box 119 123)
                        (.box 119 127)
                      )
                    )
                  )
                )
                (.splitB
                  (.splitB
                    (.box 108 103)
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
                (.box 87 89)
              )
              (.splitB
                (.box 87 105)
                (.box 87 118)
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
              (.box 193 257)
              (.box 193 161)
            )
          )
          (.splitB
            (.box 161 81)
            (.box 161 113)
          )
        )
      )
    )
    (.splitB
      (.splitA
        (.box 193 130)
        (.box 97 65)
      )
      (.splitB
        (.splitA
          (.box 0 193)
          (.box 97 129)
        )
        (.box 129 97)
      )
    )
  )

theorem f2Archived45Chart1_ok : checkMixedChart f2Archived45 1 f2Archived45Chart1 = true := by decide +kernel

def f2Archived45Chart2 : RowTree :=
  (.splitA
    (.splitB
      (.splitA
        (.box 81 129)
        (.splitA
          (.splitB
            (.box 161 97)
            (.box 161 193)
          )
          (.splitB
            (.box 0 65)
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
            (.splitB
              (.box 113 193)
              (.box 113 177)
            )
            (.splitB
              (.box 81 129)
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
                  (.box 115 81)
                  (.box 118 95)
                )
                (.splitB
                  (.box 102 79)
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
                      (.box 122 105)
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
                          (.splitA
                            (.box 124 120)
                            (.box 122 120)
                          )
                        )
                      )
                      (.splitA
                        (.splitB
                          (.splitA
                            (.splitB
                              (.box 127 123)
                              (.splitA
                                (.box 128 125)
                                (.box 127 125)
                              )
                            )
                            (.splitB
                              (.box 126 123)
                              (.splitA
                                (.box 10000 0)
                                (.box 10000 0)
                              )
                            )
                          )
                          (.splitA
                            (.splitB
                              (.splitA
                                (.splitB
                                  (.box 128 126)
                                  (.splitA
                                    (.box 1 127)
                                    (.box 128 127)
                                  )
                                )
                                (.splitB
                                  (.box 10000 0)
                                  (.splitA
                                    (.box 10000 0)
                                    (.box 10000 0)
                                  )
                                )
                              )
                              (.splitA
                                (.splitB
                                  (.splitA
                                    (.splitB
                                      (.box 10000 0)
                                      (.box 10000 0)
                                    )
                                    (.splitB
                                      (.box 10000 0)
                                      (.box 10000 0)
                                    )
                                  )
                                  (.splitA
                                    (.splitB
                                      (.box 10000 0)
                                      (.box 10000 0)
                                    )
                                    (.splitB
                                      (.box 10000 0)
                                      (.box 10000 0)
                                    )
                                  )
                                )
                                (.splitB
                                  (.splitA
                                    (.splitB
                                      (.box 10000 0)
                                      (.box 10000 0)
                                    )
                                    (.box 10000 0)
                                  )
                                  (.splitB
                                    (.splitA
                                      (.box 10000 0)
                                      (.box 10000 0)
                                    )
                                    (.splitA
                                      (.box 10000 0)
                                      (.box 10000 0)
                                    )
                                  )
                                )
                              )
                            )
                            (.splitB
                              (.splitA
                                (.splitB
                                  (.box 10000 0)
                                  (.box 10000 0)
                                )
                                (.splitB
                                  (.box 10000 0)
                                  (.box 10000 0)
                                )
                              )
                              (.splitB
                                (.splitA
                                  (.box 10000 0)
                                  (.box 126 127)
                                )
                                (.splitA
                                  (.box 127 128)
                                  (.box 126 128)
                                )
                              )
                            )
                          )
                        )
                        (.splitB
                          (.splitA
                            (.splitB
                              (.box 124 122)
                              (.splitA
                                (.box 125 124)
                                (.box 124 124)
                              )
                            )
                            (.splitB
                              (.box 122 122)
                              (.box 122 124)
                            )
                          )
                          (.splitA
                            (.splitB
                              (.splitA
                                (.box 125 126)
                                (.box 124 126)
                              )
                              (.box 125 127)
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
                          (.splitA
                            (.box 120 120)
                            (.box 119 119)
                          )
                        )
                        (.splitB
                          (.box 116 115)
                          (.box 116 119)
                        )
                      )
                      (.splitA
                        (.splitB
                          (.splitB
                            (.box 120 122)
                            (.box 120 124)
                          )
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
                  (.splitA
                    (.splitB
                      (.splitB
                        (.box 111 114)
                        (.box 111 118)
                      )
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
                  (.splitB
                    (.box 92 99)
                    (.box 92 107)
                  )
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
              (.box 225 161)
            )
          )
          (.splitA
            (.splitB
              (.splitB
                (.box 177 69)
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
              (.box 193 257)
            )
            (.box 161 129)
          )
        )
        (.box 75 65)
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
          (.box 0 75)
        )
        (.box 97 129)
      )
    )
  )

theorem f2Archived45Chart2_ok : checkMixedChart f2Archived45 2 f2Archived45Chart2 = true := by decide +kernel

end HlawkaSchatten.BelowExponent.FacetNumeric
