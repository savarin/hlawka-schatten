/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.FacetNumeric

/-! Archived facet prism certificate data: `F2Prism12Data`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true

@[expose] public section

namespace HlawkaSchatten.BelowExponent.FacetNumeric

def f2Archived12 : Prism := {
  vertices := [⟨210800, 26000, 19200, 0⟩,
    ⟨216800, 26400, 12800, 0⟩,
    ⟨217600, 19200, 19200, 0⟩,
    ⟨210273, 25935, 19152, 640⟩,
    ⟨216258, 26334, 12768, 640⟩,
    ⟨217056, 19152, 19152, 640⟩]
  profileDen := 256000
  pi := [45929951, 249117051, 243906871, 534787951]
  slope := [486828410, -228386665, -262607671]
  radiusNum := 1
  radiusDen := 8
}

set_option maxRecDepth 40000
set_option maxHeartbeats 0

theorem f2Archived12_data_ok : dataOK f2Archived12 = true := by decide +kernel

def f2Archived12Chart0 : RowTree :=
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
                          (.splitB
                            (.splitA
                              (.box 128 128)
                              (.box 126 128)
                            )
                            (.splitA
                              (.box 128 126)
                              (.box 126 126)
                            )
                          )
                          (.splitB
                            (.splitA
                              (.box 124 128)
                              (.box 123 128)
                            )
                            (.splitA
                              (.box 124 126)
                              (.box 123 126)
                            )
                          )
                        )
                        (.splitA
                          (.splitB
                            (.splitA
                              (.box 128 124)
                              (.box 126 124)
                            )
                            (.box 127 122)
                          )
                          (.splitB
                            (.box 124 124)
                            (.box 124 123)
                          )
                        )
                      )
                      (.splitB
                        (.splitA
                          (.box 120 127)
                          (.box 116 127)
                        )
                        (.splitA
                          (.box 120 124)
                          (.box 116 123)
                        )
                      )
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
                      (.splitB
                        (.splitA
                          (.box 120 120)
                          (.box 116 120)
                        )
                        (.box 119 116)
                      )
                    )
                  )
                  (.splitB
                    (.splitA
                      (.box 111 125)
                      (.box 104 125)
                    )
                    (.splitA
                      (.box 111 119)
                      (.box 104 117)
                    )
                  )
                )
                (.splitA
                  (.splitB
                    (.splitA
                      (.splitA
                        (.box 126 111)
                        (.box 125 111)
                      )
                      (.box 119 111)
                    )
                    (.splitA
                      (.box 125 103)
                      (.box 119 103)
                    )
                  )
                  (.splitB
                    (.splitA
                      (.box 111 111)
                      (.box 104 111)
                    )
                    (.box 108 103)
                  )
                )
              )
              (.splitB
                (.splitA
                  (.box 92 121)
                  (.box 79 121)
                )
                (.splitA
                  (.box 92 105)
                  (.box 79 105)
                )
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
              (.splitA
                (.splitB
                  (.box 92 92)
                  (.box 92 76)
                )
                (.box 79 82)
              )
            )
          )
          (.splitA
            (.splitB
              (.box 177 113)
              (.splitA
                (.box 177 81)
                (.box 145 81)
              )
            )
            (.splitB
              (.box 193 113)
              (.box 193 73)
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
              (.splitA
                (.splitB
                  (.box 177 177)
                  (.box 177 145)
                )
                (.splitB
                  (.box 145 177)
                  (.box 145 145)
                )
              )
              (.splitA
                (.splitB
                  (.box 225 177)
                  (.box 225 145)
                )
                (.box 289 161)
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
                (.splitA
                  (.box 225 257)
                  (.box 257 257)
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
          (.box 193 82)
          (.box 65 84)
        )
        (.splitA
          (.splitB
            (.splitA
              (.box 0 161)
              (.box 161 161)
            )
            (.splitA
              (.box 0 193)
              (.box 161 193)
            )
          )
          (.box 97 129)
        )
      )
      (.splitB
        (.splitA
          (.box 193 193)
          (.box 65 0)
        )
        (.box 65 97)
      )
    )
  )

theorem f2Archived12Chart0_ok : checkChart f2Archived12 0 1 2 f2Archived12Chart0 = true := by decide +kernel

def f2Archived12Chart1 : RowTree :=
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
            (.splitA
              (.box 225 193)
              (.box 257 193)
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
                    (.box 103 90)
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
                        (.box 115 110)
                      )
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
                          (.box 123 116)
                          (.splitA
                            (.box 124 120)
                            (.box 122 119)
                          )
                        )
                      )
                      (.splitA
                        (.splitB
                          (.splitA
                            (.splitB
                              (.box 128 122)
                              (.box 128 124)
                            )
                            (.splitB
                              (.box 126 122)
                              (.box 126 124)
                            )
                          )
                          (.splitA
                            (.splitB
                              (.splitA
                                (.splitB
                                  (.box 1 126)
                                  (.box 1 127)
                                )
                                (.box 128 126)
                              )
                              (.splitA
                                (.splitB
                                  (.splitA
                                    (.box 1 128)
                                    (.box 128 128)
                                  )
                                  (.splitA
                                    (.box 1 128)
                                    (.box 128 1)
                                  )
                                )
                                (.box 128 128)
                              )
                            )
                            (.splitB
                              (.box 126 126)
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
                            (.box 122 123)
                          )
                          (.splitA
                            (.splitB
                              (.box 124 126)
                              (.box 124 128)
                            )
                            (.box 122 127)
                          )
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
                          (.box 120 123)
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
                      (.box 109 103)
                      (.box 110 109)
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
                    (.splitB
                      (.box 104 115)
                      (.box 104 123)
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
                  (.box 92 118)
                )
                (.box 79 107)
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
              (.splitB
                (.box 177 73)
                (.box 177 89)
              )
              (.box 177 113)
            )
            (.box 129 81)
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
      (.splitB
        (.splitA
          (.splitA
            (.splitB
              (.box 193 193)
              (.box 193 161)
            )
            (.box 161 129)
          )
          (.box 75 0)
        )
        (.splitA
          (.box 129 81)
          (.box 65 65)
        )
      )
    )
  )

theorem f2Archived12Chart1_ok : checkChart f2Archived12 1 0 2 f2Archived12Chart1 = true := by decide +kernel

def f2Archived12Chart2 : RowTree :=
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
              (.box 113 225)
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
                    (.box 117 92)
                  )
                )
                (.splitB
                  (.box 105 76)
                  (.splitA
                    (.box 109 92)
                    (.splitB
                      (.box 101 88)
                      (.box 101 96)
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
                        (.box 123 111)
                      )
                    )
                    (.splitB
                      (.box 117 103)
                      (.splitA
                        (.box 119 111)
                        (.box 115 110)
                      )
                    )
                  )
                  (.splitA
                    (.splitB
                      (.splitA
                        (.splitB
                          (.box 126 116)
                          (.splitA
                            (.box 128 120)
                            (.box 126 120)
                          )
                        )
                        (.splitB
                          (.box 123 116)
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
                              (.box 128 123)
                              (.box 128 124)
                            )
                            (.splitB
                              (.box 126 122)
                              (.box 126 124)
                            )
                          )
                          (.splitA
                            (.splitB
                              (.box 128 126)
                              (.splitA
                                (.splitB
                                  (.box 128 128)
                                  (.splitA
                                    (.box 1 128)
                                    (.box 128 1)
                                  )
                                )
                                (.box 128 128)
                              )
                            )
                            (.splitB
                              (.box 126 126)
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
                            (.box 122 123)
                          )
                          (.splitA
                            (.splitB
                              (.box 124 126)
                              (.box 124 128)
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
                            (.box 120 119)
                            (.box 118 119)
                          )
                        )
                        (.splitB
                          (.box 116 115)
                          (.box 116 119)
                        )
                      )
                      (.splitA
                        (.splitB
                          (.splitA
                            (.box 120 123)
                            (.box 119 123)
                          )
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
                      (.box 109 103)
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
                        (.box 109 115)
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
                (.box 185 161)
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
              (.splitA
                (.box 185 81)
                (.box 145 81)
              )
              (.box 177 113)
            )
            (.box 225 81)
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

theorem f2Archived12Chart2_ok : checkChart f2Archived12 2 0 1 f2Archived12Chart2 = true := by decide +kernel

end HlawkaSchatten.BelowExponent.FacetNumeric
