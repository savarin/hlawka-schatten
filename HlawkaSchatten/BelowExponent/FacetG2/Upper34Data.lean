/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.FacetNumeric

/-! Certificate data for the G2 facet triangles: `Upper34Data`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true

@[expose] public section

namespace HlawkaSchatten.BelowExponent.FacetNumeric

def g2Upper34 : Prism := {
  vertices := [⟨5160500, 617500, 222000, 0⟩, ⟨5160500, 539500, 300000, 0⟩, ⟨5059000, 641000, 300000, 0⟩, ⟨5150179, 616265, 221556, 12000⟩, ⟨5150179, 538421, 299400, 12000⟩, ⟨5048882, 639718, 299400, 12000⟩]
  profileDen := 6000000
  pi := [44832744, 278258275, 216924758, 533726047]
  slope := [494410310, -180830001, -319870041]
  radiusNum := 1
  radiusDen := 16
}

set_option maxRecDepth 40000
set_option maxHeartbeats 0

theorem g2Upper34_data_ok : dataOK g2Upper34 = true := by decide +kernel

def g2Upper34Chart0 : RowTree :=
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
                            (.splitB
                              (.box 126 128)
                              (.box 126 126)
                            )
                          )
                          (.splitA
                            (.splitB
                              (.box 128 124)
                              (.box 128 122)
                            )
                            (.splitB
                              (.box 126 124)
                              (.box 126 122)
                            )
                          )
                        )
                        (.splitB
                          (.splitA
                            (.box 124 127)
                            (.box 123 127)
                          )
                          (.splitA
                            (.splitB
                              (.box 124 124)
                              (.box 124 122)
                            )
                            (.box 123 123)
                          )
                        )
                      )
                      (.splitA
                        (.splitB
                          (.splitA
                            (.splitB
                              (.box 128 120)
                              (.box 128 118)
                            )
                            (.splitB
                              (.box 126 120)
                              (.box 126 118)
                            )
                          )
                          (.box 127 115)
                        )
                        (.splitB
                          (.splitA
                            (.box 124 119)
                            (.box 122 119)
                          )
                          (.box 123 115)
                        )
                      )
                    )
                    (.splitB
                      (.splitA
                        (.splitB
                          (.box 119 127)
                          (.box 119 123)
                        )
                        (.box 117 125)
                      )
                      (.splitA
                        (.splitB
                          (.box 119 119)
                          (.box 119 115)
                        )
                        (.box 117 118)
                      )
                    )
                  )
                  (.splitA
                    (.splitB
                      (.splitA
                        (.box 127 110)
                        (.box 123 110)
                      )
                      (.box 125 101)
                    )
                    (.splitB
                      (.box 119 110)
                      (.box 117 101)
                    )
                  )
                )
                (.splitB
                  (.splitA
                    (.splitB
                      (.box 111 125)
                      (.box 109 118)
                    )
                    (.box 103 121)
                  )
                  (.splitA
                    (.splitB
                      (.box 109 109)
                      (.box 109 101)
                    )
                    (.box 101 106)
                  )
                )
              )
              (.splitA
                (.splitB
                  (.splitA
                    (.box 125 90)
                    (.box 117 90)
                  )
                  (.box 121 73)
                )
                (.splitB
                  (.splitA
                    (.box 109 90)
                    (.box 101 89)
                  )
                  (.box 105 73)
                )
              )
            )
            (.splitB
              (.splitA
                (.splitB
                  (.box 93 121)
                  (.box 89 106)
                )
                (.splitB
                  (.box 73 121)
                  (.box 73 105)
                )
              )
              (.splitA
                (.splitB
                  (.box 89 89)
                  (.box 89 73)
                )
                (.box 77 82)
              )
            )
          )
          (.splitA
            (.splitB
              (.splitA
                (.splitB
                  (.box 121 177)
                  (.box 121 145)
                )
                (.splitB
                  (.box 105 177)
                  (.box 105 145)
                )
              )
              (.splitA
                (.box 121 193)
                (.box 105 193)
              )
            )
            (.splitB
              (.splitA
                (.splitB
                  (.box 89 177)
                  (.box 89 145)
                )
                (.splitB
                  (.box 73 177)
                  (.box 73 145)
                )
              )
              (.splitA
                (.splitB
                  (.box 89 225)
                  (.box 89 257)
                )
                (.splitB
                  (.box 73 225)
                  (.box 73 289)
                )
              )
            )
          )
        )
        (.splitB
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
              (.box 193 74)
            )
          )
          (.splitA
            (.splitB
              (.splitA
                (.splitB
                  (.box 177 177)
                  (.box 177 137)
                )
                (.splitB
                  (.box 145 177)
                  (.splitA
                    (.box 153 137)
                    (.box 137 137)
                  )
                )
              )
              (.splitA
                (.splitB
                  (.splitA
                    (.box 177 224)
                    (.splitB
                      (.box 169 241)
                      (.box 169 209)
                    )
                  )
                  (.splitA
                    (.box 185 288)
                    (.splitB
                      (.box 169 305)
                      (.box 169 321)
                    )
                  )
                )
                (.splitB
                  (.splitA
                    (.splitB
                      (.box 149 233)
                      (.splitA
                        (.splitB
                          (.box 157 217)
                          (.box 157 201)
                        )
                        (.splitB
                          (.box 146 216)
                          (.splitA
                            (.box 151 201)
                            (.box 145 202)
                          )
                        )
                      )
                    )
                    (.splitB
                      (.splitA
                        (.box 140 233)
                        (.box 134 233)
                      )
                      (.splitA
                        (.splitB
                          (.splitA
                            (.splitB
                              (.box 143 221)
                              (.box 143 212)
                            )
                            (.splitB
                              (.box 139 221)
                              (.splitA
                                (.box 140 212)
                                (.box 138 212)
                              )
                            )
                          )
                          (.splitA
                            (.splitB
                              (.box 143 206)
                              (.box 143 197)
                            )
                            (.splitB
                              (.splitA
                                (.box 140 206)
                                (.box 138 206)
                              )
                              (.box 139 197)
                            )
                          )
                        )
                        (.splitB
                          (.splitA
                            (.splitB
                              (.box 135 221)
                              (.box 136 212)
                            )
                            (.splitB
                              (.box 131 221)
                              (.box 131 213)
                            )
                          )
                          (.splitA
                            (.splitB
                              (.splitA
                                (.box 136 206)
                                (.box 134 205)
                              )
                              (.box 135 197)
                            )
                            (.splitB
                              (.box 131 205)
                              (.box 131 197)
                            )
                          )
                        )
                      )
                    )
                  )
                  (.splitA
                    (.splitB
                      (.box 149 305)
                      (.box 153 321)
                    )
                    (.splitB
                      (.splitA
                        (.splitB
                          (.box 141 313)
                          (.box 141 273)
                        )
                        (.splitB
                          (.box 133 313)
                          (.box 133 273)
                        )
                      )
                      (.box 137 321)
                    )
                  )
                )
              )
            )
            (.splitB
              (.splitA
                (.splitB
                  (.box 225 177)
                  (.splitA
                    (.box 241 137)
                    (.box 209 137)
                  )
                )
                (.splitB
                  (.box 257 177)
                  (.box 257 137)
                )
              )
              (.splitA
                (.splitB
                  (.splitA
                    (.splitB
                      (.splitA
                        (.box 249 233)
                        (.box 233 241)
                      )
                      (.splitA
                        (.splitB
                          (.box 129 216)
                          (.box 129 202)
                        )
                        (.box 241 209)
                      )
                    )
                    (.splitB
                      (.box 209 241)
                      (.box 209 209)
                    )
                  )
                  (.splitA
                    (.splitB
                      (.box 249 305)
                      (.box 241 321)
                    )
                    (.box 225 289)
                  )
                )
                (.splitB
                  (.box 193 226)
                  (.box 257 289)
                )
              )
            )
          )
        )
      )
      (.splitA
        (.splitB
          (.splitA
            (.box 113 194)
            (.splitB
              (.box 81 257)
              (.box 81 161)
            )
          )
          (.box 97 97)
        )
        (.splitB
          (.splitA
            (.splitB
              (.splitA
                (.box 177 257)
                (.box 145 257)
              )
              (.box 161 161)
            )
            (.splitB
              (.splitA
                (.box 225 257)
                (.box 257 257)
              )
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
          (.splitA
            (.box 0 97)
            (.box 161 97)
          )
          (.splitA
            (.splitB
              (.box 0 161)
              (.box 0 193)
            )
            (.box 161 129)
          )
        )
        (.box 65 65)
      )
      (.splitA
        (.splitB
          (.splitA
            (.box 0 193)
            (.box 161 129)
          )
          (.box 129 97)
        )
        (.box 97 129)
      )
    )
  )

theorem g2Upper34Chart0_ok : checkChart g2Upper34 0 1 2 g2Upper34Chart0 = true := by decide +kernel

def g2Upper34Chart1 : RowTree :=
  (.splitA
    (.splitB
      (.splitA
        (.splitB
          (.box 97 97)
          (.splitA
            (.splitB
              (.box 113 161)
              (.box 113 193)
            )
            (.splitB
              (.box 81 161)
              (.box 80 257)
            )
          )
        )
        (.splitB
          (.box 129 81)
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
                (.box 225 257)
                (.box 257 257)
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
                (.splitB
                  (.box 105 257)
                  (.box 105 225)
                )
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
              (.splitA
                (.splitB
                  (.box 89 257)
                  (.box 89 225)
                )
                (.splitB
                  (.box 73 257)
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
                    (.splitB
                      (.box 125 85)
                      (.box 125 93)
                    )
                    (.splitB
                      (.box 117 85)
                      (.box 117 93)
                    )
                  )
                )
                (.splitB
                  (.splitA
                    (.box 109 73)
                    (.box 101 73)
                  )
                  (.splitA
                    (.splitB
                      (.box 109 85)
                      (.box 109 93)
                    )
                    (.box 101 90)
                  )
                )
              )
              (.splitA
                (.splitB
                  (.splitA
                    (.splitB
                      (.splitA
                        (.box 127 101)
                        (.box 123 101)
                      )
                      (.splitA
                        (.splitB
                          (.box 127 107)
                          (.box 127 111)
                        )
                        (.splitB
                          (.box 123 107)
                          (.box 123 111)
                        )
                      )
                    )
                    (.splitB
                      (.splitA
                        (.box 119 101)
                        (.box 115 101)
                      )
                      (.splitA
                        (.splitB
                          (.box 119 107)
                          (.box 119 111)
                        )
                        (.box 115 110)
                      )
                    )
                  )
                  (.splitA
                    (.splitB
                      (.splitA
                        (.splitB
                          (.splitA
                            (.box 128 115)
                            (.box 126 115)
                          )
                          (.splitA
                            (.splitB
                              (.box 128 118)
                              (.box 128 120)
                            )
                            (.splitB
                              (.box 126 118)
                              (.box 126 120)
                            )
                          )
                        )
                        (.splitB
                          (.splitA
                            (.box 124 115)
                            (.box 122 115)
                          )
                          (.splitA
                            (.splitB
                              (.box 124 118)
                              (.box 124 120)
                            )
                            (.splitB
                              (.box 122 118)
                              (.box 122 120)
                            )
                          )
                        )
                      )
                      (.splitA
                        (.splitB
                          (.splitA
                            (.splitB
                              (.splitA
                                (.splitB
                                  (.box 1 122)
                                  (.box 1 123)
                                )
                                (.splitB
                                  (.box 128 122)
                                  (.box 128 123)
                                )
                              )
                              (.box 128 124)
                            )
                            (.splitB
                              (.splitA
                                (.splitB
                                  (.box 127 122)
                                  (.box 127 123)
                                )
                                (.box 126 122)
                              )
                              (.box 126 124)
                            )
                          )
                          (.splitA
                            (.splitB
                              (.box 128 126)
                              (.box 128 128)
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
                            (.splitB
                              (.box 122 122)
                              (.box 122 124)
                            )
                          )
                          (.splitA
                            (.splitB
                              (.box 124 126)
                              (.box 124 128)
                            )
                            (.splitB
                              (.box 122 126)
                              (.box 122 128)
                            )
                          )
                        )
                      )
                    )
                    (.splitB
                      (.splitA
                        (.splitB
                          (.box 119 115)
                          (.splitA
                            (.box 120 119)
                            (.box 118 119)
                          )
                        )
                        (.splitB
                          (.box 115 115)
                          (.box 115 119)
                        )
                      )
                      (.splitA
                        (.splitB
                          (.splitA
                            (.box 120 123)
                            (.box 118 123)
                          )
                          (.box 120 127)
                        )
                        (.splitB
                          (.box 115 123)
                          (.box 115 127)
                        )
                      )
                    )
                  )
                )
                (.splitB
                  (.splitA
                    (.splitB
                      (.box 109 102)
                      (.box 110 110)
                    )
                    (.splitB
                      (.box 101 101)
                      (.box 101 109)
                    )
                  )
                  (.splitA
                    (.splitB
                      (.splitA
                        (.box 111 117)
                        (.box 107 117)
                      )
                      (.box 111 125)
                    )
                    (.box 103 120)
                  )
                )
              )
            )
            (.splitB
              (.splitA
                (.splitB
                  (.box 90 73)
                  (.box 92 89)
                )
                (.splitB
                  (.box 73 73)
                  (.box 73 89)
                )
              )
              (.splitA
                (.splitB
                  (.box 92 105)
                  (.box 93 121)
                )
                (.box 77 112)
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
                (.box 177 161)
                (.box 145 161)
              )
            )
            (.splitB
              (.splitA
                (.splitB
                  (.box 225 257)
                  (.box 225 225)
                )
                (.box 257 257)
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
              (.box 177 113)
            )
            (.box 225 97)
          )
        )
      )
    )
    (.splitB
      (.splitA
        (.splitB
          (.box 129 81)
          (.splitA
            (.splitB
              (.box 193 161)
              (.box 193 193)
            )
            (.box 161 129)
          )
        )
        (.box 81 65)
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
          (.box 193 97)
        )
        (.box 97 129)
      )
    )
  )

theorem g2Upper34Chart1_ok : checkChart g2Upper34 1 0 2 g2Upper34Chart1 = true := by decide +kernel

def g2Upper34Chart2 : RowTree :=
  (.splitA
    (.splitB
      (.splitA
        (.splitB
          (.box 97 97)
          (.splitA
            (.box 113 129)
            (.box 81 193)
          )
        )
        (.splitB
          (.box 129 65)
          (.splitA
            (.box 160 193)
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
              (.splitA
                (.box 121 177)
                (.box 105 177)
              )
            )
            (.splitB
              (.box 81 225)
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
                  (.box 121 73)
                  (.splitA
                    (.box 125 89)
                    (.box 117 93)
                  )
                )
                (.splitB
                  (.box 105 77)
                  (.splitA
                    (.box 109 92)
                    (.splitB
                      (.box 101 85)
                      (.box 101 93)
                    )
                  )
                )
              )
              (.splitA
                (.splitB
                  (.splitA
                    (.splitB
                      (.box 125 101)
                      (.splitA
                        (.box 127 109)
                        (.box 123 111)
                      )
                    )
                    (.splitB
                      (.box 117 103)
                      (.splitA
                        (.box 119 110)
                        (.box 115 110)
                      )
                    )
                  )
                  (.splitA
                    (.splitB
                      (.splitA
                        (.splitB
                          (.box 127 115)
                          (.splitA
                            (.box 128 119)
                            (.box 126 120)
                          )
                        )
                        (.splitB
                          (.box 123 116)
                          (.splitA
                            (.splitB
                              (.box 124 118)
                              (.box 124 120)
                            )
                            (.splitB
                              (.box 122 118)
                              (.box 122 120)
                            )
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
                              (.splitA
                                (.box 126 122)
                                (.splitB
                                  (.box 126 122)
                                  (.box 126 123)
                                )
                              )
                              (.box 126 124)
                            )
                          )
                          (.splitA
                            (.splitB
                              (.box 128 126)
                              (.box 128 128)
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
                              (.splitA
                                (.splitB
                                  (.box 125 122)
                                  (.box 125 123)
                                )
                                (.box 124 122)
                              )
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
                              (.box 124 128)
                            )
                            (.splitB
                              (.box 122 126)
                              (.box 122 128)
                            )
                          )
                        )
                      )
                    )
                    (.splitB
                      (.splitA
                        (.splitB
                          (.box 119 116)
                          (.splitA
                            (.splitB
                              (.box 120 118)
                              (.box 120 120)
                            )
                            (.box 118 119)
                          )
                        )
                        (.splitB
                          (.box 115 115)
                          (.box 115 119)
                        )
                      )
                      (.splitA
                        (.splitB
                          (.splitA
                            (.splitB
                              (.box 120 122)
                              (.box 120 124)
                            )
                            (.box 118 123)
                          )
                          (.box 120 126)
                        )
                        (.box 116 124)
                      )
                    )
                  )
                )
                (.splitB
                  (.splitA
                    (.splitB
                      (.splitA
                        (.box 111 101)
                        (.box 107 101)
                      )
                      (.splitA
                        (.box 111 110)
                        (.box 107 109)
                      )
                    )
                    (.splitB
                      (.box 101 101)
                      (.box 101 109)
                    )
                  )
                  (.splitA
                    (.splitB
                      (.splitA
                        (.splitB
                          (.box 111 115)
                          (.box 111 119)
                        )
                        (.box 107 117)
                      )
                      (.box 111 123)
                    )
                    (.splitB
                      (.box 101 117)
                      (.box 101 125)
                    )
                  )
                )
              )
            )
            (.splitB
              (.splitA
                (.splitB
                  (.splitA
                    (.box 93 73)
                    (.box 85 73)
                  )
                  (.splitA
                    (.box 93 90)
                    (.box 85 89)
                  )
                )
                (.splitB
                  (.box 73 74)
                  (.box 77 85)
                )
              )
              (.splitA
                (.splitB
                  (.splitA
                    (.box 95 104)
                    (.box 85 105)
                  )
                  (.box 93 117)
                )
                (.splitB
                  (.box 73 105)
                  (.box 73 121)
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
              (.splitA
                (.box 225 161)
                (.box 257 161)
              )
            )
          )
          (.splitA
            (.splitB
              (.splitA
                (.box 184 80)
                (.box 145 81)
              )
              (.box 177 105)
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
          (.box 97 97)
          (.box 97 129)
        )
      )
      (.splitA
        (.splitB
          (.splitA
            (.splitB
              (.box 257 193)
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

theorem g2Upper34Chart2_ok : checkChart g2Upper34 2 0 1 g2Upper34Chart2 = true := by decide +kernel

end HlawkaSchatten.BelowExponent.FacetNumeric
