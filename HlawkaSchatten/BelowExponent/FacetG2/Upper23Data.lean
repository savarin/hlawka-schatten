/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.FacetNumeric

/-! Certificate data for the G2 facet triangles: `Upper23Data`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true

@[expose] public section

namespace HlawkaSchatten.BelowExponent.FacetNumeric

def g2Upper23 : Prism := {
  vertices := [⟨4957500, 840000, 202500, 0⟩, ⟨4856000, 844000, 300000, 0⟩, ⟨4856000, 922000, 222000, 0⟩, ⟨4947585, 838320, 202095, 12000⟩, ⟨4846288, 842312, 299400, 12000⟩, ⟨4846288, 920156, 221556, 12000⟩]
  profileDen := 6000000
  pi := [53731308, 244500406, 241677853, 533832257]
  slope := [456236254, -166860502, -295453063]
  radiusNum := 1
  radiusDen := 16
}

set_option maxRecDepth 40000
set_option maxHeartbeats 0

theorem g2Upper23_data_ok : dataOK g2Upper23 = true := by decide +kernel

def g2Upper23Chart0 : RowTree :=
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
                            (.box 122 127)
                          )
                          (.splitA
                            (.splitB
                              (.box 124 124)
                              (.box 124 122)
                            )
                            (.box 122 123)
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
                          (.box 124 119)
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
                        (.box 115 125)
                      )
                      (.splitA
                        (.splitB
                          (.box 119 119)
                          (.box 119 115)
                        )
                        (.box 115 117)
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
                      (.box 119 109)
                      (.box 117 101)
                    )
                  )
                )
                (.splitB
                  (.splitA
                    (.splitB
                      (.box 109 125)
                      (.box 109 117)
                    )
                    (.box 101 121)
                  )
                  (.splitA
                    (.box 112 106)
                    (.box 101 105)
                  )
                )
              )
              (.splitA
                (.splitB
                  (.splitA
                    (.splitB
                      (.box 125 93)
                      (.box 125 85)
                    )
                    (.box 118 90)
                  )
                  (.box 121 73)
                )
                (.splitB
                  (.box 109 90)
                  (.box 105 73)
                )
              )
            )
            (.splitB
              (.splitA
                (.splitB
                  (.box 89 121)
                  (.box 89 105)
                )
                (.box 73 113)
              )
              (.splitA
                (.splitB
                  (.box 89 89)
                  (.box 89 73)
                )
                (.box 73 81)
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
                  (.box 69 209)
                  (.splitA
                    (.box 77 257)
                    (.splitB
                      (.box 69 289)
                      (.box 69 321)
                    )
                  )
                )
              )
            )
          )
        )
        (.splitB
          (.splitA
            (.splitB
              (.box 161 113)
              (.box 161 81)
            )
            (.box 225 96)
          )
          (.splitA
            (.splitB
              (.splitA
                (.splitB
                  (.box 177 177)
                  (.box 177 145)
                )
                (.box 145 145)
              )
              (.splitA
                (.splitB
                  (.splitA
                    (.splitB
                      (.box 185 241)
                      (.box 185 201)
                    )
                    (.splitB
                      (.box 169 241)
                      (.splitA
                        (.box 173 201)
                        (.box 163 200)
                      )
                    )
                  )
                  (.splitA
                    (.splitB
                      (.box 178 290)
                      (.box 185 353)
                    )
                    (.splitB
                      (.splitA
                        (.splitB
                          (.box 169 305)
                          (.box 173 281)
                        )
                        (.splitB
                          (.splitA
                            (.splitB
                              (.box 167 313)
                              (.box 167 297)
                            )
                            (.splitB
                              (.box 163 309)
                              (.box 162 297)
                            )
                          )
                          (.splitA
                            (.box 167 281)
                            (.splitB
                              (.box 163 285)
                              (.box 163 265)
                            )
                          )
                        )
                      )
                      (.splitA
                        (.box 173 353)
                        (.box 165 353)
                      )
                    )
                  )
                )
                (.splitB
                  (.splitA
                    (.splitB
                      (.box 153 241)
                      (.splitA
                        (.splitB
                          (.box 157 217)
                          (.box 157 197)
                        )
                        (.box 149 200)
                      )
                    )
                    (.splitB
                      (.box 137 241)
                      (.box 137 200)
                    )
                  )
                  (.splitA
                    (.splitB
                      (.splitA
                        (.splitB
                          (.splitA
                            (.splitB
                              (.box 159 309)
                              (.splitA
                                (.splitB
                                  (.box 160 301)
                                  (.box 160 293)
                                )
                                (.splitB
                                  (.box 158 301)
                                  (.box 158 293)
                                )
                              )
                            )
                            (.splitB
                              (.box 155 313)
                              (.box 156 297)
                            )
                          )
                          (.splitA
                            (.splitB
                              (.box 159 285)
                              (.box 159 265)
                            )
                            (.box 156 281)
                          )
                        )
                        (.splitB
                          (.splitA
                            (.splitB
                              (.box 151 313)
                              (.box 151 297)
                            )
                            (.box 147 305)
                          )
                          (.box 151 281)
                        )
                      )
                      (.splitA
                        (.box 157 353)
                        (.box 149 353)
                      )
                    )
                    (.splitB
                      (.splitA
                        (.splitB
                          (.box 141 305)
                          (.box 141 273)
                        )
                        (.box 133 289)
                      )
                      (.box 137 257)
                    )
                  )
                )
              )
            )
            (.splitB
              (.box 225 145)
              (.splitA
                (.splitB
                  (.box 129 209)
                  (.splitA
                    (.splitB
                      (.box 241 289)
                      (.box 241 321)
                    )
                    (.box 209 257)
                  )
                )
                (.box 193 193)
              )
            )
          )
        )
      )
      (.splitA
        (.splitB
          (.splitA
            (.splitB
              (.box 113 257)
              (.box 113 161)
            )
            (.splitB
              (.splitA
                (.box 89 257)
                (.box 73 257)
              )
              (.box 81 161)
            )
          )
          (.box 97 97)
        )
        (.splitB
          (.splitA
            (.splitB
              (.splitA
                (.splitB
                  (.box 177 0)
                  (.box 177 225)
                )
                (.splitB
                  (.box 145 0)
                  (.box 145 225)
                )
              )
              (.box 161 161)
            )
            (.splitB
              (.box 225 257)
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
          (.box 129 81)
          (.splitA
            (.splitB
              (.box 193 161)
              (.box 193 193)
            )
            (.box 161 129)
          )
        )
        (.box 97 65)
      )
      (.splitA
        (.splitB
          (.box 0 193)
          (.box 129 97)
        )
        (.box 97 65)
      )
    )
  )

theorem g2Upper23Chart0_ok : checkChart g2Upper23 0 1 2 g2Upper23Chart0 = true := by decide +kernel

def g2Upper23Chart1 : RowTree :=
  (.splitA
    (.splitB
      (.splitA
        (.splitB
          (.box 97 97)
          (.splitA
            (.splitB
              (.box 113 161)
              (.box 113 257)
            )
            (.splitB
              (.box 81 161)
              (.splitA
                (.box 89 257)
                (.box 73 257)
              )
            )
          )
        )
        (.splitB
          (.box 129 97)
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
              (.box 225 257)
            )
          )
        )
      )
      (.splitA
        (.splitB
          (.splitA
            (.splitB
              (.splitA
                (.box 121 194)
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
                (.box 73 161)
              )
            )
          )
          (.splitA
            (.splitB
              (.splitA
                (.splitB
                  (.splitA
                    (.box 125 73)
                    (.box 117 73)
                  )
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
                  (.box 106 76)
                  (.splitA
                    (.box 111 90)
                    (.box 101 89)
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
                      (.box 118 101)
                      (.splitA
                        (.box 119 110)
                        (.box 115 109)
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
                            (.box 122 119)
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
                                (.box 127 122)
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
                            (.box 122 123)
                          )
                          (.splitA
                            (.box 124 127)
                            (.box 122 127)
                          )
                        )
                      )
                    )
                    (.splitB
                      (.splitA
                        (.splitB
                          (.box 119 115)
                          (.box 119 119)
                        )
                        (.box 115 117)
                      )
                      (.splitA
                        (.splitB
                          (.box 119 123)
                          (.box 119 127)
                        )
                        (.box 115 125)
                      )
                    )
                  )
                )
                (.splitB
                  (.splitA
                    (.splitB
                      (.box 109 101)
                      (.box 109 109)
                    )
                    (.box 101 105)
                  )
                  (.splitA
                    (.splitB
                      (.box 109 117)
                      (.box 109 125)
                    )
                    (.box 101 121)
                  )
                )
              )
            )
            (.splitB
              (.splitA
                (.splitB
                  (.box 89 73)
                  (.box 89 89)
                )
                (.box 73 81)
              )
              (.splitA
                (.splitB
                  (.box 89 105)
                  (.box 89 121)
                )
                (.box 73 113)
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
                (.box 153 258)
              )
              (.box 177 161)
            )
            (.splitB
              (.box 225 257)
              (.box 193 161)
            )
          )
          (.splitA
            (.splitB
              (.box 161 81)
              (.box 161 113)
            )
            (.box 193 97)
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
      (.splitA
        (.splitB
          (.box 193 193)
          (.box 129 97)
        )
        (.box 97 65)
      )
    )
  )

theorem g2Upper23Chart1_ok : checkChart g2Upper23 1 0 2 g2Upper23Chart1 = true := by decide +kernel

def g2Upper23Chart2 : RowTree :=
  (.splitA
    (.splitB
      (.splitA
        (.splitB
          (.box 97 97)
          (.box 81 193)
        )
        (.splitB
          (.box 129 97)
          (.splitA
            (.box 161 193)
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
          (.splitA
            (.splitB
              (.box 113 193)
              (.splitA
                (.box 121 161)
                (.box 105 177)
              )
            )
            (.splitB
              (.box 81 225)
              (.splitA
                (.box 89 177)
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
                  (.box 118 93)
                )
                (.splitB
                  (.box 105 77)
                  (.splitA
                    (.box 109 93)
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
                      (.box 124 111)
                    )
                    (.splitB
                      (.box 117 103)
                      (.splitA
                        (.box 119 111)
                        (.splitB
                          (.box 115 107)
                          (.box 115 111)
                        )
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
                            (.box 124 120)
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
                                (.box 127 122)
                                (.box 125 122)
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
                                (.splitB
                                  (.box 124 122)
                                  (.box 124 123)
                                )
                              )
                              (.box 124 124)
                            )
                            (.splitB
                              (.splitA
                                (.box 123 122)
                                (.box 122 122)
                              )
                              (.splitA
                                (.box 123 124)
                                (.box 122 124)
                              )
                            )
                          )
                          (.splitA
                            (.splitB
                              (.box 124 126)
                              (.box 124 128)
                            )
                            (.splitB
                              (.splitA
                                (.box 123 126)
                                (.box 122 126)
                              )
                              (.box 122 128)
                            )
                          )
                        )
                      )
                    )
                    (.splitB
                      (.splitA
                        (.splitB
                          (.splitA
                            (.box 120 115)
                            (.box 118 115)
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
                            (.box 116 115)
                            (.box 114 115)
                          )
                          (.splitA
                            (.box 116 119)
                            (.box 114 119)
                          )
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
                        (.splitB
                          (.box 115 122)
                          (.box 115 127)
                        )
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
                        (.splitB
                          (.box 111 107)
                          (.box 111 111)
                        )
                        (.box 107 109)
                      )
                    )
                    (.splitB
                      (.box 102 101)
                      (.box 102 109)
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
                    (.box 103 118)
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
                    (.splitB
                      (.box 93 85)
                      (.box 93 93)
                    )
                    (.box 85 89)
                  )
                )
                (.splitB
                  (.splitA
                    (.box 77 73)
                    (.box 69 73)
                  )
                  (.box 76 88)
                )
              )
              (.splitA
                (.splitB
                  (.splitA
                    (.splitB
                      (.box 93 101)
                      (.box 93 109)
                    )
                    (.box 85 105)
                  )
                  (.box 93 121)
                )
                (.box 77 106)
              )
            )
          )
        )
        (.splitB
          (.splitA
            (.splitB
              (.splitA
                (.box 177 225)
                (.box 136 224)
              )
              (.splitA
                (.splitB
                  (.box 177 145)
                  (.box 177 177)
                )
                (.box 146 162)
              )
            )
            (.splitB
              (.splitA
                (.box 225 194)
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
                (.splitB
                  (.box 177 73)
                  (.box 177 89)
                )
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
              (.box 257 193)
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

theorem g2Upper23Chart2_ok : checkChart g2Upper23 2 0 1 g2Upper23Chart2 = true := by decide +kernel

end HlawkaSchatten.BelowExponent.FacetNumeric
