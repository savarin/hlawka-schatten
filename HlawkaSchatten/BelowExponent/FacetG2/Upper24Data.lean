/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.FacetNumeric

/-! Certificate data for the G2 facet triangles: `Upper24Data`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true

@[expose] public section

namespace HlawkaSchatten.BelowExponent.FacetNumeric

def g2Upper24 : Prism := {
  vertices := [⟨5059000, 758000, 183000, 0⟩, ⟨4856000, 844000, 300000, 0⟩, ⟨4957500, 840000, 202500, 0⟩, ⟨5048882, 756484, 182634, 12000⟩, ⟨4846288, 842312, 299400, 12000⟩, ⟨4947585, 838320, 202095, 12000⟩]
  profileDen := 6000000
  pi := [47437296, 229980150, 260611832, 535712546]
  slope := [460340878, -189192563, -273465050]
  radiusNum := 1
  radiusDen := 32
}

set_option maxRecDepth 40000
set_option maxHeartbeats 0

theorem g2Upper24_data_ok : dataOK g2Upper24 = true := by decide +kernel

def g2Upper24Chart0 : RowTree :=
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
                              (.splitA
                                (.splitB
                                  (.splitA
                                    (.splitB
                                      (.box 1 1)
                                      (.box 1 128)
                                    )
                                    (.splitB
                                      (.box 128 1)
                                      (.box 128 128)
                                    )
                                  )
                                  (.splitA
                                    (.splitB
                                      (.box 1 128)
                                      (.box 1 127)
                                    )
                                    (.splitB
                                      (.box 128 128)
                                      (.box 128 127)
                                    )
                                  )
                                )
                                (.splitB
                                  (.splitA
                                    (.splitB
                                      (.box 128 1)
                                      (.box 128 128)
                                    )
                                    (.splitB
                                      (.box 127 1)
                                      (.box 127 128)
                                    )
                                  )
                                  (.splitA
                                    (.splitB
                                      (.box 128 128)
                                      (.box 128 127)
                                    )
                                    (.splitB
                                      (.box 127 128)
                                      (.box 127 127)
                                    )
                                  )
                                )
                              )
                              (.splitA
                                (.splitB
                                  (.splitA
                                    (.splitB
                                      (.box 1 127)
                                      (.box 1 126)
                                    )
                                    (.splitB
                                      (.box 128 127)
                                      (.box 128 126)
                                    )
                                  )
                                  (.splitA
                                    (.splitB
                                      (.box 1 126)
                                      (.box 1 125)
                                    )
                                    (.splitB
                                      (.box 128 126)
                                      (.box 128 125)
                                    )
                                  )
                                )
                                (.splitB
                                  (.splitA
                                    (.box 128 127)
                                    (.box 127 127)
                                  )
                                  (.splitA
                                    (.splitB
                                      (.box 128 126)
                                      (.box 128 125)
                                    )
                                    (.splitB
                                      (.box 127 126)
                                      (.box 127 125)
                                    )
                                  )
                                )
                              )
                            )
                            (.splitB
                              (.splitA
                                (.box 127 128)
                                (.box 126 128)
                              )
                              (.splitA
                                (.splitB
                                  (.box 127 127)
                                  (.box 127 126)
                                )
                                (.box 126 126)
                              )
                            )
                          )
                          (.splitA
                            (.splitB
                              (.splitA
                                (.splitB
                                  (.splitA
                                    (.box 1 125)
                                    (.box 128 125)
                                  )
                                  (.splitA
                                    (.box 1 124)
                                    (.box 128 124)
                                  )
                                )
                                (.splitB
                                  (.splitA
                                    (.box 128 125)
                                    (.box 127 125)
                                  )
                                  (.box 128 124)
                                )
                              )
                              (.splitA
                                (.splitB
                                  (.box 1 123)
                                  (.box 1 122)
                                )
                                (.box 128 122)
                              )
                            )
                            (.splitB
                              (.splitA
                                (.box 127 124)
                                (.box 126 124)
                              )
                              (.box 126 122)
                            )
                          )
                        )
                        (.splitB
                          (.splitA
                            (.splitB
                              (.box 124 128)
                              (.box 124 126)
                            )
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
                          (.box 127 116)
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
                      (.box 125 103)
                    )
                    (.splitB
                      (.splitA
                        (.box 119 109)
                        (.box 115 109)
                      )
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
                    (.splitB
                      (.box 109 109)
                      (.box 109 101)
                    )
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
                    (.splitB
                      (.box 117 93)
                      (.box 117 85)
                    )
                  )
                  (.box 121 74)
                )
                (.splitB
                  (.box 108 90)
                  (.box 105 74)
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
                (.box 120 194)
                (.splitB
                  (.box 105 225)
                  (.box 105 257)
                )
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
                  (.splitA
                    (.box 77 225)
                    (.box 67 210)
                  )
                  (.splitA
                    (.splitB
                      (.box 77 289)
                      (.box 77 321)
                    )
                    (.splitB
                      (.box 69 289)
                      (.box 69 353)
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
            (.box 129 82)
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
                      (.box 181 201)
                    )
                    (.splitB
                      (.box 169 241)
                      (.splitA
                        (.box 173 200)
                        (.box 165 200)
                      )
                    )
                  )
                  (.splitA
                    (.splitB
                      (.splitA
                        (.splitB
                          (.box 189 305)
                          (.box 189 273)
                        )
                        (.splitB
                          (.box 179 298)
                          (.splitA
                            (.box 183 273)
                            (.splitB
                              (.box 179 281)
                              (.box 179 265)
                            )
                          )
                        )
                      )
                      (.box 181 353)
                    )
                    (.splitB
                      (.splitA
                        (.splitB
                          (.splitA
                            (.splitB
                              (.box 175 313)
                              (.box 175 294)
                            )
                            (.splitB
                              (.box 171 313)
                              (.splitA
                                (.box 172 294)
                                (.splitB
                                  (.box 170 301)
                                  (.box 170 291)
                                )
                              )
                            )
                          )
                          (.splitA
                            (.splitB
                              (.box 174 282)
                              (.box 175 265)
                            )
                            (.splitB
                              (.splitA
                                (.splitB
                                  (.box 172 285)
                                  (.box 172 277)
                                )
                                (.splitB
                                  (.splitA
                                    (.box 171 286)
                                    (.box 169 286)
                                  )
                                  (.box 170 277)
                                )
                              )
                              (.box 171 273)
                            )
                          )
                        )
                        (.splitB
                          (.splitA
                            (.splitB
                              (.box 167 313)
                              (.splitA
                                (.splitB
                                  (.box 168 301)
                                  (.box 168 291)
                                )
                                (.splitB
                                  (.box 166 301)
                                  (.box 166 291)
                                )
                              )
                            )
                            (.splitB
                              (.box 163 313)
                              (.box 164 294)
                            )
                          )
                          (.splitA
                            (.splitB
                              (.splitA
                                (.splitB
                                  (.splitA
                                    (.splitB
                                      (.box 169 287)
                                      (.box 169 283)
                                    )
                                    (.box 168 286)
                                  )
                                  (.box 168 277)
                                )
                                (.splitB
                                  (.box 166 286)
                                  (.box 166 277)
                                )
                              )
                              (.box 167 273)
                            )
                            (.splitB
                              (.splitA
                                (.splitB
                                  (.box 164 285)
                                  (.box 164 277)
                                )
                                (.box 162 281)
                              )
                              (.box 163 265)
                            )
                          )
                        )
                      )
                      (.splitA
                        (.splitB
                          (.box 173 257)
                          (.box 173 385)
                        )
                        (.splitB
                          (.box 165 257)
                          (.box 165 385)
                        )
                      )
                    )
                  )
                )
                (.splitB
                  (.splitA
                    (.splitB
                      (.box 153 241)
                      (.box 157 201)
                    )
                    (.box 137 209)
                  )
                  (.splitA
                    (.splitB
                      (.splitA
                        (.splitB
                          (.splitA
                            (.box 161 298)
                            (.box 155 305)
                          )
                          (.splitA
                            (.splitB
                              (.box 159 281)
                              (.box 159 265)
                            )
                            (.box 155 273)
                          )
                        )
                        (.splitB
                          (.box 149 305)
                          (.box 149 273)
                        )
                      )
                      (.box 157 353)
                    )
                    (.splitB
                      (.box 137 289)
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
                  (.box 225 209)
                  (.box 129 258)
                )
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
              (.box 113 257)
              (.box 113 161)
            )
            (.splitB
              (.splitA
                (.box 89 257)
                (.splitB
                  (.box 73 0)
                  (.box 73 225)
                )
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
          (.box 193 193)
          (.box 129 97)
        )
        (.box 97 65)
      )
    )
  )

theorem g2Upper24Chart0_ok : checkChart g2Upper24 0 1 2 g2Upper24Chart0 = true := by decide +kernel

def g2Upper24Chart1 : RowTree :=
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
              (.box 225 193)
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
                  (.box 121 257)
                  (.box 121 225)
                )
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
                  (.splitA
                    (.box 109 73)
                    (.box 101 73)
                  )
                  (.splitA
                    (.box 111 89)
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
                                  (.box 128 123)
                                )
                                (.splitB
                                  (.box 128 122)
                                  (.splitA
                                    (.box 128 123)
                                    (.box 127 123)
                                  )
                                )
                              )
                              (.splitA
                                (.splitB
                                  (.splitA
                                    (.box 1 124)
                                    (.box 128 124)
                                  )
                                  (.splitA
                                    (.splitB
                                      (.box 1 124)
                                      (.box 1 125)
                                    )
                                    (.splitB
                                      (.box 128 124)
                                      (.box 128 125)
                                    )
                                  )
                                )
                                (.splitB
                                  (.splitA
                                    (.box 128 124)
                                    (.box 127 124)
                                  )
                                  (.splitA
                                    (.splitB
                                      (.box 128 124)
                                      (.box 128 125)
                                    )
                                    (.splitB
                                      (.box 127 124)
                                      (.box 127 125)
                                    )
                                  )
                                )
                              )
                            )
                            (.splitB
                              (.splitA
                                (.box 127 122)
                                (.box 126 122)
                              )
                              (.splitA
                                (.splitB
                                  (.box 127 124)
                                  (.splitA
                                    (.box 127 125)
                                    (.box 126 125)
                                  )
                                )
                                (.box 126 124)
                              )
                            )
                          )
                          (.splitA
                            (.splitB
                              (.splitA
                                (.splitB
                                  (.splitA
                                    (.splitB
                                      (.splitA
                                        (.box 1 125)
                                        (.splitB
                                          (.box 1 125)
                                          (.box 1 125)
                                        )
                                      )
                                      (.box 1 126)
                                    )
                                    (.splitB
                                      (.splitA
                                        (.splitB
                                          (.box 128 125)
                                          (.box 128 125)
                                        )
                                        (.box 128 125)
                                      )
                                      (.box 128 126)
                                    )
                                  )
                                  (.splitA
                                    (.splitB
                                      (.box 1 126)
                                      (.box 1 127)
                                    )
                                    (.splitB
                                      (.box 128 126)
                                      (.box 128 127)
                                    )
                                  )
                                )
                                (.splitB
                                  (.splitA
                                    (.splitB
                                      (.box 128 125)
                                      (.box 128 126)
                                    )
                                    (.splitB
                                      (.box 127 125)
                                      (.box 127 126)
                                    )
                                  )
                                  (.splitA
                                    (.box 128 127)
                                    (.box 127 127)
                                  )
                                )
                              )
                              (.splitA
                                (.splitB
                                  (.splitA
                                    (.splitB
                                      (.box 1 127)
                                      (.box 1 128)
                                    )
                                    (.splitB
                                      (.box 128 127)
                                      (.box 128 128)
                                    )
                                  )
                                  (.splitA
                                    (.splitB
                                      (.box 1 128)
                                      (.box 1 1)
                                    )
                                    (.splitB
                                      (.box 128 128)
                                      (.box 128 1)
                                    )
                                  )
                                )
                                (.splitB
                                  (.splitA
                                    (.splitB
                                      (.box 128 127)
                                      (.box 128 128)
                                    )
                                    (.splitB
                                      (.box 127 127)
                                      (.box 127 128)
                                    )
                                  )
                                  (.splitA
                                    (.box 128 128)
                                    (.box 127 128)
                                  )
                                )
                              )
                            )
                            (.splitB
                              (.splitA
                                (.splitB
                                  (.splitA
                                    (.box 127 126)
                                    (.box 126 126)
                                  )
                                  (.box 127 127)
                                )
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
                (.box 145 258)
              )
              (.box 177 161)
            )
            (.splitB
              (.box 193 257)
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
          (.box 193 129)
        )
        (.box 97 65)
      )
      (.splitA
        (.splitB
          (.box 193 129)
          (.box 129 97)
        )
        (.box 97 65)
      )
    )
  )

theorem g2Upper24Chart1_ok : checkChart g2Upper24 1 0 2 g2Upper24Chart1 = true := by decide +kernel

def g2Upper24Chart2 : RowTree :=
  (.splitA
    (.splitB
      (.splitA
        (.splitB
          (.box 97 97)
          (.box 81 193)
        )
        (.splitB
          (.box 129 65)
          (.splitA
            (.box 145 193)
            (.splitB
              (.box 193 161)
              (.splitA
                (.box 225 193)
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
              (.box 113 193)
              (.splitA
                (.box 121 161)
                (.box 105 177)
              )
            )
            (.splitB
              (.box 81 225)
              (.splitA
                (.box 85 177)
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
                  (.box 118 94)
                )
                (.splitB
                  (.box 105 77)
                  (.splitA
                    (.box 107 93)
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
                        (.box 118 111)
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
                              (.splitA
                                (.box 128 124)
                                (.splitB
                                  (.box 128 124)
                                  (.box 127 125)
                                )
                              )
                            )
                            (.splitB
                              (.splitA
                                (.box 127 123)
                                (.box 125 123)
                              )
                              (.splitA
                                (.splitB
                                  (.box 126 124)
                                  (.splitA
                                    (.box 127 125)
                                    (.box 126 125)
                                  )
                                )
                                (.splitB
                                  (.splitA
                                    (.box 126 124)
                                    (.box 125 124)
                                  )
                                  (.splitA
                                    (.splitB
                                      (.box 126 124)
                                      (.box 126 125)
                                    )
                                    (.splitB
                                      (.box 125 124)
                                      (.box 125 125)
                                    )
                                  )
                                )
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
                                  (.splitA
                                    (.box 128 126)
                                    (.box 127 126)
                                  )
                                  (.splitA
                                    (.splitB
                                      (.box 128 126)
                                      (.box 128 127)
                                    )
                                    (.splitB
                                      (.box 127 126)
                                      (.box 127 127)
                                    )
                                  )
                                )
                              )
                              (.splitA
                                (.splitB
                                  (.splitA
                                    (.splitB
                                      (.box 1 127)
                                      (.box 1 128)
                                    )
                                    (.splitB
                                      (.box 128 127)
                                      (.box 128 128)
                                    )
                                  )
                                  (.splitA
                                    (.splitB
                                      (.box 1 128)
                                      (.box 1 1)
                                    )
                                    (.splitB
                                      (.box 128 128)
                                      (.box 128 1)
                                    )
                                  )
                                )
                                (.splitB
                                  (.splitA
                                    (.splitB
                                      (.box 128 127)
                                      (.box 128 128)
                                    )
                                    (.splitB
                                      (.box 127 127)
                                      (.box 127 128)
                                    )
                                  )
                                  (.splitA
                                    (.splitB
                                      (.box 128 128)
                                      (.box 128 1)
                                    )
                                    (.splitB
                                      (.box 127 128)
                                      (.box 127 1)
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
                                      (.splitA
                                        (.box 127 125)
                                        (.splitB
                                          (.box 127 125)
                                          (.box 127 125)
                                        )
                                      )
                                      (.box 127 126)
                                    )
                                    (.splitB
                                      (.splitA
                                        (.splitB
                                          (.box 126 125)
                                          (.box 126 125)
                                        )
                                        (.box 126 125)
                                      )
                                      (.box 126 126)
                                    )
                                  )
                                  (.splitA
                                    (.splitB
                                      (.box 127 126)
                                      (.box 127 127)
                                    )
                                    (.splitB
                                      (.box 126 126)
                                      (.box 126 127)
                                    )
                                  )
                                )
                                (.splitB
                                  (.splitA
                                    (.splitB
                                      (.splitA
                                        (.box 126 125)
                                        (.splitB
                                          (.box 126 125)
                                          (.box 126 125)
                                        )
                                      )
                                      (.box 126 126)
                                    )
                                    (.splitB
                                      (.splitA
                                        (.splitB
                                          (.box 125 125)
                                          (.box 125 125)
                                        )
                                        (.box 125 125)
                                      )
                                      (.splitA
                                        (.box 125 126)
                                        (.box 125 126)
                                      )
                                    )
                                  )
                                  (.splitA
                                    (.box 126 127)
                                    (.splitB
                                      (.splitA
                                        (.box 125 126)
                                        (.box 125 126)
                                      )
                                      (.splitA
                                        (.box 125 127)
                                        (.box 125 127)
                                      )
                                    )
                                  )
                                )
                              )
                              (.splitA
                                (.splitB
                                  (.splitA
                                    (.box 127 127)
                                    (.box 126 127)
                                  )
                                  (.box 127 128)
                                )
                                (.splitB
                                  (.splitA
                                    (.box 126 128)
                                    (.box 125 127)
                                  )
                                  (.box 126 128)
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
                                  (.box 125 122)
                                  (.box 124 123)
                                )
                                (.splitB
                                  (.box 124 122)
                                  (.splitA
                                    (.box 124 123)
                                    (.box 123 123)
                                  )
                                )
                              )
                              (.splitA
                                (.splitB
                                  (.splitA
                                    (.box 125 124)
                                    (.box 124 124)
                                  )
                                  (.splitA
                                    (.splitB
                                      (.box 125 124)
                                      (.box 125 125)
                                    )
                                    (.splitB
                                      (.box 124 124)
                                      (.box 124 125)
                                    )
                                  )
                                )
                                (.splitB
                                  (.splitA
                                    (.box 124 124)
                                    (.box 123 124)
                                  )
                                  (.splitA
                                    (.box 124 125)
                                    (.box 123 125)
                                  )
                                )
                              )
                            )
                            (.splitB
                              (.splitA
                                (.splitB
                                  (.box 123 122)
                                  (.splitA
                                    (.box 123 123)
                                    (.box 122 123)
                                  )
                                )
                                (.box 122 122)
                              )
                              (.splitA
                                (.splitB
                                  (.box 123 123)
                                  (.box 123 125)
                                )
                                (.box 122 124)
                              )
                            )
                          )
                          (.splitA
                            (.splitB
                              (.splitA
                                (.splitB
                                  (.splitA
                                    (.splitB
                                      (.box 125 125)
                                      (.box 125 126)
                                    )
                                    (.splitB
                                      (.box 124 125)
                                      (.box 124 126)
                                    )
                                  )
                                  (.splitA
                                    (.box 125 126)
                                    (.box 124 126)
                                  )
                                )
                                (.splitB
                                  (.box 124 125)
                                  (.box 124 127)
                                )
                              )
                              (.splitA
                                (.splitB
                                  (.box 125 127)
                                  (.box 125 1)
                                )
                                (.box 124 128)
                              )
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
                            (.splitB
                              (.box 118 118)
                              (.box 118 120)
                            )
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
                            (.box 119 122)
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
                        (.splitB
                          (.box 107 107)
                          (.box 107 111)
                        )
                      )
                    )
                    (.splitB
                      (.splitA
                        (.box 103 101)
                        (.box 99 101)
                      )
                      (.splitA
                        (.box 103 109)
                        (.box 99 109)
                      )
                    )
                  )
                  (.splitA
                    (.splitB
                      (.splitA
                        (.splitB
                          (.box 111 115)
                          (.box 111 119)
                        )
                        (.box 107 116)
                      )
                      (.box 111 123)
                    )
                    (.splitB
                      (.box 101 115)
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
                    (.splitB
                      (.box 93 85)
                      (.box 93 93)
                    )
                    (.splitB
                      (.box 85 85)
                      (.box 85 93)
                    )
                  )
                )
                (.splitB
                  (.splitA
                    (.box 77 73)
                    (.box 69 73)
                  )
                  (.splitA
                    (.box 77 89)
                    (.box 69 89)
                  )
                )
              )
              (.splitA
                (.splitB
                  (.splitA
                    (.splitB
                      (.box 93 101)
                      (.box 93 109)
                    )
                    (.box 85 104)
                  )
                  (.box 93 117)
                )
                (.splitB
                  (.box 73 101)
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
                (.box 177 225)
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
                (.splitB
                  (.box 145 145)
                  (.box 145 177)
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
                  (.box 257 257)
                  (.box 257 225)
                )
              )
              (.splitA
                (.box 225 160)
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
                (.box 145 73)
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
          (.box 129 81)
          (.splitA
            (.splitB
              (.box 193 161)
              (.splitA
                (.box 257 257)
                (.box 225 193)
              )
            )
            (.box 145 129)
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
              (.box 257 257)
              (.box 193 161)
            )
            (.box 161 193)
          )
          (.box 193 97)
        )
        (.box 97 129)
      )
    )
  )

theorem g2Upper24Chart2_ok : checkChart g2Upper24 2 0 1 g2Upper24Chart2 = true := by decide +kernel

end HlawkaSchatten.BelowExponent.FacetNumeric
