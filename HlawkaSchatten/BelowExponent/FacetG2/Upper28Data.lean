/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.FacetNumeric

/-! Certificate data for the G2 facet triangles: `Upper28Data`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true

@[expose] public section

namespace HlawkaSchatten.BelowExponent.FacetNumeric

def g2Upper28 : Prism := {
  vertices := [⟨10422500, 1270000, 307500, 0⟩, ⟨10321000, 1313000, 366000, 0⟩, ⟨10321000, 1352000, 327000, 0⟩, ⟨10401655, 1267460, 306885, 24000⟩, ⟨10300358, 1310374, 365268, 24000⟩, ⟨10300358, 1349296, 326346, 24000⟩]
  profileDen := 12000000
  pi := [40330985, 251072453, 247929321, 534409065]
  slope := [493297827, -194293943, -303927578]
  radiusNum := 1
  radiusDen := 16
}

set_option maxRecDepth 40000
set_option maxHeartbeats 0

theorem g2Upper28_data_ok : dataOK g2Upper28 = true := by decide +kernel

def g2Upper28Chart0 : RowTree :=
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
                              (.splitA
                                (.splitB
                                  (.box 1 123)
                                  (.box 1 122)
                                )
                                (.splitB
                                  (.box 128 123)
                                  (.box 128 122)
                                )
                              )
                            )
                            (.splitB
                              (.box 126 124)
                              (.splitA
                                (.box 127 122)
                                (.box 126 122)
                              )
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
                          (.splitA
                            (.box 128 115)
                            (.box 126 115)
                          )
                        )
                        (.splitB
                          (.splitA
                            (.splitB
                              (.box 124 120)
                              (.box 124 118)
                            )
                            (.box 122 119)
                          )
                          (.box 124 115)
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
                        (.splitB
                          (.box 127 111)
                          (.box 127 107)
                        )
                        (.splitB
                          (.box 123 111)
                          (.box 123 107)
                        )
                      )
                      (.box 125 102)
                    )
                    (.splitB
                      (.splitA
                        (.box 119 110)
                        (.box 115 109)
                      )
                      (.box 117 102)
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
                  (.splitA
                    (.box 125 73)
                    (.box 117 73)
                  )
                )
                (.splitB
                  (.splitA
                    (.box 109 90)
                    (.box 101 89)
                  )
                  (.box 106 74)
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
                (.box 81 80)
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
                (.splitB
                  (.box 121 225)
                  (.box 121 257)
                )
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
                  (.box 89 258)
                )
                (.splitB
                  (.splitA
                    (.box 77 224)
                    (.splitB
                      (.box 69 241)
                      (.box 69 209)
                    )
                  )
                  (.splitA
                    (.splitB
                      (.box 77 289)
                      (.box 77 321)
                    )
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
          (.splitA
            (.splitB
              (.splitA
                (.splitB
                  (.box 177 177)
                  (.box 177 137)
                )
                (.splitB
                  (.box 145 177)
                  (.box 145 137)
                )
              )
              (.splitA
                (.splitB
                  (.splitA
                    (.splitB
                      (.box 185 241)
                      (.splitA
                        (.box 189 201)
                        (.splitB
                          (.box 181 217)
                          (.box 181 201)
                        )
                      )
                    )
                    (.splitB
                      (.box 169 241)
                      (.splitA
                        (.splitB
                          (.box 173 217)
                          (.box 171 197)
                        )
                        (.splitB
                          (.box 165 217)
                          (.splitA
                            (.box 167 197)
                            (.box 163 197)
                          )
                        )
                      )
                    )
                  )
                  (.splitA
                    (.splitB
                      (.splitA
                        (.box 185 290)
                        (.splitB
                          (.box 181 305)
                          (.box 181 273)
                        )
                      )
                      (.box 185 353)
                    )
                    (.splitB
                      (.splitA
                        (.splitB
                          (.splitA
                            (.box 173 305)
                            (.splitB
                              (.box 171 313)
                              (.box 171 298)
                            )
                          )
                          (.box 171 281)
                        )
                        (.splitB
                          (.splitA
                            (.splitB
                              (.splitA
                                (.box 168 312)
                                (.splitB
                                  (.box 166 317)
                                  (.box 166 309)
                                )
                              )
                              (.splitA
                                (.box 168 298)
                                (.box 166 300)
                              )
                            )
                            (.splitB
                              (.splitA
                                (.splitB
                                  (.box 164 317)
                                  (.box 164 309)
                                )
                                (.splitB
                                  (.box 162 317)
                                  (.box 162 309)
                                )
                              )
                              (.splitA
                                (.splitB
                                  (.box 164 301)
                                  (.box 164 293)
                                )
                                (.box 162 300)
                              )
                            )
                          )
                          (.splitA
                            (.box 167 281)
                            (.box 163 281)
                          )
                        )
                      )
                      (.box 168 353)
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
                          (.splitA
                            (.box 159 197)
                            (.box 155 197)
                          )
                        )
                        (.splitB
                          (.box 149 217)
                          (.box 149 197)
                        )
                      )
                    )
                    (.splitB
                      (.box 137 241)
                      (.box 141 201)
                    )
                  )
                  (.splitA
                    (.splitB
                      (.splitA
                        (.splitB
                          (.splitA
                            (.splitB
                              (.box 160 312)
                              (.box 160 298)
                            )
                            (.splitB
                              (.box 155 313)
                              (.box 155 297)
                            )
                          )
                          (.box 159 281)
                        )
                        (.splitB
                          (.box 153 305)
                          (.box 149 281)
                        )
                      )
                      (.box 157 353)
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
                  (.splitA
                    (.box 129 210)
                    (.box 209 225)
                  )
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
                (.box 69 257)
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
          (.box 193 97)
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

theorem g2Upper28Chart0_ok : checkChart g2Upper28 0 1 2 g2Upper28Chart0 = true := by decide +kernel

def g2Upper28Chart1 : RowTree :=
  (.splitA
    (.splitB
      (.splitA
        (.splitB
          (.box 97 81)
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
          (.box 130 82)
          (.splitA
            (.splitB
              (.box 161 161)
              (.splitA
                (.box 176 258)
                (.splitB
                  (.box 145 225)
                  (.box 145 257)
                )
              )
            )
            (.splitB
              (.box 193 161)
              (.splitA
                (.box 225 257)
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
                  (.box 121 185)
                )
                (.splitB
                  (.box 105 145)
                  (.box 105 178)
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
                (.box 77 161)
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
                    (.splitB
                      (.box 109 85)
                      (.box 109 93)
                    )
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
                      (.splitA
                        (.box 119 101)
                        (.box 115 101)
                      )
                      (.splitA
                        (.splitB
                          (.box 119 107)
                          (.box 119 111)
                        )
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
                          (.box 120 119)
                        )
                        (.box 116 117)
                      )
                      (.splitA
                        (.splitB
                          (.box 120 123)
                          (.box 120 127)
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
                      (.box 111 109)
                    )
                    (.box 103 105)
                  )
                  (.splitA
                    (.splitB
                      (.box 111 117)
                      (.box 111 125)
                    )
                    (.box 101 121)
                  )
                )
              )
            )
            (.splitB
              (.splitA
                (.splitB
                  (.box 89 74)
                  (.box 93 89)
                )
                (.box 77 81)
              )
              (.splitA
                (.splitB
                  (.box 93 105)
                  (.box 93 121)
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
                (.splitB
                  (.box 145 257)
                  (.box 145 225)
                )
              )
              (.box 176 160)
            )
            (.splitB
              (.box 225 257)
              (.box 193 161)
            )
          )
          (.splitA
            (.splitB
              (.box 177 81)
              (.box 177 113)
            )
            (.box 129 96)
          )
        )
      )
    )
    (.splitB
      (.splitA
        (.splitB
          (.box 129 81)
          (.splitA
            (.box 257 129)
            (.box 161 129)
          )
        )
        (.box 97 65)
      )
      (.splitA
        (.splitB
          (.splitA
            (.box 0 193)
            (.box 161 129)
          )
          (.box 129 96)
        )
        (.box 97 65)
      )
    )
  )

theorem g2Upper28Chart1_ok : checkChart g2Upper28 1 0 2 g2Upper28Chart1 = true := by decide +kernel

def g2Upper28Chart2 : RowTree :=
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
          (.box 193 97)
          (.splitA
            (.splitB
              (.box 161 161)
              (.box 161 257)
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
              (.box 113 193)
              (.splitA
                (.box 121 161)
                (.box 105 177)
              )
            )
            (.splitB
              (.splitA
                (.box 89 193)
                (.box 73 225)
              )
              (.splitA
                (.splitB
                  (.box 89 145)
                  (.box 89 185)
                )
                (.splitB
                  (.box 73 145)
                  (.box 72 185)
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
                  (.box 104 77)
                  (.splitA
                    (.splitB
                      (.box 109 85)
                      (.box 109 93)
                    )
                    (.splitB
                      (.box 101 85)
                      (.box 101 95)
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
                      (.box 116 103)
                      (.splitA
                        (.splitB
                          (.box 119 107)
                          (.box 119 111)
                        )
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
                                (.splitB
                                  (.box 124 122)
                                  (.box 124 123)
                                )
                              )
                              (.box 124 124)
                            )
                            (.splitB
                              (.splitA
                                (.splitB
                                  (.box 123 122)
                                  (.box 123 123)
                                )
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
                            (.splitB
                              (.box 118 122)
                              (.box 118 124)
                            )
                          )
                          (.splitA
                            (.box 120 126)
                            (.box 118 127)
                          )
                        )
                        (.splitB
                          (.box 116 122)
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
                      (.splitA
                        (.box 111 123)
                        (.box 107 125)
                      )
                    )
                    (.splitB
                      (.box 103 115)
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
                    (.box 93 77)
                    (.box 85 74)
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
                    (.box 85 102)
                  )
                  (.box 92 117)
                )
                (.splitB
                  (.box 77 105)
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
                (.box 169 224)
                (.splitB
                  (.box 145 257)
                  (.box 145 225)
                )
              )
              (.splitA
                (.splitB
                  (.box 177 145)
                  (.box 178 177)
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
                (.box 241 160)
                (.box 257 161)
              )
            )
          )
          (.splitA
            (.splitB
              (.splitA
                (.splitB
                  (.box 177 72)
                  (.box 177 89)
                )
                (.box 145 74)
              )
              (.splitA
                (.box 177 105)
                (.box 145 113)
              )
            )
            (.splitB
              (.box 225 81)
              (.box 193 113)
            )
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
                (.box 257 257)
                (.box 225 193)
              )
            )
            (.box 145 129)
          )
        )
        (.splitB
          (.box 97 97)
          (.splitA
            (.box 81 129)
            (.box 113 129)
          )
        )
      )
      (.splitA
        (.splitB
          (.splitA
            (.splitB
              (.splitA
                (.box 321 193)
                (.box 225 193)
              )
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

theorem g2Upper28Chart2_ok : checkChart g2Upper28 2 0 1 g2Upper28Chart2 = true := by decide +kernel

end HlawkaSchatten.BelowExponent.FacetNumeric
