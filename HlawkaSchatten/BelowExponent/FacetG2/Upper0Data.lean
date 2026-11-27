/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.FacetNumeric

/-! Certificate data for the G2 facet triangles: `Upper0Data`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true

@[expose] public section

namespace HlawkaSchatten.BelowExponent.FacetNumeric

def g2Upper0 : Prism := {
  vertices := [⟨2326500, 543000, 130500, 0⟩, ⟨2322500, 547000, 130500, 0⟩, ⟨2225000, 625000, 150000, 0⟩, ⟨2321847, 541914, 130239, 6000⟩, ⟨2317855, 545906, 130239, 6000⟩, ⟨2220550, 623750, 149700, 6000⟩]
  profileDen := 3000000
  pi := [69147740, 223550485, 247883390, 533160209]
  slope := [401452455, -127663821, -281210041]
  radiusNum := 1
  radiusDen := 16
}

set_option maxRecDepth 40000
set_option maxHeartbeats 0

theorem g2Upper0_data_ok : dataOK g2Upper0 = true := by decide +kernel

def g2Upper0Chart0 : RowTree :=
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
                            (.box 126 127)
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
                            (.box 125 123)
                            (.box 122 123)
                          )
                        )
                      )
                      (.splitA
                        (.splitB
                          (.splitA
                            (.box 128 120)
                            (.box 126 120)
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
                        (.box 121 125)
                        (.box 115 125)
                      )
                      (.splitA
                        (.box 121 117)
                        (.box 115 117)
                      )
                    )
                  )
                  (.splitA
                    (.splitB
                      (.splitA
                        (.box 127 111)
                        (.box 123 111)
                      )
                      (.box 125 101)
                    )
                    (.splitB
                      (.box 117 110)
                      (.box 117 101)
                    )
                  )
                )
                (.splitB
                  (.splitA
                    (.box 113 121)
                    (.box 101 121)
                  )
                  (.splitA
                    (.box 113 105)
                    (.box 101 105)
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
                  (.box 109 89)
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
                (.box 93 161)
                (.box 69 161)
              )
              (.splitA
                (.splitB
                  (.box 89 225)
                  (.box 89 257)
                )
                (.splitB
                  (.box 73 209)
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
            (.box 193 97)
          )
          (.splitA
            (.splitB
              (.splitA
                (.box 177 145)
                (.box 145 145)
              )
              (.splitA
                (.splitB
                  (.splitA
                    (.box 185 209)
                    (.splitB
                      (.box 169 241)
                      (.box 169 193)
                    )
                  )
                  (.splitA
                    (.splitB
                      (.box 177 289)
                      (.box 185 353)
                    )
                    (.splitB
                      (.splitA
                        (.splitB
                          (.box 173 305)
                          (.box 173 273)
                        )
                        (.splitB
                          (.box 163 297)
                          (.splitA
                            (.splitB
                              (.box 167 281)
                              (.box 167 265)
                            )
                            (.splitB
                              (.box 162 278)
                              (.box 163 269)
                            )
                          )
                        )
                      )
                      (.splitA
                        (.box 173 353)
                        (.splitB
                          (.box 163 257)
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
                      (.box 153 193)
                    )
                    (.box 137 209)
                  )
                  (.splitA
                    (.splitB
                      (.splitA
                        (.splitB
                          (.splitA
                            (.box 159 297)
                            (.box 155 297)
                          )
                          (.splitA
                            (.splitB
                              (.splitA
                                (.box 160 278)
                                (.box 158 278)
                              )
                              (.box 159 269)
                            )
                            (.splitB
                              (.box 155 278)
                              (.box 155 269)
                            )
                          )
                        )
                        (.splitB
                          (.box 149 297)
                          (.box 152 273)
                        )
                      )
                      (.splitA
                        (.splitB
                          (.box 158 257)
                          (.box 157 385)
                        )
                        (.box 152 353)
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
                      (.box 145 353)
                    )
                  )
                )
              )
            )
            (.splitB
              (.box 225 161)
              (.splitA
                (.splitB
                  (.box 225 209)
                  (.box 129 257)
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
            (.box 113 193)
            (.splitB
              (.box 72 257)
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
              (.splitA
                (.box 129 257)
                (.box 257 0)
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
          (.box 129 97)
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

theorem g2Upper0Chart0_ok : checkChart g2Upper0 0 1 2 g2Upper0Chart0 = true := by decide +kernel

def g2Upper0Chart1 : RowTree :=
  (.splitA
    (.splitB
      (.splitA
        (.splitB
          (.box 97 97)
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
              (.box 162 257)
            )
            (.box 225 193)
          )
        )
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
                (.splitB
                  (.box 105 145)
                  (.box 105 177)
                )
              )
            )
            (.splitB
              (.splitA
                (.box 89 193)
                (.box 69 193)
              )
              (.splitA
                (.box 93 161)
                (.box 73 161)
              )
            )
          )
          (.splitA
            (.splitB
              (.splitA
                (.splitB
                  (.box 121 73)
                  (.splitA
                    (.box 125 92)
                    (.box 117 92)
                  )
                )
                (.splitB
                  (.box 105 77)
                  (.box 108 90)
                )
              )
              (.splitA
                (.splitB
                  (.splitA
                    (.splitB
                      (.box 125 101)
                      (.splitA
                        (.box 127 110)
                        (.box 123 110)
                      )
                    )
                    (.splitB
                      (.box 117 101)
                      (.box 118 110)
                    )
                  )
                  (.splitA
                    (.splitB
                      (.splitA
                        (.splitB
                          (.box 127 115)
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
                          (.box 123 115)
                          (.splitA
                            (.box 124 119)
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
                              (.box 128 126)
                              (.box 128 128)
                            )
                            (.box 126 127)
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
                    (.box 111 106)
                    (.box 101 105)
                  )
                  (.splitA
                    (.box 112 121)
                    (.box 101 121)
                  )
                )
              )
            )
            (.splitB
              (.splitA
                (.box 94 82)
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
                (.box 145 257)
              )
              (.box 161 161)
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

theorem g2Upper0Chart1_ok : checkChart g2Upper0 1 0 2 g2Upper0Chart1 = true := by decide +kernel

def g2Upper0Chart2 : RowTree :=
  (.splitA
    (.splitB
      (.splitA
        (.box 81 129)
        (.splitB
          (.box 129 97)
          (.splitA
            (.box 161 193)
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
              (.box 105 65)
            )
            (.splitB
              (.box 81 129)
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
                  (.box 117 97)
                )
                (.splitB
                  (.box 105 73)
                  (.splitA
                    (.box 109 93)
                    (.box 101 92)
                  )
                )
              )
              (.splitA
                (.splitB
                  (.splitA
                    (.splitB
                      (.box 125 101)
                      (.box 123 113)
                    )
                    (.splitB
                      (.box 117 101)
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
                          (.box 127 115)
                          (.box 126 121)
                        )
                        (.splitB
                          (.box 123 115)
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
                              (.box 126 122)
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
                          (.box 120 127)
                        )
                        (.box 116 124)
                      )
                    )
                  )
                )
                (.splitB
                  (.splitA
                    (.splitB
                      (.box 109 101)
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
                      (.box 111 125)
                    )
                    (.box 103 117)
                  )
                )
              )
            )
            (.splitB
              (.splitA
                (.splitB
                  (.box 89 77)
                  (.splitA
                    (.box 95 90)
                    (.box 85 89)
                  )
                )
                (.splitB
                  (.box 73 77)
                  (.box 77 89)
                )
              )
              (.splitA
                (.splitB
                  (.splitA
                    (.box 95 104)
                    (.box 85 105)
                  )
                  (.box 93 121)
                )
                (.box 73 106)
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
                (.box 184 80)
                (.box 145 81)
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
          (.box 129 81)
        )
        (.box 97 129)
      )
    )
  )

theorem g2Upper0Chart2_ok : checkChart g2Upper0 2 0 1 g2Upper0Chart2 = true := by decide +kernel

end HlawkaSchatten.BelowExponent.FacetNumeric
