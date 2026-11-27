/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.FacetNumeric

/-! Archived facet prism certificate data: `F2Prism83Data`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true

@[expose] public section

namespace HlawkaSchatten.BelowExponent.FacetNumeric

def f2Archived83 : Prism := {
  vertices := [⟨51200, 6400, 6400, 0⟩,
    ⟨46000, 12400, 5600, 0⟩,
    ⟨47600, 11600, 4800, 0⟩,
    ⟨51072, 6384, 6384, 160⟩,
    ⟨45885, 12369, 5586, 160⟩,
    ⟨47481, 11571, 4788, 160⟩]
  profileDen := 64000
  pi := [64419276, 180502030, 293997458, 534823060]
  slope := [406366391, -241612341, -168849759]
  radiusNum := 1
  radiusDen := 8
}

set_option maxRecDepth 40000
set_option maxHeartbeats 0

theorem f2Archived83_data_ok : dataOK f2Archived83 = true := by decide +kernel

def f2Archived83Chart0 : RowTree :=
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
                              (.box 128 123)
                            )
                            (.box 126 124)
                          )
                        )
                        (.splitB
                          (.splitB
                            (.box 124 128)
                            (.box 124 126)
                          )
                          (.splitA
                            (.box 124 123)
                            (.box 123 123)
                          )
                        )
                      )
                      (.splitA
                        (.splitB
                          (.box 127 120)
                          (.box 127 116)
                        )
                        (.splitB
                          (.box 124 120)
                          (.box 124 116)
                        )
                      )
                    )
                    (.splitB
                      (.splitB
                        (.box 119 127)
                        (.splitA
                          (.box 119 123)
                          (.box 118 123)
                        )
                      )
                      (.splitB
                        (.box 118 120)
                        (.box 119 116)
                      )
                    )
                  )
                  (.splitA
                    (.splitB
                      (.box 125 111)
                      (.box 125 104)
                    )
                    (.splitB
                      (.box 119 111)
                      (.box 117 104)
                    )
                  )
                )
                (.splitB
                  (.splitB
                    (.box 108 125)
                    (.box 108 117)
                  )
                  (.splitB
                    (.box 108 109)
                    (.box 108 103)
                  )
                )
              )
              (.splitA
                (.splitB
                  (.box 121 92)
                  (.box 121 79)
                )
                (.splitB
                  (.box 108 92)
                  (.box 105 79)
                )
              )
            )
            (.splitB
              (.splitB
                (.box 87 120)
                (.splitA
                  (.box 95 105)
                  (.box 79 105)
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
          (.splitB
            (.splitA
              (.box 113 177)
              (.splitB
                (.box 81 177)
                (.box 81 145)
              )
            )
            (.splitA
              (.box 113 193)
              (.splitB
                (.box 81 225)
                (.box 81 289)
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
            (.box 225 81)
          )
          (.splitB
            (.splitA
              (.splitA
                (.box 177 146)
                (.splitA
                  (.box 153 145)
                  (.box 137 145)
                )
              )
              (.splitA
                (.box 241 145)
                (.box 257 145)
              )
            )
            (.splitA
              (.splitA
                (.splitB
                  (.box 169 209)
                  (.box 161 289)
                )
                (.splitB
                  (.splitA
                    (.splitB
                      (.box 153 241)
                      (.box 149 201)
                    )
                    (.splitB
                      (.box 137 225)
                      (.splitA
                        (.splitB
                          (.box 141 217)
                          (.box 139 197)
                        )
                        (.splitB
                          (.box 133 217)
                          (.splitA
                            (.splitB
                              (.box 135 205)
                              (.box 135 195)
                            )
                            (.splitB
                              (.box 131 205)
                              (.box 131 195)
                            )
                          )
                        )
                      )
                    )
                  )
                  (.splitA
                    (.splitB
                      (.box 145 305)
                      (.box 153 321)
                    )
                    (.splitB
                      (.splitA
                        (.splitB
                          (.box 139 313)
                          (.box 141 273)
                        )
                        (.splitB
                          (.splitA
                            (.splitB
                              (.box 134 313)
                              (.box 135 297)
                            )
                            (.splitB
                              (.splitA
                                (.box 132 317)
                                (.box 130 317)
                              )
                              (.box 131 297)
                            )
                          )
                          (.box 133 289)
                        )
                      )
                      (.box 137 257)
                    )
                  )
                )
              )
              (.splitB
                (.splitA
                  (.splitA
                    (.splitB
                      (.box 241 225)
                      (.splitA
                        (.splitB
                          (.box 249 217)
                          (.splitA
                            (.box 255 197)
                            (.box 245 197)
                          )
                        )
                        (.box 233 201)
                      )
                    )
                    (.box 225 209)
                  )
                  (.box 193 225)
                )
                (.splitA
                  (.splitA
                    (.splitB
                      (.splitA
                        (.splitB
                          (.splitA
                            (.splitB
                              (.box 255 313)
                              (.box 253 297)
                            )
                            (.box 245 313)
                          )
                          (.box 249 289)
                        )
                        (.box 241 305)
                      )
                      (.box 241 257)
                    )
                    (.splitB
                      (.box 209 305)
                      (.box 209 321)
                    )
                  )
                  (.box 193 257)
                )
              )
            )
          )
        )
      )
      (.splitA
        (.splitB
          (.splitA
            (.box 113 193)
            (.box 73 193)
          )
          (.box 97 65)
        )
        (.splitB
          (.splitA
            (.splitB
              (.splitA
                (.box 177 0)
                (.box 145 0)
              )
              (.box 161 161)
            )
            (.splitB
              (.splitA
                (.box 225 0)
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
      (.splitB
        (.splitA
          (.box 193 97)
          (.box 65 75)
        )
        (.splitA
          (.splitB
            (.box 193 161)
            (.box 193 193)
          )
          (.box 65 0)
        )
      )
      (.splitB
        (.splitA
          (.box 193 193)
          (.box 65 0)
        )
        (.box 129 97)
      )
    )
  )

theorem f2Archived83Chart0_ok : checkChart f2Archived83 0 1 2 f2Archived83Chart0 = true := by decide +kernel

def f2Archived83Chart1 : RowTree :=
  (.splitA
    (.splitB
      (.splitA
        (.splitB
          (.box 97 65)
          (.splitA
            (.box 113 193)
            (.box 81 193)
          )
        )
        (.splitB
          (.box 129 97)
          (.splitA
            (.box 161 193)
            (.box 193 193)
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
              (.box 81 193)
              (.splitA
                (.box 89 161)
                (.box 73 161)
              )
            )
          )
          (.splitA
            (.splitB
              (.splitA
                (.splitB
                  (.box 121 79)
                  (.splitA
                    (.box 125 92)
                    (.box 117 92)
                  )
                )
                (.splitB
                  (.box 105 79)
                  (.splitA
                    (.box 111 92)
                    (.box 103 92)
                  )
                )
              )
              (.splitA
                (.splitB
                  (.splitA
                    (.splitB
                      (.box 125 104)
                      (.splitA
                        (.box 127 111)
                        (.box 123 111)
                      )
                    )
                    (.splitB
                      (.box 117 104)
                      (.splitA
                        (.box 120 111)
                        (.box 116 111)
                      )
                    )
                  )
                  (.splitA
                    (.splitB
                      (.splitA
                        (.splitB
                          (.box 127 116)
                          (.box 127 120)
                        )
                        (.splitB
                          (.box 123 116)
                          (.box 123 120)
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
                              (.splitA
                                (.box 1 128)
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
                            (.box 124 123)
                            (.box 123 123)
                          )
                          (.splitA
                            (.box 124 127)
                            (.box 123 127)
                          )
                        )
                      )
                    )
                    (.splitB
                      (.splitA
                        (.splitB
                          (.box 120 116)
                          (.box 120 120)
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
                      (.box 111 103)
                      (.box 111 111)
                    )
                    (.box 104 105)
                  )
                  (.splitA
                    (.splitB
                      (.box 111 117)
                      (.box 112 123)
                    )
                    (.box 104 121)
                  )
                )
              )
            )
            (.splitB
              (.splitA
                (.splitB
                  (.box 92 76)
                  (.box 92 92)
                )
                (.box 79 81)
              )
              (.splitA
                (.splitB
                  (.box 92 105)
                  (.box 95 118)
                )
                (.box 79 113)
              )
            )
          )
        )
        (.splitB
          (.splitA
            (.splitB
              (.box 161 193)
              (.box 161 161)
            )
            (.box 225 129)
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
        (.box 193 129)
        (.box 97 65)
      )
      (.splitA
        (.splitB
          (.box 193 129)
          (.box 0 84)
        )
        (.box 97 65)
      )
    )
  )

theorem f2Archived83Chart1_ok : checkChart f2Archived83 1 0 2 f2Archived83Chart1 = true := by decide +kernel

def f2Archived83Chart2 : RowTree :=
  (.splitA
    (.splitB
      (.splitA
        (.splitB
          (.box 84 65)
          (.box 81 193)
        )
        (.splitB
          (.box 129 97)
          (.splitA
            (.box 145 193)
            (.splitB
              (.box 193 161)
              (.box 193 257)
            )
          )
        )
      )
      (.splitA
        (.splitB
          (.splitB
            (.splitA
              (.box 113 193)
              (.box 81 225)
            )
            (.splitA
              (.box 112 178)
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
                  (.box 118 79)
                  (.box 118 95)
                )
                (.splitB
                  (.box 105 79)
                  (.splitA
                    (.box 109 92)
                    (.box 101 92)
                  )
                )
              )
              (.splitA
                (.splitB
                  (.splitA
                    (.splitB
                      (.box 123 104)
                      (.box 124 111)
                    )
                    (.splitB
                      (.box 117 104)
                      (.splitA
                        (.box 119 111)
                        (.box 115 111)
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
                              (.splitA
                                (.splitB
                                  (.box 128 126)
                                  (.box 128 127)
                                )
                                (.splitB
                                  (.box 128 126)
                                  (.box 128 127)
                                )
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
                      (.splitB
                        (.box 109 108)
                        (.box 110 110)
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
                        (.box 111 115)
                        (.box 111 118)
                      )
                      (.box 111 123)
                    )
                    (.splitB
                      (.box 104 115)
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
                  (.splitB
                    (.box 89 88)
                    (.box 92 91)
                  )
                )
                (.splitB
                  (.box 76 73)
                  (.box 79 86)
                )
              )
              (.splitA
                (.splitB
                  (.splitB
                    (.box 92 101)
                    (.box 92 107)
                  )
                  (.box 92 118)
                )
                (.box 81 107)
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
              (.splitB
                (.box 161 153)
                (.splitA
                  (.box 177 177)
                  (.box 145 177)
                )
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
            (.splitB
              (.box 193 161)
              (.box 193 257)
            )
            (.box 161 129)
          )
        )
        (.box 75 65)
      )
      (.splitB
        (.splitA
          (.splitA
            (.splitB
              (.box 193 257)
              (.box 193 161)
            )
            (.box 161 129)
          )
          (.box 75 0)
        )
        (.box 129 81)
      )
    )
  )

theorem f2Archived83Chart2_ok : checkChart f2Archived83 2 0 1 f2Archived83Chart2 = true := by decide +kernel

end HlawkaSchatten.BelowExponent.FacetNumeric
