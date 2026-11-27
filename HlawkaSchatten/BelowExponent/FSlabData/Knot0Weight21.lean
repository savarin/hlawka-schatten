/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.FSlabCheck

/-! Exact data for the weighted F-slab facet checks: `Knot0Weight21`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.FSlabCheck

set_option maxRecDepth 40000
set_option maxHeartbeats 0

def k0w21Low : Band := ⟨0, 21, false⟩

def k0w21LowChart0 : FacetNumeric.RowTree :=
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
                                  (.box 10001 0)
                                  (.splitA
                                    (.splitB
                                      (.box 10001 0)
                                      (.splitA
                                        (.splitB
                                          (.box 10001 0)
                                          (.box 10000 0)
                                        )
                                        (.splitB
                                          (.box 10001 0)
                                          (.box 10000 0)
                                        )
                                      )
                                    )
                                    (.splitB
                                      (.box 10001 0)
                                      (.box 10000 0)
                                    )
                                  )
                                )
                                (.splitB
                                  (.splitA
                                    (.box 10001 0)
                                    (.box 10000 0)
                                  )
                                  (.splitA
                                    (.box 10000 0)
                                    (.box 127 128)
                                  )
                                )
                              )
                              (.splitA
                                (.splitB
                                  (.splitA
                                    (.splitB
                                      (.splitA
                                        (.splitB
                                          (.box 10000 0)
                                          (.box 10000 0)
                                        )
                                        (.box 10000 0)
                                      )
                                      (.splitA
                                        (.box 10000 0)
                                        (.box 10000 0)
                                      )
                                    )
                                    (.splitB
                                      (.box 10000 0)
                                      (.box 10000 0)
                                    )
                                  )
                                  (.splitA
                                    (.splitB
                                      (.splitA
                                        (.box 10000 0)
                                        (.box 10000 0)
                                      )
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
                                    (.box 127 127)
                                  )
                                  (.box 10000 0)
                                )
                              )
                            )
                            (.splitB
                              (.box 127 128)
                              (.box 127 126)
                            )
                          )
                          (.splitA
                            (.splitB
                              (.splitA
                                (.splitB
                                  (.splitA
                                    (.splitB
                                      (.box 10000 0)
                                      (.box 10000 0)
                                    )
                                    (.box 10000 0)
                                  )
                                  (.splitA
                                    (.box 10000 0)
                                    (.box 10000 0)
                                  )
                                )
                                (.splitB
                                  (.box 128 125)
                                  (.box 128 124)
                                )
                              )
                              (.splitA
                                (.splitB
                                  (.splitA
                                    (.box 10000 0)
                                    (.box 10000 0)
                                  )
                                  (.box 10000 0)
                                )
                                (.box 128 122)
                              )
                            )
                            (.splitB
                              (.box 127 124)
                              (.box 126 122)
                            )
                          )
                        )
                        (.splitB
                          (.box 125 127)
                          (.box 125 123)
                        )
                      )
                      (.splitA
                        (.splitB
                          (.splitA
                            (.splitB
                              (.splitA
                                (.splitB
                                  (.splitA
                                    (.splitB
                                      (.box 1 121)
                                      (.box 1 120)
                                    )
                                    (.splitB
                                      (.box 128 121)
                                      (.box 128 120)
                                    )
                                  )
                                  (.splitA
                                    (.box 1 120)
                                    (.box 128 120)
                                  )
                                )
                                (.box 128 120)
                              )
                              (.splitA
                                (.splitB
                                  (.splitA
                                    (.box 1 119)
                                    (.box 128 119)
                                  )
                                  (.splitA
                                    (.box 1 118)
                                    (.box 128 118)
                                  )
                                )
                                (.box 128 118)
                              )
                            )
                            (.splitB
                              (.box 126 120)
                              (.box 126 118)
                            )
                          )
                          (.splitA
                            (.splitB
                              (.splitA
                                (.splitB
                                  (.box 1 117)
                                  (.box 1 116)
                                )
                                (.box 128 116)
                              )
                              (.box 128 114)
                            )
                            (.box 127 115)
                          )
                        )
                        (.splitB
                          (.box 125 119)
                          (.box 123 115)
                        )
                      )
                    )
                    (.splitB
                      (.box 121 125)
                      (.box 121 117)
                    )
                  )
                  (.splitA
                    (.splitB
                      (.splitA
                        (.splitB
                          (.splitA
                            (.splitB
                              (.box 128 112)
                              (.box 128 110)
                            )
                            (.box 126 111)
                          )
                          (.splitA
                            (.box 128 107)
                            (.box 126 107)
                          )
                        )
                        (.splitB
                          (.box 123 111)
                          (.box 123 107)
                        )
                      )
                      (.splitA
                        (.splitB
                          (.splitA
                            (.box 128 103)
                            (.box 126 103)
                          )
                          (.box 127 99)
                        )
                        (.box 125 101)
                      )
                    )
                    (.splitB
                      (.box 121 109)
                      (.box 117 101)
                    )
                  )
                )
                (.splitB
                  (.box 113 121)
                  (.box 113 105)
                )
              )
              (.splitA
                (.splitB
                  (.splitA
                    (.splitB
                      (.splitA
                        (.splitB
                          (.box 127 95)
                          (.box 127 91)
                        )
                        (.box 123 93)
                      )
                      (.splitA
                        (.box 127 85)
                        (.box 123 85)
                      )
                    )
                    (.splitB
                      (.box 117 93)
                      (.box 117 85)
                    )
                  )
                  (.splitA
                    (.splitB
                      (.box 126 77)
                      (.box 125 69)
                    )
                    (.box 119 74)
                  )
                )
                (.splitB
                  (.box 113 89)
                  (.box 113 73)
                )
              )
            )
            (.splitB
              (.box 97 113)
              (.box 97 81)
            )
          )
          (.splitA
            (.splitB
              (.splitA
                (.splitB
                  (.splitA
                    (.splitB
                      (.box 125 185)
                      (.box 125 169)
                    )
                    (.box 117 178)
                  )
                  (.splitA
                    (.box 125 145)
                    (.box 117 145)
                  )
                )
                (.splitB
                  (.box 105 177)
                  (.box 105 145)
                )
              )
              (.splitA
                (.splitB
                  (.box 122 226)
                  (.splitA
                    (.box 125 257)
                    (.box 117 257)
                  )
                )
                (.splitB
                  (.box 105 225)
                  (.splitA
                    (.splitB
                      (.box 109 289)
                      (.box 109 321)
                    )
                    (.box 103 321)
                  )
                )
              )
            )
            (.splitB
              (.box 89 161)
              (.splitA
                (.splitB
                  (.box 89 225)
                  (.splitA
                    (.box 93 321)
                    (.box 85 321)
                  )
                )
                (.splitB
                  (.box 73 225)
                  (.box 73 321)
                )
              )
            )
          )
        )
        (.splitB
          (.box 65 97)
          (.splitA
            (.splitB
              (.box 161 161)
              (.box 65 257)
            )
            (.box 193 193)
          )
        )
      )
      (.splitA
        (.splitB
          (.splitA
            (.splitB
              (.splitA
                (.splitB
                  (.box 121 321)
                  (.box 121 225)
                )
                (.splitB
                  (.box 102 321)
                  (.box 105 225)
                )
              )
              (.box 113 161)
            )
            (.splitB
              (.splitA
                (.splitB
                  (.splitA
                    (.box 93 321)
                    (.box 85 321)
                  )
                  (.box 89 225)
                )
                (.splitB
                  (.box 73 321)
                  (.box 73 225)
                )
              )
              (.box 81 161)
            )
          )
          (.splitA
            (.splitB
              (.box 113 81)
              (.box 113 113)
            )
            (.box 81 97)
          )
        )
        (.splitB
          (.splitA
            (.splitB
              (.box 65 257)
              (.box 161 161)
            )
            (.box 193 193)
          )
          (.box 65 97)
        )
      )
    )
    (.splitB
      (.box 0 65)
      (.box 0 65)
    )
  )

theorem k0w21LowChart0_ok : checkChart k0w21Low 0 k0w21LowChart0 = true := by decide +kernel

def k0w21LowChart1 : FacetNumeric.RowTree :=
  (.splitA
    (.splitB
      (.splitA
        (.splitB
          (.splitA
            (.splitB
              (.box 113 113)
              (.box 113 81)
            )
            (.box 81 96)
          )
          (.splitA
            (.splitB
              (.box 113 161)
              (.splitA
                (.splitB
                  (.box 121 225)
                  (.box 121 321)
                )
                (.splitB
                  (.box 105 225)
                  (.splitA
                    (.box 109 321)
                    (.box 101 321)
                  )
                )
              )
            )
            (.splitB
              (.box 81 161)
              (.splitA
                (.splitB
                  (.box 89 225)
                  (.splitA
                    (.box 93 321)
                    (.box 85 321)
                  )
                )
                (.splitB
                  (.box 73 225)
                  (.box 77 321)
                )
              )
            )
          )
        )
        (.splitB
          (.box 65 97)
          (.splitA
            (.splitB
              (.box 161 161)
              (.box 65 257)
            )
            (.box 193 193)
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
                    (.box 125 257)
                    (.box 117 257)
                  )
                  (.box 122 226)
                )
                (.splitB
                  (.splitA
                    (.splitB
                      (.box 109 321)
                      (.box 109 289)
                    )
                    (.splitB
                      (.box 101 321)
                      (.box 101 289)
                    )
                  )
                  (.box 105 225)
                )
              )
              (.splitA
                (.splitB
                  (.splitA
                    (.box 125 145)
                    (.box 117 145)
                  )
                  (.splitA
                    (.splitB
                      (.box 125 169)
                      (.box 125 185)
                    )
                    (.box 121 178)
                  )
                )
                (.splitB
                  (.box 105 145)
                  (.box 113 177)
                )
              )
            )
            (.splitB
              (.splitA
                (.splitB
                  (.splitA
                    (.box 93 321)
                    (.box 85 321)
                  )
                  (.box 89 225)
                )
                (.splitB
                  (.box 77 321)
                  (.box 73 225)
                )
              )
              (.box 89 161)
            )
          )
          (.splitA
            (.splitB
              (.splitA
                (.splitB
                  (.splitA
                    (.splitB
                      (.box 125 69)
                      (.box 126 77)
                    )
                    (.splitB
                      (.box 117 69)
                      (.box 117 77)
                    )
                  )
                  (.splitA
                    (.splitB
                      (.splitA
                        (.box 127 85)
                        (.box 123 85)
                      )
                      (.splitA
                        (.splitB
                          (.box 127 91)
                          (.box 127 95)
                        )
                        (.box 125 93)
                      )
                    )
                    (.splitB
                      (.box 117 85)
                      (.box 117 93)
                    )
                  )
                )
                (.splitB
                  (.box 113 73)
                  (.box 113 89)
                )
              )
              (.splitA
                (.splitB
                  (.splitA
                    (.splitB
                      (.splitA
                        (.splitB
                          (.box 127 99)
                          (.splitA
                            (.box 128 103)
                            (.box 126 103)
                          )
                        )
                        (.splitB
                          (.box 123 99)
                          (.box 123 103)
                        )
                      )
                      (.splitA
                        (.splitB
                          (.splitA
                            (.box 128 107)
                            (.box 126 107)
                          )
                          (.splitA
                            (.splitB
                              (.box 128 110)
                              (.box 128 112)
                            )
                            (.box 127 111)
                          )
                        )
                        (.splitB
                          (.box 123 107)
                          (.box 123 111)
                        )
                      )
                    )
                    (.splitB
                      (.box 121 101)
                      (.box 121 109)
                    )
                  )
                  (.splitA
                    (.splitB
                      (.splitA
                        (.splitB
                          (.splitA
                            (.splitB
                              (.box 128 114)
                              (.splitA
                                (.splitB
                                  (.box 1 116)
                                  (.box 1 117)
                                )
                                (.box 128 116)
                              )
                            )
                            (.splitB
                              (.box 126 114)
                              (.box 126 116)
                            )
                          )
                          (.splitA
                            (.splitB
                              (.splitA
                                (.splitB
                                  (.splitA
                                    (.box 1 118)
                                    (.box 128 118)
                                  )
                                  (.splitA
                                    (.box 1 119)
                                    (.box 128 119)
                                  )
                                )
                                (.box 128 118)
                              )
                              (.splitA
                                (.splitB
                                  (.splitA
                                    (.box 1 120)
                                    (.box 128 120)
                                  )
                                  (.splitA
                                    (.splitB
                                      (.box 1 120)
                                      (.box 1 121)
                                    )
                                    (.splitB
                                      (.box 128 120)
                                      (.box 128 121)
                                    )
                                  )
                                )
                                (.box 128 120)
                              )
                            )
                            (.splitB
                              (.box 126 118)
                              (.box 126 120)
                            )
                          )
                        )
                        (.splitB
                          (.box 125 115)
                          (.box 125 119)
                        )
                      )
                      (.splitA
                        (.splitB
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
                                  (.box 128 122)
                                  (.box 128 123)
                                )
                              )
                              (.splitA
                                (.splitB
                                  (.splitA
                                    (.box 10000 0)
                                    (.box 10000 0)
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
                                  (.box 10000 0)
                                  (.box 10000 0)
                                )
                              )
                            )
                            (.splitB
                              (.box 127 122)
                              (.box 127 124)
                            )
                          )
                          (.splitA
                            (.splitB
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
                                      (.box 10000 0)
                                    )
                                  )
                                  (.splitA
                                    (.splitB
                                      (.splitA
                                        (.box 10000 0)
                                        (.box 10000 0)
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
                                      (.box 10000 0)
                                      (.box 10000 0)
                                    )
                                  )
                                )
                                (.splitB
                                  (.splitA
                                    (.box 10000 0)
                                    (.box 127 126)
                                  )
                                  (.splitA
                                    (.box 10000 0)
                                    (.box 127 127)
                                  )
                                )
                              )
                              (.splitA
                                (.splitB
                                  (.splitA
                                    (.splitB
                                      (.splitA
                                        (.splitB
                                          (.box 10000 0)
                                          (.box 10001 0)
                                        )
                                        (.splitB
                                          (.box 10000 0)
                                          (.box 10001 0)
                                        )
                                      )
                                      (.box 10001 0)
                                    )
                                    (.splitB
                                      (.splitA
                                        (.box 10000 0)
                                        (.box 10000 0)
                                      )
                                      (.box 10001 0)
                                    )
                                  )
                                  (.box 10001 0)
                                )
                                (.splitB
                                  (.splitA
                                    (.box 10000 0)
                                    (.box 10000 0)
                                  )
                                  (.splitA
                                    (.box 10001 0)
                                    (.box 127 128)
                                  )
                                )
                              )
                            )
                            (.splitB
                              (.box 127 126)
                              (.box 127 128)
                            )
                          )
                        )
                        (.splitB
                          (.box 125 123)
                          (.box 125 127)
                        )
                      )
                    )
                    (.splitB
                      (.box 121 117)
                      (.box 121 125)
                    )
                  )
                )
                (.splitB
                  (.box 113 105)
                  (.box 113 121)
                )
              )
            )
            (.splitB
              (.box 97 81)
              (.box 97 113)
            )
          )
        )
        (.splitB
          (.splitA
            (.splitB
              (.box 65 257)
              (.box 161 161)
            )
            (.box 193 193)
          )
          (.box 65 97)
        )
      )
    )
    (.splitB
      (.box 0 65)
      (.box 0 65)
    )
  )

theorem k0w21LowChart1_ok : checkChart k0w21Low 1 k0w21LowChart1 = true := by decide +kernel

def k0w21LowChart2 : FacetNumeric.RowTree :=
  (.splitA
    (.splitB
      (.splitA
        (.box 65 129)
        (.splitB
          (.box 129 65)
          (.splitA
            (.box 129 193)
            (.splitB
              (.box 193 161)
              (.splitA
                (.box 225 257)
                (.splitB
                  (.box 257 225)
                  (.splitA
                    (.box 289 321)
                    (.splitB
                      (.box 321 289)
                      (.box 385 385)
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
                (.box 81 177)
                (.splitB
                  (.box 73 161)
                  (.splitA
                    (.box 77 185)
                    (.splitB
                      (.box 69 169)
                      (.box 69 186)
                    )
                  )
                )
              )
            )
          )
          (.splitA
            (.splitB
              (.splitA
                (.box 113 89)
                (.splitB
                  (.box 105 81)
                  (.splitA
                    (.box 109 94)
                    (.splitB
                      (.box 101 89)
                      (.splitA
                        (.box 103 95)
                        (.splitB
                          (.box 99 91)
                          (.box 99 95)
                        )
                      )
                    )
                  )
                )
              )
              (.splitA
                (.splitB
                  (.splitA
                    (.box 121 109)
                    (.splitB
                      (.box 117 105)
                      (.splitA
                        (.box 117 111)
                        (.splitB
                          (.box 115 109)
                          (.splitA
                            (.box 116 112)
                            (.splitB
                              (.box 114 110)
                              (.box 114 112)
                            )
                          )
                        )
                      )
                    )
                  )
                  (.splitA
                    (.splitB
                      (.splitA
                        (.box 125 119)
                        (.splitB
                          (.box 123 117)
                          (.splitA
                            (.box 123 120)
                            (.splitB
                              (.box 122 119)
                              (.splitA
                                (.splitB
                                  (.box 123 120)
                                  (.box 122 121)
                                )
                                (.splitB
                                  (.box 121 120)
                                  (.splitA
                                    (.splitB
                                      (.box 122 120)
                                      (.box 122 121)
                                    )
                                    (.splitB
                                      (.box 121 120)
                                      (.box 121 121)
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
                            (.box 127 124)
                            (.splitB
                              (.box 126 123)
                              (.splitA
                                (.splitB
                                  (.box 127 124)
                                  (.box 126 125)
                                )
                                (.splitB
                                  (.box 125 124)
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
                              )
                            )
                          )
                          (.splitA
                            (.splitB
                              (.splitA
                                (.splitB
                                  (.box 1 126)
                                  (.box 128 127)
                                )
                                (.splitB
                                  (.box 127 126)
                                  (.splitA
                                    (.splitB
                                      (.box 10000 0)
                                      (.splitA
                                        (.box 128 127)
                                        (.box 10000 0)
                                      )
                                    )
                                    (.splitB
                                      (.splitA
                                        (.box 10000 0)
                                        (.box 10000 0)
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
                                  )
                                )
                              )
                              (.splitA
                                (.splitB
                                  (.splitA
                                    (.splitB
                                      (.box 10000 0)
                                      (.box 10001 0)
                                    )
                                    (.splitB
                                      (.splitA
                                        (.box 10000 0)
                                        (.box 10000 0)
                                      )
                                      (.box 10001 0)
                                    )
                                  )
                                  (.box 10001 0)
                                )
                                (.splitB
                                  (.splitA
                                    (.splitB
                                      (.splitA
                                        (.splitB
                                          (.box 10000 0)
                                          (.box 10001 0)
                                        )
                                        (.splitB
                                          (.box 10000 0)
                                          (.box 10001 0)
                                        )
                                      )
                                      (.box 10001 0)
                                    )
                                    (.splitB
                                      (.splitA
                                        (.splitB
                                          (.splitA
                                            (.box 10000 0)
                                            (.box 10000 0)
                                          )
                                          (.box 10001 0)
                                        )
                                        (.splitB
                                          (.splitA
                                            (.box 10000 0)
                                            (.box 10000 0)
                                          )
                                          (.splitA
                                            (.box 10001 0)
                                            (.box 10000 0)
                                          )
                                        )
                                      )
                                      (.splitA
                                        (.box 10001 0)
                                        (.splitB
                                          (.box 10000 0)
                                          (.box 10000 0)
                                        )
                                      )
                                    )
                                  )
                                  (.splitA
                                    (.box 10001 0)
                                    (.splitB
                                      (.splitA
                                        (.box 10001 0)
                                        (.box 127 128)
                                      )
                                      (.box 10000 0)
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
                                      (.box 10000 0)
                                      (.box 10000 0)
                                    )
                                    (.splitB
                                      (.box 10000 0)
                                      (.splitA
                                        (.box 10000 0)
                                        (.splitB
                                          (.box 10000 0)
                                          (.box 126 126)
                                        )
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
                                        (.box 10000 0)
                                      )
                                    )
                                  )
                                )
                                (.splitB
                                  (.splitA
                                    (.splitB
                                      (.splitA
                                        (.box 10000 0)
                                        (.box 10000 0)
                                      )
                                      (.splitA
                                        (.splitB
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
                                          (.box 126 126)
                                          (.box 10000 0)
                                        )
                                        (.box 10000 0)
                                      )
                                      (.box 10000 0)
                                    )
                                    (.splitB
                                      (.box 10000 0)
                                      (.box 10000 0)
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
                                          (.box 10000 0)
                                          (.box 10000 0)
                                        )
                                        (.splitB
                                          (.box 10000 0)
                                          (.box 10000 0)
                                        )
                                      )
                                      (.splitA
                                        (.box 10000 0)
                                        (.box 10000 0)
                                      )
                                    )
                                    (.splitB
                                      (.box 10000 0)
                                      (.box 10000 0)
                                    )
                                  )
                                  (.box 127 128)
                                )
                                (.splitB
                                  (.box 126 127)
                                  (.box 126 1)
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
                                  (.box 123 122)
                                  (.splitA
                                    (.splitB
                                      (.box 124 122)
                                      (.box 124 123)
                                    )
                                    (.splitB
                                      (.box 123 122)
                                      (.box 123 123)
                                    )
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
                                    (.splitB
                                      (.box 10000 0)
                                      (.box 10000 0)
                                    )
                                  )
                                  (.splitA
                                    (.splitB
                                      (.box 124 124)
                                      (.box 124 125)
                                    )
                                    (.splitB
                                      (.box 123 124)
                                      (.box 123 125)
                                    )
                                  )
                                )
                              )
                            )
                            (.splitB
                              (.splitA
                                (.splitB
                                  (.splitA
                                    (.box 10000 0)
                                    (.box 10000 0)
                                  )
                                  (.splitA
                                    (.splitB
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
                                      (.box 123 123)
                                      (.box 123 124)
                                    )
                                    (.box 10000 0)
                                  )
                                  (.box 123 124)
                                )
                                (.splitB
                                  (.box 122 123)
                                  (.box 122 125)
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
                                      (.box 10000 0)
                                      (.box 10000 0)
                                    )
                                    (.splitB
                                      (.box 10000 0)
                                      (.box 10000 0)
                                    )
                                  )
                                  (.box 125 126)
                                )
                                (.splitB
                                  (.box 124 125)
                                  (.box 124 127)
                                )
                              )
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
                          (.splitA
                            (.box 120 116)
                            (.splitB
                              (.box 118 114)
                              (.splitA
                                (.box 118 116)
                                (.splitB
                                  (.box 118 116)
                                  (.box 117 117)
                                )
                              )
                            )
                          )
                          (.splitA
                            (.splitB
                              (.splitA
                                (.splitB
                                  (.box 121 118)
                                  (.box 121 119)
                                )
                                (.splitB
                                  (.box 120 118)
                                  (.box 119 119)
                                )
                              )
                              (.splitA
                                (.splitB
                                  (.splitA
                                    (.box 121 120)
                                    (.box 120 120)
                                  )
                                  (.splitA
                                    (.splitB
                                      (.box 121 120)
                                      (.box 121 121)
                                    )
                                    (.splitB
                                      (.box 120 120)
                                      (.box 120 121)
                                    )
                                  )
                                )
                                (.splitB
                                  (.splitA
                                    (.splitB
                                      (.box 120 119)
                                      (.box 120 120)
                                    )
                                    (.splitB
                                      (.box 119 119)
                                      (.box 119 120)
                                    )
                                  )
                                  (.splitA
                                    (.splitB
                                      (.box 120 120)
                                      (.box 120 121)
                                    )
                                    (.box 119 120)
                                  )
                                )
                              )
                            )
                            (.splitB
                              (.splitA
                                (.splitB
                                  (.box 118 118)
                                  (.splitA
                                    (.splitB
                                      (.box 119 118)
                                      (.box 119 119)
                                    )
                                    (.splitB
                                      (.box 118 118)
                                      (.box 118 119)
                                    )
                                  )
                                )
                                (.splitB
                                  (.splitA
                                    (.splitB
                                      (.box 118 117)
                                      (.box 118 118)
                                    )
                                    (.splitB
                                      (.box 117 117)
                                      (.box 117 118)
                                    )
                                  )
                                  (.box 118 118)
                                )
                              )
                              (.splitA
                                (.splitB
                                  (.box 119 119)
                                  (.box 119 121)
                                )
                                (.box 118 120)
                              )
                            )
                          )
                        )
                        (.splitB
                          (.splitA
                            (.splitB
                              (.splitA
                                (.box 116 114)
                                (.splitB
                                  (.box 116 114)
                                  (.box 115 115)
                                )
                              )
                              (.splitA
                                (.splitB
                                  (.box 116 116)
                                  (.splitA
                                    (.box 117 117)
                                    (.box 116 117)
                                  )
                                )
                                (.splitB
                                  (.splitA
                                    (.box 116 116)
                                    (.box 115 116)
                                  )
                                  (.box 116 116)
                                )
                              )
                            )
                            (.splitB
                              (.splitA
                                (.box 115 114)
                                (.box 114 114)
                              )
                              (.splitA
                                (.box 115 116)
                                (.box 114 116)
                              )
                            )
                          )
                          (.splitA
                            (.splitB
                              (.splitA
                                (.splitB
                                  (.box 117 117)
                                  (.box 117 119)
                                )
                                (.box 116 118)
                              )
                              (.box 116 120)
                            )
                            (.box 114 118)
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
                                    (.splitB
                                      (.box 121 121)
                                      (.box 121 122)
                                    )
                                    (.box 120 121)
                                  )
                                  (.box 121 122)
                                )
                                (.splitB
                                  (.box 120 121)
                                  (.box 120 123)
                                )
                              )
                              (.box 120 123)
                            )
                            (.box 118 122)
                          )
                          (.box 119 125)
                        )
                        (.box 117 123)
                      )
                    )
                  )
                )
                (.splitB
                  (.splitA
                    (.splitB
                      (.splitA
                        (.box 111 103)
                        (.splitB
                          (.box 107 99)
                          (.splitA
                            (.box 108 103)
                            (.box 106 104)
                          )
                        )
                      )
                      (.splitA
                        (.splitB
                          (.splitA
                            (.box 112 108)
                            (.splitB
                              (.box 110 106)
                              (.box 110 108)
                            )
                          )
                          (.splitA
                            (.splitB
                              (.box 112 110)
                              (.box 112 112)
                            )
                            (.splitB
                              (.box 110 110)
                              (.box 110 112)
                            )
                          )
                        )
                        (.splitB
                          (.splitA
                            (.splitB
                              (.box 108 106)
                              (.box 108 108)
                            )
                            (.splitB
                              (.box 106 106)
                              (.box 106 108)
                            )
                          )
                          (.splitA
                            (.splitB
                              (.box 108 110)
                              (.box 108 112)
                            )
                            (.box 106 111)
                          )
                        )
                      )
                    )
                    (.splitB
                      (.splitA
                        (.splitB
                          (.box 102 100)
                          (.splitA
                            (.splitB
                              (.box 104 102)
                              (.box 104 104)
                            )
                            (.box 102 103)
                          )
                        )
                        (.splitB
                          (.splitA
                            (.box 100 99)
                            (.box 98 99)
                          )
                          (.box 100 103)
                        )
                      )
                      (.splitA
                        (.splitB
                          (.box 104 106)
                          (.box 103 111)
                        )
                        (.box 99 107)
                      )
                    )
                  )
                  (.splitA
                    (.splitB
                      (.splitA
                        (.splitB
                          (.splitA
                            (.splitB
                              (.box 112 114)
                              (.box 112 116)
                            )
                            (.box 110 114)
                          )
                          (.box 111 117)
                        )
                        (.box 107 115)
                      )
                      (.box 109 121)
                    )
                    (.box 101 116)
                  )
                )
              )
            )
            (.splitB
              (.splitA
                (.splitB
                  (.splitA
                    (.box 93 77)
                    (.splitB
                      (.box 85 69)
                      (.splitA
                        (.box 87 79)
                        (.box 83 79)
                      )
                    )
                  )
                  (.splitA
                    (.splitB
                      (.splitA
                        (.box 95 87)
                        (.splitB
                          (.box 91 83)
                          (.box 91 87)
                        )
                      )
                      (.splitA
                        (.splitB
                          (.box 95 91)
                          (.box 95 95)
                        )
                        (.splitB
                          (.box 91 91)
                          (.box 91 95)
                        )
                      )
                    )
                    (.splitB
                      (.splitA
                        (.splitB
                          (.box 87 83)
                          (.box 87 87)
                        )
                        (.splitB
                          (.box 83 83)
                          (.box 83 87)
                        )
                      )
                      (.splitA
                        (.box 88 92)
                        (.box 83 93)
                      )
                    )
                  )
                )
                (.splitB
                  (.splitA
                    (.splitB
                      (.box 76 71)
                      (.splitA
                        (.splitB
                          (.box 79 75)
                          (.box 79 79)
                        )
                        (.box 75 77)
                      )
                    )
                    (.splitB
                      (.splitA
                        (.box 71 69)
                        (.box 67 69)
                      )
                      (.box 71 75)
                    )
                  )
                  (.splitA
                    (.splitB
                      (.box 79 84)
                      (.box 77 93)
                    )
                    (.box 69 85)
                  )
                )
              )
              (.splitA
                (.splitB
                  (.splitA
                    (.splitB
                      (.splitA
                        (.splitB
                          (.box 95 99)
                          (.box 95 103)
                        )
                        (.box 91 99)
                      )
                      (.box 93 105)
                    )
                    (.box 85 101)
                  )
                  (.box 89 113)
                )
                (.box 81 105)
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
                  (.box 145 193)
                  (.splitA
                    (.box 153 241)
                    (.box 132 240)
                  )
                )
              )
              (.splitA
                (.splitB
                  (.splitA
                    (.box 185 153)
                    (.splitB
                      (.box 169 137)
                      (.box 169 153)
                    )
                  )
                  (.splitA
                    (.splitB
                      (.box 185 169)
                      (.splitA
                        (.box 189 185)
                        (.box 181 185)
                      )
                    )
                    (.splitB
                      (.box 169 169)
                      (.box 169 185)
                    )
                  )
                )
                (.splitB
                  (.splitA
                    (.splitB
                      (.box 153 137)
                      (.box 153 153)
                    )
                    (.splitB
                      (.box 137 137)
                      (.box 137 153)
                    )
                  )
                  (.splitA
                    (.box 157 170)
                    (.box 137 169)
                  )
                )
              )
            )
            (.splitB
              (.splitA
                (.splitB
                  (.splitA
                    (.box 241 289)
                    (.splitB
                      (.box 209 321)
                      (.box 209 289)
                    )
                  )
                  (.splitA
                    (.splitB
                      (.box 241 209)
                      (.box 241 241)
                    )
                    (.splitB
                      (.box 209 209)
                      (.box 209 241)
                    )
                  )
                )
                (.splitB
                  (.splitA
                    (.splitB
                      (.box 289 321)
                      (.box 289 289)
                    )
                    (.splitB
                      (.splitA
                        (.box 353 321)
                        (.splitB
                          (.box 385 385)
                          (.box 385 353)
                        )
                      )
                      (.box 321 289)
                    )
                  )
                  (.box 289 210)
                )
              )
              (.splitA
                (.splitB
                  (.box 241 138)
                  (.box 225 177)
                )
                (.box 257 145)
              )
            )
          )
          (.splitA
            (.splitB
              (.splitA
                (.splitB
                  (.splitA
                    (.splitB
                      (.box 185 68)
                      (.box 185 77)
                    )
                    (.box 169 69)
                  )
                  (.box 177 81)
                )
                (.box 145 73)
              )
              (.box 161 97)
            )
            (.box 129 81)
          )
        )
      )
    )
    (.splitB
      (.splitA
        (.splitB
          (.splitA
            (.box 193 81)
            (.splitB
              (.box 161 113)
              (.box 161 74)
            )
          )
          (.splitA
            (.splitB
              (.splitA
                (.box 257 145)
                (.box 225 146)
              )
              (.splitA
                (.splitB
                  (.box 258 210)
                  (.splitA
                    (.splitB
                      (.box 321 289)
                      (.splitA
                        (.box 385 385)
                        (.box 353 321)
                      )
                    )
                    (.box 289 257)
                  )
                )
                (.splitB
                  (.splitA
                    (.box 209 225)
                    (.box 241 225)
                  )
                  (.box 209 257)
                )
              )
            )
            (.splitB
              (.splitA
                (.splitB
                  (.box 145 177)
                  (.box 145 145)
                )
                (.box 177 161)
              )
              (.splitA
                (.splitB
                  (.box 145 225)
                  (.box 145 257)
                )
                (.box 177 129)
              )
            )
          )
        )
        (.splitB
          (.splitA
            (.splitB
              (.box 81 113)
              (.splitA
                (.box 73 81)
                (.box 89 81)
              )
            )
            (.splitB
              (.box 113 113)
              (.box 113 81)
            )
          )
          (.splitA
            (.splitB
              (.box 73 161)
              (.box 81 193)
            )
            (.box 113 161)
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
                    (.splitB
                      (.box 385 385)
                      (.box 321 289)
                    )
                    (.box 289 257)
                  )
                  (.box 257 225)
                )
                (.box 225 0)
              )
              (.box 193 161)
            )
            (.box 161 193)
          )
          (.box 129 65)
        )
        (.box 97 129)
      )
    )
  )

theorem k0w21LowChart2_ok : checkChart k0w21Low 2 k0w21LowChart2 = true := by decide +kernel

def k0w21High : Band := ⟨0, 21, true⟩

def k0w21HighChart0 : FacetNumeric.RowTree :=
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
                                  (.box 10001 0)
                                  (.splitA
                                    (.splitB
                                      (.box 10001 0)
                                      (.splitA
                                        (.splitB
                                          (.box 10001 0)
                                          (.box 10000 0)
                                        )
                                        (.splitB
                                          (.box 10001 0)
                                          (.box 10000 0)
                                        )
                                      )
                                    )
                                    (.splitB
                                      (.box 10001 0)
                                      (.splitA
                                        (.box 10000 0)
                                        (.box 10000 0)
                                      )
                                    )
                                  )
                                )
                                (.splitB
                                  (.splitA
                                    (.box 10001 0)
                                    (.box 10000 0)
                                  )
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
                                      (.splitA
                                        (.splitB
                                          (.box 10000 0)
                                          (.box 10000 0)
                                        )
                                        (.box 10000 0)
                                      )
                                      (.splitA
                                        (.box 10000 0)
                                        (.box 10000 0)
                                      )
                                    )
                                    (.splitB
                                      (.box 10000 0)
                                      (.box 10000 0)
                                    )
                                  )
                                  (.splitA
                                    (.splitB
                                      (.splitA
                                        (.box 10000 0)
                                        (.box 10000 0)
                                      )
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
                                    (.box 127 126)
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
                                (.box 127 126)
                                (.box 126 126)
                              )
                            )
                          )
                          (.splitA
                            (.splitB
                              (.splitA
                                (.splitB
                                  (.splitA
                                    (.splitB
                                      (.box 10000 0)
                                      (.box 10000 0)
                                    )
                                    (.box 10000 0)
                                  )
                                  (.splitA
                                    (.box 10000 0)
                                    (.box 10000 0)
                                  )
                                )
                                (.splitB
                                  (.box 10000 0)
                                  (.box 10000 0)
                                )
                              )
                              (.splitA
                                (.splitB
                                  (.splitA
                                    (.box 10000 0)
                                    (.box 10000 0)
                                  )
                                  (.box 10000 0)
                                )
                                (.splitB
                                  (.box 128 123)
                                  (.box 128 122)
                                )
                              )
                            )
                            (.splitB
                              (.box 127 124)
                              (.box 127 122)
                            )
                          )
                        )
                        (.splitB
                          (.box 124 127)
                          (.box 124 123)
                        )
                      )
                      (.splitA
                        (.splitB
                          (.splitA
                            (.splitB
                              (.splitA
                                (.splitB
                                  (.splitA
                                    (.box 1 121)
                                    (.box 128 121)
                                  )
                                  (.splitA
                                    (.box 1 120)
                                    (.box 128 120)
                                  )
                                )
                                (.box 128 120)
                              )
                              (.splitA
                                (.splitB
                                  (.splitA
                                    (.box 1 119)
                                    (.box 128 119)
                                  )
                                  (.box 1 118)
                                )
                                (.box 128 118)
                              )
                            )
                            (.splitB
                              (.box 126 120)
                              (.box 126 118)
                            )
                          )
                          (.splitA
                            (.splitB
                              (.splitA
                                (.box 1 116)
                                (.box 128 116)
                              )
                              (.box 128 114)
                            )
                            (.splitB
                              (.box 126 116)
                              (.box 126 114)
                            )
                          )
                        )
                        (.splitB
                          (.box 125 119)
                          (.box 125 115)
                        )
                      )
                    )
                    (.splitB
                      (.box 119 125)
                      (.box 119 117)
                    )
                  )
                  (.splitA
                    (.splitB
                      (.splitA
                        (.splitB
                          (.splitA
                            (.splitB
                              (.box 128 112)
                              (.box 128 110)
                            )
                            (.box 126 111)
                          )
                          (.splitA
                            (.box 128 107)
                            (.box 126 107)
                          )
                        )
                        (.splitB
                          (.box 123 111)
                          (.box 123 107)
                        )
                      )
                      (.splitA
                        (.splitB
                          (.splitA
                            (.box 128 103)
                            (.box 126 103)
                          )
                          (.box 127 99)
                        )
                        (.box 124 101)
                      )
                    )
                    (.splitB
                      (.box 119 109)
                      (.box 121 101)
                    )
                  )
                )
                (.splitB
                  (.box 109 121)
                  (.box 109 105)
                )
              )
              (.splitA
                (.splitB
                  (.splitA
                    (.splitB
                      (.splitA
                        (.splitB
                          (.box 127 95)
                          (.box 127 91)
                        )
                        (.box 123 93)
                      )
                      (.splitA
                        (.box 127 85)
                        (.box 123 85)
                      )
                    )
                    (.splitB
                      (.box 117 93)
                      (.box 117 85)
                    )
                  )
                  (.splitA
                    (.splitB
                      (.box 126 77)
                      (.box 125 69)
                    )
                    (.box 119 74)
                  )
                )
                (.splitB
                  (.box 109 89)
                  (.box 109 73)
                )
              )
            )
            (.splitB
              (.box 89 113)
              (.box 89 81)
            )
          )
          (.splitA
            (.splitB
              (.splitA
                (.splitB
                  (.splitA
                    (.splitB
                      (.box 125 185)
                      (.box 125 169)
                    )
                    (.box 117 178)
                  )
                  (.splitA
                    (.box 125 145)
                    (.box 117 145)
                  )
                )
                (.splitB
                  (.box 105 178)
                  (.box 105 145)
                )
              )
              (.splitA
                (.splitB
                  (.box 122 226)
                  (.box 121 257)
                )
                (.splitB
                  (.box 105 225)
                  (.splitA
                    (.box 109 257)
                    (.splitB
                      (.box 101 289)
                      (.box 101 321)
                    )
                  )
                )
              )
            )
            (.splitB
              (.box 88 160)
              (.splitA
                (.splitB
                  (.box 89 225)
                  (.splitA
                    (.box 93 322)
                    (.box 85 321)
                  )
                )
                (.splitB
                  (.box 73 225)
                  (.box 73 321)
                )
              )
            )
          )
        )
        (.splitB
          (.box 161 97)
          (.splitA
            (.splitB
              (.box 161 161)
              (.box 177 257)
            )
            (.box 193 193)
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
                  (.box 105 321)
                  (.box 105 225)
                )
              )
              (.box 113 161)
            )
            (.splitB
              (.splitA
                (.splitB
                  (.box 89 321)
                  (.box 89 225)
                )
                (.box 77 257)
              )
              (.box 81 161)
            )
          )
          (.splitA
            (.splitB
              (.box 113 81)
              (.box 113 113)
            )
            (.box 81 97)
          )
        )
        (.splitB
          (.splitA
            (.splitB
              (.box 65 257)
              (.box 161 161)
            )
            (.box 193 193)
          )
          (.box 65 97)
        )
      )
    )
    (.splitB
      (.splitA
        (.box 0 65)
        (.box 97 65)
      )
      (.splitA
        (.box 0 65)
        (.box 97 65)
      )
    )
  )

theorem k0w21HighChart0_ok : checkChart k0w21High 0 k0w21HighChart0 = true := by decide +kernel

def k0w21HighChart1 : FacetNumeric.RowTree :=
  (.splitA
    (.splitB
      (.splitA
        (.splitB
          (.splitA
            (.splitB
              (.box 113 113)
              (.box 113 81)
            )
            (.box 89 97)
          )
          (.splitA
            (.splitB
              (.box 113 161)
              (.splitA
                (.splitB
                  (.box 121 225)
                  (.box 121 321)
                )
                (.splitB
                  (.box 105 225)
                  (.box 102 321)
                )
              )
            )
            (.splitB
              (.box 81 161)
              (.splitA
                (.splitB
                  (.box 89 225)
                  (.splitA
                    (.box 93 321)
                    (.box 85 321)
                  )
                )
                (.splitB
                  (.box 73 225)
                  (.box 77 321)
                )
              )
            )
          )
        )
        (.splitB
          (.box 161 97)
          (.splitA
            (.splitB
              (.box 161 161)
              (.box 177 257)
            )
            (.box 193 193)
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
                    (.box 125 257)
                    (.box 117 257)
                  )
                  (.splitA
                    (.box 125 225)
                    (.box 117 225)
                  )
                )
                (.splitB
                  (.splitA
                    (.splitB
                      (.box 109 321)
                      (.box 109 289)
                    )
                    (.splitB
                      (.box 101 321)
                      (.box 101 289)
                    )
                  )
                  (.box 109 225)
                )
              )
              (.splitA
                (.splitB
                  (.splitA
                    (.box 125 145)
                    (.box 117 145)
                  )
                  (.splitA
                    (.splitB
                      (.box 125 169)
                      (.box 125 185)
                    )
                    (.box 119 178)
                  )
                )
                (.splitB
                  (.box 109 145)
                  (.box 109 177)
                )
              )
            )
            (.splitB
              (.splitA
                (.splitB
                  (.splitA
                    (.box 93 321)
                    (.box 85 321)
                  )
                  (.box 89 225)
                )
                (.splitB
                  (.box 77 321)
                  (.box 73 225)
                )
              )
              (.box 90 161)
            )
          )
          (.splitA
            (.splitB
              (.splitA
                (.splitB
                  (.splitA
                    (.splitB
                      (.box 125 69)
                      (.splitA
                        (.box 127 77)
                        (.box 123 77)
                      )
                    )
                    (.splitB
                      (.box 117 69)
                      (.box 117 77)
                    )
                  )
                  (.splitA
                    (.splitB
                      (.splitA
                        (.box 127 85)
                        (.box 123 85)
                      )
                      (.splitA
                        (.splitB
                          (.box 127 91)
                          (.box 127 95)
                        )
                        (.box 124 93)
                      )
                    )
                    (.splitB
                      (.box 119 85)
                      (.box 119 93)
                    )
                  )
                )
                (.splitB
                  (.box 109 73)
                  (.box 109 89)
                )
              )
              (.splitA
                (.splitB
                  (.splitA
                    (.splitB
                      (.splitA
                        (.splitB
                          (.box 127 99)
                          (.splitA
                            (.box 128 103)
                            (.box 126 103)
                          )
                        )
                        (.splitB
                          (.box 123 99)
                          (.box 123 103)
                        )
                      )
                      (.splitA
                        (.splitB
                          (.splitA
                            (.box 128 107)
                            (.box 126 107)
                          )
                          (.splitA
                            (.splitB
                              (.box 128 110)
                              (.box 128 112)
                            )
                            (.splitB
                              (.box 126 110)
                              (.box 126 112)
                            )
                          )
                        )
                        (.splitB
                          (.box 124 107)
                          (.box 124 111)
                        )
                      )
                    )
                    (.splitB
                      (.box 119 101)
                      (.box 119 109)
                    )
                  )
                  (.splitA
                    (.splitB
                      (.splitA
                        (.splitB
                          (.splitA
                            (.splitB
                              (.box 128 114)
                              (.splitA
                                (.splitB
                                  (.box 1 116)
                                  (.splitA
                                    (.box 1 117)
                                    (.box 128 117)
                                  )
                                )
                                (.box 128 116)
                              )
                            )
                            (.splitB
                              (.box 126 114)
                              (.box 126 116)
                            )
                          )
                          (.splitA
                            (.splitB
                              (.splitA
                                (.splitB
                                  (.splitA
                                    (.box 1 118)
                                    (.box 128 118)
                                  )
                                  (.splitA
                                    (.box 1 119)
                                    (.box 128 119)
                                  )
                                )
                                (.splitB
                                  (.box 128 118)
                                  (.box 128 119)
                                )
                              )
                              (.splitA
                                (.splitB
                                  (.splitA
                                    (.box 1 120)
                                    (.box 128 120)
                                  )
                                  (.splitA
                                    (.splitB
                                      (.box 1 120)
                                      (.box 1 121)
                                    )
                                    (.splitB
                                      (.box 128 120)
                                      (.box 128 121)
                                    )
                                  )
                                )
                                (.splitB
                                  (.splitA
                                    (.box 128 120)
                                    (.box 127 120)
                                  )
                                  (.splitA
                                    (.box 128 121)
                                    (.box 127 121)
                                  )
                                )
                              )
                            )
                            (.splitB
                              (.splitA
                                (.box 127 118)
                                (.box 126 118)
                              )
                              (.splitA
                                (.box 127 120)
                                (.box 126 120)
                              )
                            )
                          )
                        )
                        (.splitB
                          (.box 124 115)
                          (.box 124 119)
                        )
                      )
                      (.splitA
                        (.splitB
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
                                  (.box 10000 0)
                                )
                              )
                              (.splitA
                                (.splitB
                                  (.splitA
                                    (.box 10000 0)
                                    (.box 10000 0)
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
                              (.splitA
                                (.box 127 122)
                                (.box 126 122)
                              )
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
                                      (.box 10000 0)
                                    )
                                  )
                                  (.splitA
                                    (.splitB
                                      (.splitA
                                        (.box 10000 0)
                                        (.box 10000 0)
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
                              (.splitA
                                (.splitB
                                  (.splitA
                                    (.splitB
                                      (.splitA
                                        (.splitB
                                          (.box 10000 0)
                                          (.box 10001 0)
                                        )
                                        (.splitB
                                          (.box 10000 0)
                                          (.box 10001 0)
                                        )
                                      )
                                      (.box 10001 0)
                                    )
                                    (.splitB
                                      (.splitA
                                        (.box 10000 0)
                                        (.box 10000 0)
                                      )
                                      (.box 10001 0)
                                    )
                                  )
                                  (.box 10001 0)
                                )
                                (.splitB
                                  (.splitA
                                    (.box 10000 0)
                                    (.box 10000 0)
                                  )
                                  (.splitA
                                    (.box 10001 0)
                                    (.box 10000 0)
                                  )
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
                          (.box 124 123)
                          (.box 124 127)
                        )
                      )
                    )
                    (.splitB
                      (.box 119 117)
                      (.box 119 125)
                    )
                  )
                )
                (.splitB
                  (.box 109 105)
                  (.box 109 121)
                )
              )
            )
            (.splitB
              (.box 89 81)
              (.box 89 113)
            )
          )
        )
        (.splitB
          (.splitA
            (.splitB
              (.box 177 257)
              (.box 161 161)
            )
            (.box 193 193)
          )
          (.box 161 97)
        )
      )
    )
    (.splitB
      (.splitA
        (.box 0 65)
        (.box 97 65)
      )
      (.splitA
        (.box 0 65)
        (.box 97 65)
      )
    )
  )

theorem k0w21HighChart1_ok : checkChart k0w21High 1 k0w21HighChart1 = true := by decide +kernel

def k0w21HighChart2 : FacetNumeric.RowTree :=
  (.splitA
    (.splitB
      (.splitA
        (.box 66 129)
        (.splitB
          (.box 129 66)
          (.splitA
            (.box 129 193)
            (.splitB
              (.box 193 129)
              (.splitA
                (.box 193 257)
                (.splitB
                  (.box 257 193)
                  (.splitA
                    (.box 289 321)
                    (.splitB
                      (.box 321 289)
                      (.splitA
                        (.box 353 385)
                        (.box 449 385)
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
            (.splitB
              (.box 113 193)
              (.box 97 65)
            )
            (.splitB
              (.box 81 225)
              (.splitA
                (.box 85 178)
                (.splitB
                  (.box 73 153)
                  (.splitA
                    (.box 77 185)
                    (.splitB
                      (.box 69 169)
                      (.box 69 186)
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
                  (.box 121 73)
                  (.box 121 94)
                )
                (.splitB
                  (.box 105 78)
                  (.splitA
                    (.box 107 93)
                    (.splitB
                      (.box 101 87)
                      (.splitA
                        (.box 103 95)
                        (.splitB
                          (.box 99 91)
                          (.box 99 95)
                        )
                      )
                    )
                  )
                )
              )
              (.splitA
                (.splitB
                  (.splitA
                    (.box 122 109)
                    (.splitB
                      (.box 117 104)
                      (.splitA
                        (.box 118 111)
                        (.splitB
                          (.box 115 108)
                          (.splitA
                            (.box 116 112)
                            (.splitB
                              (.box 114 110)
                              (.box 114 112)
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
                          (.box 127 115)
                          (.box 125 121)
                        )
                        (.splitB
                          (.box 121 117)
                          (.splitA
                            (.splitB
                              (.box 124 118)
                              (.box 123 121)
                            )
                            (.splitB
                              (.box 121 119)
                              (.splitA
                                (.splitB
                                  (.box 123 120)
                                  (.box 122 121)
                                )
                                (.splitB
                                  (.box 121 120)
                                  (.splitA
                                    (.splitB
                                      (.box 122 120)
                                      (.box 122 121)
                                    )
                                    (.splitB
                                      (.box 121 120)
                                      (.box 121 121)
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
                            (.splitB
                              (.box 128 122)
                              (.box 127 125)
                            )
                            (.splitB
                              (.box 125 123)
                              (.splitA
                                (.splitB
                                  (.box 127 124)
                                  (.box 126 125)
                                )
                                (.splitB
                                  (.box 125 124)
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
                              )
                            )
                          )
                          (.splitA
                            (.splitB
                              (.splitA
                                (.splitB
                                  (.box 1 126)
                                  (.box 128 127)
                                )
                                (.splitB
                                  (.box 127 126)
                                  (.splitA
                                    (.splitB
                                      (.box 10000 0)
                                      (.splitA
                                        (.box 128 127)
                                        (.box 10000 0)
                                      )
                                    )
                                    (.splitB
                                      (.splitA
                                        (.box 10000 0)
                                        (.box 10000 0)
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
                                  )
                                )
                              )
                              (.splitA
                                (.splitB
                                  (.splitA
                                    (.splitB
                                      (.box 10000 0)
                                      (.box 10001 0)
                                    )
                                    (.splitB
                                      (.splitA
                                        (.box 10000 0)
                                        (.splitB
                                          (.box 128 127)
                                          (.box 10001 0)
                                        )
                                      )
                                      (.box 10001 0)
                                    )
                                  )
                                  (.box 10001 0)
                                )
                                (.splitB
                                  (.splitA
                                    (.splitB
                                      (.splitA
                                        (.splitB
                                          (.box 10000 0)
                                          (.box 10001 0)
                                        )
                                        (.splitB
                                          (.box 10000 0)
                                          (.box 10001 0)
                                        )
                                      )
                                      (.box 10001 0)
                                    )
                                    (.splitB
                                      (.splitA
                                        (.splitB
                                          (.splitA
                                            (.box 10000 0)
                                            (.box 10000 0)
                                          )
                                          (.box 10001 0)
                                        )
                                        (.splitB
                                          (.splitA
                                            (.box 10000 0)
                                            (.box 10000 0)
                                          )
                                          (.splitA
                                            (.box 10001 0)
                                            (.box 10000 0)
                                          )
                                        )
                                      )
                                      (.splitA
                                        (.box 10001 0)
                                        (.splitB
                                          (.box 10000 0)
                                          (.box 10000 0)
                                        )
                                      )
                                    )
                                  )
                                  (.splitA
                                    (.box 10001 0)
                                    (.splitB
                                      (.splitA
                                        (.box 10001 0)
                                        (.box 127 128)
                                      )
                                      (.box 10000 0)
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
                                      (.box 10000 0)
                                      (.splitA
                                        (.box 127 126)
                                        (.box 10000 0)
                                      )
                                    )
                                    (.splitB
                                      (.box 10000 0)
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
                                        (.box 10000 0)
                                      )
                                    )
                                  )
                                )
                                (.splitB
                                  (.splitA
                                    (.splitB
                                      (.splitA
                                        (.box 10000 0)
                                        (.box 10000 0)
                                      )
                                      (.splitA
                                        (.splitB
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
                                          (.box 126 126)
                                          (.box 10000 0)
                                        )
                                        (.box 10000 0)
                                      )
                                      (.box 10000 0)
                                    )
                                    (.splitB
                                      (.box 10000 0)
                                      (.box 10000 0)
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
                                          (.box 10000 0)
                                          (.box 10000 0)
                                        )
                                        (.splitB
                                          (.box 10000 0)
                                          (.box 10000 0)
                                        )
                                      )
                                      (.splitA
                                        (.box 10000 0)
                                        (.box 10000 0)
                                      )
                                    )
                                    (.splitB
                                      (.box 10000 0)
                                      (.box 10000 0)
                                    )
                                  )
                                  (.box 127 128)
                                )
                                (.splitB
                                  (.box 126 127)
                                  (.box 126 1)
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
                                  (.box 123 122)
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
                                    (.splitB
                                      (.box 10000 0)
                                      (.box 10000 0)
                                    )
                                  )
                                  (.splitA
                                    (.splitB
                                      (.box 124 124)
                                      (.box 124 125)
                                    )
                                    (.box 10000 0)
                                  )
                                )
                              )
                            )
                            (.splitB
                              (.splitA
                                (.splitB
                                  (.splitA
                                    (.box 10000 0)
                                    (.box 10000 0)
                                  )
                                  (.splitA
                                    (.splitB
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
                                      (.box 123 123)
                                      (.box 123 124)
                                    )
                                    (.box 10000 0)
                                  )
                                  (.box 123 124)
                                )
                                (.splitB
                                  (.box 122 123)
                                  (.box 122 125)
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
                                      (.box 10000 0)
                                      (.box 10000 0)
                                    )
                                    (.splitB
                                      (.box 10000 0)
                                      (.box 10000 0)
                                    )
                                  )
                                  (.box 125 126)
                                )
                                (.splitB
                                  (.box 124 125)
                                  (.box 124 127)
                                )
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
                          (.splitA
                            (.splitB
                              (.box 120 114)
                              (.box 119 117)
                            )
                            (.splitB
                              (.box 118 114)
                              (.splitA
                                (.splitB
                                  (.box 119 116)
                                  (.box 118 117)
                                )
                                (.splitB
                                  (.box 118 116)
                                  (.splitA
                                    (.box 118 117)
                                    (.box 117 117)
                                  )
                                )
                              )
                            )
                          )
                          (.splitA
                            (.splitB
                              (.splitA
                                (.splitB
                                  (.box 121 118)
                                  (.box 120 119)
                                )
                                (.splitB
                                  (.box 119 118)
                                  (.splitA
                                    (.splitB
                                      (.box 120 118)
                                      (.box 120 119)
                                    )
                                    (.splitB
                                      (.box 119 118)
                                      (.box 119 119)
                                    )
                                  )
                                )
                              )
                              (.splitA
                                (.splitB
                                  (.splitA
                                    (.splitB
                                      (.box 121 119)
                                      (.box 121 120)
                                    )
                                    (.splitB
                                      (.box 120 119)
                                      (.box 120 120)
                                    )
                                  )
                                  (.splitA
                                    (.splitB
                                      (.box 121 120)
                                      (.box 121 121)
                                    )
                                    (.splitB
                                      (.box 120 120)
                                      (.box 120 121)
                                    )
                                  )
                                )
                                (.splitB
                                  (.splitA
                                    (.splitB
                                      (.box 120 119)
                                      (.box 120 120)
                                    )
                                    (.splitB
                                      (.box 119 119)
                                      (.box 119 120)
                                    )
                                  )
                                  (.box 120 120)
                                )
                              )
                            )
                            (.splitB
                              (.splitA
                                (.splitB
                                  (.splitA
                                    (.box 119 118)
                                    (.box 118 118)
                                  )
                                  (.splitA
                                    (.splitB
                                      (.box 119 118)
                                      (.box 119 119)
                                    )
                                    (.splitB
                                      (.box 118 118)
                                      (.box 118 119)
                                    )
                                  )
                                )
                                (.splitB
                                  (.splitA
                                    (.splitB
                                      (.box 118 117)
                                      (.box 118 118)
                                    )
                                    (.splitB
                                      (.box 117 117)
                                      (.box 117 118)
                                    )
                                  )
                                  (.box 118 118)
                                )
                              )
                              (.splitA
                                (.splitB
                                  (.box 119 119)
                                  (.box 119 121)
                                )
                                (.box 118 120)
                              )
                            )
                          )
                        )
                        (.splitB
                          (.splitA
                            (.splitB
                              (.splitA
                                (.box 116 114)
                                (.splitB
                                  (.box 116 114)
                                  (.box 115 115)
                                )
                              )
                              (.splitA
                                (.splitB
                                  (.box 116 116)
                                  (.splitA
                                    (.box 117 117)
                                    (.box 116 117)
                                  )
                                )
                                (.splitB
                                  (.splitA
                                    (.box 116 116)
                                    (.box 115 116)
                                  )
                                  (.box 116 117)
                                )
                              )
                            )
                            (.splitB
                              (.splitA
                                (.box 115 114)
                                (.box 114 114)
                              )
                              (.splitA
                                (.box 115 116)
                                (.box 114 116)
                              )
                            )
                          )
                          (.splitA
                            (.splitB
                              (.splitA
                                (.splitB
                                  (.box 117 117)
                                  (.box 117 119)
                                )
                                (.box 116 118)
                              )
                              (.box 116 120)
                            )
                            (.box 114 118)
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
                                    (.splitB
                                      (.box 121 121)
                                      (.box 121 122)
                                    )
                                    (.box 120 121)
                                  )
                                  (.box 121 122)
                                )
                                (.box 120 122)
                              )
                              (.box 120 123)
                            )
                            (.box 118 122)
                          )
                          (.box 119 126)
                        )
                        (.box 117 123)
                      )
                    )
                  )
                )
                (.splitB
                  (.splitA
                    (.splitB
                      (.splitA
                        (.box 110 103)
                        (.splitB
                          (.box 107 99)
                          (.splitA
                            (.box 108 104)
                            (.splitB
                              (.box 106 102)
                              (.box 106 104)
                            )
                          )
                        )
                      )
                      (.splitA
                        (.splitB
                          (.splitA
                            (.box 112 108)
                            (.splitB
                              (.box 110 106)
                              (.box 110 108)
                            )
                          )
                          (.splitA
                            (.splitB
                              (.box 112 110)
                              (.box 112 112)
                            )
                            (.splitB
                              (.box 110 110)
                              (.box 110 112)
                            )
                          )
                        )
                        (.splitB
                          (.splitA
                            (.splitB
                              (.box 108 106)
                              (.box 108 108)
                            )
                            (.splitB
                              (.box 106 106)
                              (.box 106 108)
                            )
                          )
                          (.splitA
                            (.splitB
                              (.box 108 110)
                              (.box 108 112)
                            )
                            (.box 106 111)
                          )
                        )
                      )
                    )
                    (.splitB
                      (.splitA
                        (.splitB
                          (.splitA
                            (.box 104 99)
                            (.box 102 99)
                          )
                          (.splitA
                            (.splitB
                              (.box 104 102)
                              (.box 104 104)
                            )
                            (.box 102 103)
                          )
                        )
                        (.splitB
                          (.splitA
                            (.box 100 99)
                            (.box 98 99)
                          )
                          (.box 100 103)
                        )
                      )
                      (.splitA
                        (.splitB
                          (.box 104 106)
                          (.box 103 111)
                        )
                        (.box 99 107)
                      )
                    )
                  )
                  (.splitA
                    (.splitB
                      (.splitA
                        (.splitB
                          (.splitA
                            (.splitB
                              (.box 112 114)
                              (.box 112 116)
                            )
                            (.box 110 114)
                          )
                          (.box 111 117)
                        )
                        (.box 107 115)
                      )
                      (.box 109 123)
                    )
                    (.box 105 117)
                  )
                )
              )
            )
            (.splitB
              (.splitA
                (.splitB
                  (.splitA
                    (.box 91 77)
                    (.splitB
                      (.box 85 73)
                      (.splitA
                        (.box 87 79)
                        (.box 83 78)
                      )
                    )
                  )
                  (.splitA
                    (.splitB
                      (.splitA
                        (.box 95 87)
                        (.splitB
                          (.box 91 83)
                          (.box 91 87)
                        )
                      )
                      (.splitA
                        (.splitB
                          (.box 95 91)
                          (.box 95 95)
                        )
                        (.splitB
                          (.box 91 91)
                          (.box 91 95)
                        )
                      )
                    )
                    (.splitB
                      (.splitA
                        (.splitB
                          (.box 87 83)
                          (.box 87 87)
                        )
                        (.splitB
                          (.box 83 83)
                          (.box 83 87)
                        )
                      )
                      (.splitA
                        (.box 88 92)
                        (.box 83 93)
                      )
                    )
                  )
                )
                (.splitB
                  (.splitA
                    (.splitB
                      (.splitA
                        (.box 79 69)
                        (.box 75 69)
                      )
                      (.splitA
                        (.splitB
                          (.box 79 75)
                          (.box 79 79)
                        )
                        (.box 75 77)
                      )
                    )
                    (.splitB
                      (.splitA
                        (.box 71 69)
                        (.box 67 69)
                      )
                      (.box 71 77)
                    )
                  )
                  (.splitA
                    (.splitB
                      (.box 79 84)
                      (.box 77 93)
                    )
                    (.box 69 85)
                  )
                )
              )
              (.splitA
                (.splitB
                  (.splitA
                    (.splitB
                      (.splitA
                        (.splitB
                          (.box 95 99)
                          (.box 95 103)
                        )
                        (.box 91 99)
                      )
                      (.box 93 105)
                    )
                    (.box 85 101)
                  )
                  (.box 89 117)
                )
                (.box 81 105)
              )
            )
          )
        )
        (.splitB
          (.splitA
            (.splitB
              (.splitA
                (.box 169 225)
                (.splitB
                  (.box 145 289)
                  (.splitA
                    (.box 153 241)
                    (.splitB
                      (.box 137 209)
                      (.box 137 241)
                    )
                  )
                )
              )
              (.splitA
                (.splitB
                  (.splitA
                    (.box 185 153)
                    (.splitB
                      (.box 169 137)
                      (.box 169 153)
                    )
                  )
                  (.splitA
                    (.splitB
                      (.box 185 169)
                      (.splitA
                        (.box 189 185)
                        (.box 181 185)
                      )
                    )
                    (.splitB
                      (.box 169 169)
                      (.box 169 185)
                    )
                  )
                )
                (.splitB
                  (.splitA
                    (.splitB
                      (.box 153 137)
                      (.box 153 153)
                    )
                    (.splitB
                      (.box 137 137)
                      (.box 137 153)
                    )
                  )
                  (.splitA
                    (.splitB
                      (.box 153 169)
                      (.box 153 185)
                    )
                    (.box 137 169)
                  )
                )
              )
            )
            (.splitB
              (.splitA
                (.splitB
                  (.splitA
                    (.box 241 289)
                    (.splitB
                      (.box 209 321)
                      (.box 209 289)
                    )
                  )
                  (.splitA
                    (.splitB
                      (.box 241 209)
                      (.box 241 241)
                    )
                    (.splitB
                      (.box 209 209)
                      (.box 209 241)
                    )
                  )
                )
                (.splitB
                  (.splitA
                    (.splitB
                      (.box 289 321)
                      (.box 289 289)
                    )
                    (.splitB
                      (.splitA
                        (.splitB
                          (.box 353 385)
                          (.box 353 353)
                        )
                        (.box 385 385)
                      )
                      (.box 321 289)
                    )
                  )
                  (.box 289 209)
                )
              )
              (.splitA
                (.splitB
                  (.box 241 138)
                  (.box 225 177)
                )
                (.box 257 145)
              )
            )
          )
          (.splitA
            (.splitB
              (.splitA
                (.splitB
                  (.splitA
                    (.splitB
                      (.box 185 67)
                      (.box 185 77)
                    )
                    (.box 169 69)
                  )
                  (.box 177 81)
                )
                (.box 145 73)
              )
              (.box 161 104)
            )
            (.box 129 81)
          )
        )
      )
    )
    (.splitB
      (.splitA
        (.splitB
          (.splitA
            (.box 225 81)
            (.splitB
              (.box 161 113)
              (.splitA
                (.box 145 81)
                (.box 177 81)
              )
            )
          )
          (.splitA
            (.splitB
              (.splitA
                (.box 257 145)
                (.splitB
                  (.box 225 177)
                  (.box 225 145)
                )
              )
              (.splitA
                (.splitB
                  (.splitA
                    (.box 321 225)
                    (.box 289 225)
                  )
                  (.splitA
                    (.splitB
                      (.box 321 289)
                      (.splitA
                        (.splitB
                          (.box 385 353)
                          (.box 385 385)
                        )
                        (.box 353 321)
                      )
                    )
                    (.box 289 258)
                  )
                )
                (.splitB
                  (.splitA
                    (.box 209 225)
                    (.box 241 225)
                  )
                  (.box 225 289)
                )
              )
            )
            (.splitB
              (.splitA
                (.splitB
                  (.box 145 177)
                  (.box 145 145)
                )
                (.box 177 161)
              )
              (.splitA
                (.splitB
                  (.box 145 225)
                  (.box 145 257)
                )
                (.box 177 225)
              )
            )
          )
        )
        (.splitB
          (.splitA
            (.splitB
              (.box 81 113)
              (.splitA
                (.box 73 81)
                (.box 89 81)
              )
            )
            (.splitB
              (.box 113 113)
              (.box 113 81)
            )
          )
          (.splitA
            (.splitB
              (.box 73 161)
              (.box 81 193)
            )
            (.box 113 161)
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
                    (.splitB
                      (.box 385 385)
                      (.box 321 289)
                    )
                    (.box 289 257)
                  )
                  (.box 257 225)
                )
                (.box 225 257)
              )
              (.box 193 161)
            )
            (.box 161 193)
          )
          (.box 129 65)
        )
        (.box 65 129)
      )
    )
  )

theorem k0w21HighChart2_ok : checkChart k0w21High 2 k0w21HighChart2 = true := by decide +kernel

end HlawkaSchatten.BelowExponent.FSlabCheck
