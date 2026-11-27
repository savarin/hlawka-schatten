/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.FSlabCheck

/-! Exact data for the weighted F-slab facet checks: `Knot102Weight25`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.FSlabCheck

set_option maxRecDepth 40000
set_option maxHeartbeats 0

def k102w25Low : Band := ⟨102, 25, false⟩

def k102w25LowChart0 : FacetNumeric.RowTree :=
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
                                        (.box 10000 0)
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
                                    (.box 10000 0)
                                  )
                                )
                              )
                              (.splitA
                                (.splitB
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
                                    (.box 10000 0)
                                    (.box 10000 0)
                                  )
                                  (.box 10000 0)
                                )
                                (.splitB
                                  (.box 128 125)
                                  (.box 128 124)
                                )
                              )
                              (.splitA
                                (.splitB
                                  (.box 10000 0)
                                  (.box 1 122)
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
                                (.box 1 120)
                                (.box 128 120)
                              )
                              (.box 128 118)
                            )
                            (.splitB
                              (.box 126 120)
                              (.box 126 118)
                            )
                          )
                          (.splitA
                            (.splitB
                              (.box 128 116)
                              (.box 128 114)
                            )
                            (.box 126 115)
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
                            (.box 128 111)
                            (.box 126 111)
                          )
                          (.box 127 107)
                        )
                        (.splitB
                          (.box 123 111)
                          (.box 123 107)
                        )
                      )
                      (.splitA
                        (.box 127 102)
                        (.box 123 101)
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
                      (.box 125 94)
                      (.box 125 85)
                    )
                    (.box 119 90)
                  )
                  (.splitA
                    (.box 125 74)
                    (.box 117 73)
                  )
                )
                (.splitB
                  (.box 113 89)
                  (.box 105 73)
                )
              )
            )
            (.splitB
              (.box 97 113)
              (.box 89 81)
            )
          )
          (.splitA
            (.splitB
              (.splitA
                (.splitB
                  (.box 121 185)
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
              (.box 89 161)
              (.splitA
                (.splitB
                  (.box 89 225)
                  (.box 89 257)
                )
                (.splitB
                  (.box 73 225)
                  (.box 73 257)
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
              (.box 105 257)
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
              (.box 177 257)
              (.box 161 161)
            )
            (.box 193 193)
          )
          (.box 129 97)
        )
      )
    )
    (.splitB
      (.box 0 129)
      (.box 0 129)
    )
  )

theorem k102w25LowChart0_ok : checkChart k102w25Low 0 k102w25LowChart0 = true := by decide +kernel

def k102w25LowChart1 : FacetNumeric.RowTree :=
  (.splitA
    (.splitB
      (.splitA
        (.splitB
          (.box 97 97)
          (.splitA
            (.splitB
              (.box 113 161)
              (.box 105 257)
            )
            (.splitB
              (.box 81 161)
              (.splitA
                (.splitB
                  (.box 89 225)
                  (.box 89 321)
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
          (.box 129 97)
          (.splitA
            (.splitB
              (.box 161 161)
              (.splitA
                (.splitB
                  (.box 177 225)
                  (.box 177 321)
                )
                (.box 145 257)
              )
            )
            (.box 129 193)
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
                  (.box 105 177)
                )
              )
            )
            (.splitB
              (.splitA
                (.splitB
                  (.box 89 321)
                  (.box 89 225)
                )
                (.splitB
                  (.box 73 321)
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
                    (.box 125 74)
                    (.box 117 74)
                  )
                  (.splitA
                    (.splitB
                      (.box 125 85)
                      (.box 125 94)
                    )
                    (.splitB
                      (.box 117 85)
                      (.box 117 93)
                    )
                  )
                )
                (.splitB
                  (.box 109 73)
                  (.box 113 89)
                )
              )
              (.splitA
                (.splitB
                  (.splitA
                    (.splitB
                      (.splitA
                        (.box 127 102)
                        (.box 123 102)
                      )
                      (.splitA
                        (.splitB
                          (.box 127 107)
                          (.splitA
                            (.box 128 111)
                            (.box 126 111)
                          )
                        )
                        (.splitB
                          (.box 123 107)
                          (.box 123 111)
                        )
                      )
                    )
                    (.splitB
                      (.box 117 102)
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
                              (.box 128 116)
                            )
                            (.box 126 115)
                          )
                          (.splitA
                            (.splitB
                              (.box 128 118)
                              (.splitA
                                (.splitB
                                  (.box 1 120)
                                  (.box 1 121)
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
                                  (.box 10000 0)
                                )
                                (.box 10000 0)
                              )
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
                                      (.box 10000 0)
                                    )
                                    (.box 10000 0)
                                  )
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
                                        (.box 10000 0)
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
              (.box 89 81)
              (.box 97 113)
            )
          )
        )
        (.splitB
          (.splitA
            (.splitB
              (.splitA
                (.splitB
                  (.box 177 321)
                  (.box 177 225)
                )
                (.box 145 257)
              )
              (.box 161 161)
            )
            (.box 129 193)
          )
          (.box 65 96)
        )
      )
    )
    (.splitB
      (.box 0 129)
      (.box 0 129)
    )
  )

theorem k102w25LowChart1_ok : checkChart k102w25Low 1 k102w25LowChart1 = true := by decide +kernel

def k102w25LowChart2 : FacetNumeric.RowTree :=
  (.splitA
    (.splitB
      (.splitA
        (.box 65 129)
        (.splitB
          (.box 129 97)
          (.splitA
            (.box 161 193)
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
                (.box 89 177)
                (.splitB
                  (.box 73 145)
                  (.splitA
                    (.box 77 185)
                    (.box 69 178)
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
                    (.box 109 93)
                    (.splitB
                      (.box 101 85)
                      (.splitA
                        (.box 103 93)
                        (.box 99 93)
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
                        (.box 119 111)
                        (.splitB
                          (.box 115 107)
                          (.splitA
                            (.box 116 111)
                            (.box 114 111)
                          )
                        )
                      )
                    )
                  )
                  (.splitA
                    (.splitB
                      (.splitA
                        (.box 126 119)
                        (.splitB
                          (.box 123 117)
                          (.splitA
                            (.box 124 120)
                            (.splitB
                              (.box 122 118)
                              (.splitA
                                (.box 122 120)
                                (.splitB
                                  (.box 122 120)
                                  (.box 121 121)
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
                              (.box 128 125)
                            )
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
                                    (.box 10000 0)
                                    (.box 10000 0)
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
                                      (.box 10000 0)
                                    )
                                    (.splitB
                                      (.box 10000 0)
                                      (.splitA
                                        (.box 10000 0)
                                        (.box 10000 0)
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
                                          (.box 10000 0)
                                          (.box 10001 0)
                                        )
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
                                      (.box 10000 0)
                                    )
                                  )
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
                                )
                                (.splitB
                                  (.splitA
                                    (.splitB
                                      (.box 10000 0)
                                      (.box 10000 0)
                                    )
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
                              )
                              (.splitA
                                (.splitB
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
                                  (.box 124 122)
                                  (.box 10000 0)
                                )
                              )
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
                            )
                            (.splitB
                              (.splitA
                                (.splitB
                                  (.box 122 122)
                                  (.box 10000 0)
                                )
                                (.splitB
                                  (.box 10000 0)
                                  (.box 122 122)
                                )
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
                                    (.box 10000 0)
                                    (.box 10000 0)
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
                              (.box 118 116)
                            )
                          )
                          (.splitA
                            (.splitB
                              (.box 120 118)
                              (.splitA
                                (.splitB
                                  (.box 121 120)
                                  (.splitA
                                    (.box 121 121)
                                    (.box 120 121)
                                  )
                                )
                                (.box 120 120)
                              )
                            )
                            (.splitB
                              (.box 118 118)
                              (.box 118 120)
                            )
                          )
                        )
                        (.splitB
                          (.splitA
                            (.splitB
                              (.box 116 114)
                              (.box 116 116)
                            )
                            (.box 114 115)
                          )
                          (.splitA
                            (.splitB
                              (.box 116 118)
                              (.box 116 120)
                            )
                            (.box 114 119)
                          )
                        )
                      )
                      (.splitA
                        (.splitB
                          (.splitA
                            (.splitB
                              (.splitA
                                (.splitB
                                  (.box 121 121)
                                  (.box 121 123)
                                )
                                (.box 120 122)
                              )
                              (.box 120 124)
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
                          (.box 107 103)
                        )
                      )
                      (.splitA
                        (.splitB
                          (.box 111 107)
                          (.splitA
                            (.box 112 111)
                            (.box 110 111)
                          )
                        )
                        (.splitB
                          (.box 107 107)
                          (.box 107 111)
                        )
                      )
                    )
                    (.splitB
                      (.splitA
                        (.splitB
                          (.box 103 99)
                          (.box 103 103)
                        )
                        (.box 99 101)
                      )
                      (.splitA
                        (.box 104 108)
                        (.box 99 109)
                      )
                    )
                  )
                  (.splitA
                    (.splitB
                      (.splitA
                        (.splitB
                          (.splitA
                            (.box 112 115)
                            (.box 110 115)
                          )
                          (.box 111 119)
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
                    (.box 84 76)
                  )
                  (.splitA
                    (.splitB
                      (.box 93 85)
                      (.splitA
                        (.box 95 93)
                        (.box 91 93)
                      )
                    )
                    (.splitB
                      (.box 85 85)
                      (.box 85 93)
                    )
                  )
                )
                (.splitB
                  (.splitA
                    (.splitB
                      (.box 77 69)
                      (.box 77 77)
                    )
                    (.splitB
                      (.box 69 69)
                      (.box 69 77)
                    )
                  )
                  (.splitA
                    (.box 79 86)
                    (.box 69 85)
                  )
                )
              )
              (.splitA
                (.splitB
                  (.splitA
                    (.splitB
                      (.box 95 100)
                      (.box 93 109)
                    )
                    (.box 85 101)
                  )
                  (.box 89 113)
                )
                (.box 73 104)
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
                  (.box 145 226)
                )
              )
              (.splitA
                (.splitB
                  (.box 169 154)
                  (.splitA
                    (.box 185 178)
                    (.box 169 177)
                  )
                )
                (.splitB
                  (.splitA
                    (.box 153 145)
                    (.box 137 145)
                  )
                  (.box 153 177)
                )
              )
            )
            (.splitB
              (.splitA
                (.splitB
                  (.box 209 289)
                  (.splitA
                    (.box 241 225)
                    (.box 209 225)
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
                        (.box 385 385)
                      )
                      (.box 321 289)
                    )
                  )
                  (.box 257 209)
                )
              )
              (.splitA
                (.splitB
                  (.box 225 137)
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
                  (.box 185 70)
                  (.box 177 89)
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
            (.box 161 81)
          )
          (.splitA
            (.splitB
              (.box 193 145)
              (.splitA
                (.splitB
                  (.box 257 225)
                  (.splitA
                    (.splitB
                      (.box 321 289)
                      (.box 385 385)
                    )
                    (.box 289 257)
                  )
                )
                (.box 209 193)
              )
            )
            (.splitB
              (.box 161 161)
              (.box 129 225)
            )
          )
        )
        (.splitB
          (.splitA
            (.box 81 96)
            (.box 113 97)
          )
          (.splitA
            (.splitB
              (.box 81 161)
              (.box 81 193)
            )
            (.box 113 129)
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

theorem k102w25LowChart2_ok : checkChart k102w25Low 2 k102w25LowChart2 = true := by decide +kernel

def k102w25High : Band := ⟨102, 25, true⟩

def k102w25HighChart0 : FacetNumeric.RowTree :=
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
                                        (.box 10000 0)
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
                                    (.box 10000 0)
                                  )
                                )
                              )
                              (.splitA
                                (.splitB
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
                                  (.box 10000 0)
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
                                    (.box 10000 0)
                                    (.box 10000 0)
                                  )
                                  (.box 10000 0)
                                )
                                (.splitB
                                  (.box 128 125)
                                  (.box 128 124)
                                )
                              )
                              (.splitA
                                (.splitB
                                  (.box 10000 0)
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
                          (.box 124 127)
                          (.box 124 123)
                        )
                      )
                      (.splitA
                        (.splitB
                          (.splitA
                            (.splitB
                              (.splitA
                                (.box 1 120)
                                (.box 128 120)
                              )
                              (.box 128 118)
                            )
                            (.splitB
                              (.box 126 120)
                              (.box 126 118)
                            )
                          )
                          (.splitA
                            (.splitB
                              (.box 128 116)
                              (.box 128 114)
                            )
                            (.box 126 115)
                          )
                        )
                        (.splitB
                          (.box 124 119)
                          (.box 123 115)
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
                            (.box 128 111)
                            (.box 126 111)
                          )
                          (.box 127 107)
                        )
                        (.box 124 110)
                      )
                      (.splitA
                        (.box 127 102)
                        (.box 123 101)
                      )
                    )
                    (.splitB
                      (.box 119 109)
                      (.box 117 101)
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
                      (.box 125 94)
                      (.box 125 85)
                    )
                    (.box 119 90)
                  )
                  (.splitA
                    (.box 125 74)
                    (.box 117 73)
                  )
                )
                (.splitB
                  (.box 109 89)
                  (.box 105 73)
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
                  (.box 121 185)
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
                (.box 89 161)
                (.box 73 161)
              )
              (.splitA
                (.splitB
                  (.box 89 225)
                  (.box 89 257)
                )
                (.splitB
                  (.box 73 225)
                  (.box 73 257)
                )
              )
            )
          )
        )
        (.splitB
          (.box 161 96)
          (.splitA
            (.splitB
              (.box 161 161)
              (.splitA
                (.splitB
                  (.box 177 225)
                  (.box 177 257)
                )
                (.box 145 193)
              )
            )
            (.splitB
              (.box 193 161)
              (.box 193 193)
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
              (.box 177 257)
              (.box 161 161)
            )
            (.box 193 193)
          )
          (.box 129 97)
        )
      )
    )
    (.splitB
      (.splitA
        (.splitB
          (.box 129 97)
          (.box 129 129)
        )
        (.box 97 65)
      )
      (.splitA
        (.box 0 129)
        (.box 97 65)
      )
    )
  )

theorem k102w25HighChart0_ok : checkChart k102w25High 0 k102w25HighChart0 = true := by decide +kernel

def k102w25HighChart1 : FacetNumeric.RowTree :=
  (.splitA
    (.splitB
      (.splitA
        (.splitB
          (.box 97 96)
          (.splitA
            (.splitB
              (.box 113 161)
              (.box 105 257)
            )
            (.splitB
              (.box 81 161)
              (.splitA
                (.box 84 257)
                (.splitB
                  (.box 73 225)
                  (.box 72 321)
                )
              )
            )
          )
        )
        (.splitB
          (.box 161 81)
          (.splitA
            (.splitB
              (.box 161 161)
              (.splitA
                (.splitB
                  (.box 177 225)
                  (.box 185 321)
                )
                (.box 145 257)
              )
            )
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
                  (.splitA
                    (.box 125 177)
                    (.box 117 177)
                  )
                )
                (.splitB
                  (.box 105 145)
                  (.box 109 177)
                )
              )
            )
            (.splitB
              (.splitA
                (.splitB
                  (.box 89 321)
                  (.box 89 225)
                )
                (.splitB
                  (.box 72 321)
                  (.box 73 225)
                )
              )
              (.splitA
                (.box 93 162)
                (.box 73 161)
              )
            )
          )
          (.splitA
            (.splitB
              (.splitA
                (.splitB
                  (.splitA
                    (.splitB
                      (.box 125 69)
                      (.box 125 77)
                    )
                    (.box 119 74)
                  )
                  (.splitA
                    (.splitB
                      (.box 125 85)
                      (.box 125 94)
                    )
                    (.splitB
                      (.box 117 85)
                      (.box 117 94)
                    )
                  )
                )
                (.splitB
                  (.box 109 73)
                  (.box 110 89)
                )
              )
              (.splitA
                (.splitB
                  (.splitA
                    (.splitB
                      (.splitA
                        (.box 127 102)
                        (.box 123 102)
                      )
                      (.splitA
                        (.splitB
                          (.box 127 107)
                          (.splitA
                            (.box 128 111)
                            (.box 126 111)
                          )
                        )
                        (.splitB
                          (.box 123 107)
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
                              (.box 128 116)
                            )
                            (.splitB
                              (.box 126 114)
                              (.box 126 116)
                            )
                          )
                          (.splitA
                            (.splitB
                              (.box 128 118)
                              (.splitA
                                (.splitB
                                  (.box 1 120)
                                  (.box 128 121)
                                )
                                (.splitB
                                  (.box 128 120)
                                  (.box 128 121)
                                )
                              )
                            )
                            (.splitB
                              (.box 126 118)
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
              (.splitA
                (.box 97 81)
                (.box 73 81)
              )
              (.box 89 113)
            )
          )
        )
        (.splitB
          (.splitA
            (.splitB
              (.splitA
                (.splitB
                  (.box 185 321)
                  (.box 177 225)
                )
                (.box 145 257)
              )
              (.box 161 161)
            )
            (.box 129 193)
          )
          (.splitA
            (.box 65 97)
            (.box 193 97)
          )
        )
      )
    )
    (.splitB
      (.splitA
        (.splitB
          (.box 129 97)
          (.box 0 129)
        )
        (.box 97 65)
      )
      (.splitA
        (.splitB
          (.box 129 193)
          (.box 129 97)
        )
        (.box 97 65)
      )
    )
  )

theorem k102w25HighChart1_ok : checkChart k102w25High 1 k102w25HighChart1 = true := by decide +kernel

def k102w25HighChart2 : FacetNumeric.RowTree :=
  (.splitA
    (.splitB
      (.splitA
        (.splitB
          (.box 97 97)
          (.box 97 193)
        )
        (.splitB
          (.box 0 65)
          (.splitA
            (.splitB
              (.box 161 161)
              (.box 161 257)
            )
            (.splitB
              (.box 193 129)
              (.splitA
                (.box 194 257)
                (.splitB
                  (.box 257 193)
                  (.splitA
                    (.box 257 321)
                    (.splitB
                      (.box 321 289)
                      (.splitA
                        (.box 321 385)
                        (.splitB
                          (.box 385 353)
                          (.box 385 385)
                        )
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
              (.box 105 177)
            )
            (.splitB
              (.box 81 225)
              (.splitA
                (.box 84 176)
                (.splitB
                  (.box 73 153)
                  (.splitA
                    (.box 77 185)
                    (.splitB
                      (.box 69 169)
                      (.box 69 185)
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
                  (.box 117 93)
                )
                (.splitB
                  (.box 105 78)
                  (.splitA
                    (.splitB
                      (.box 109 85)
                      (.box 109 95)
                    )
                    (.splitB
                      (.box 101 85)
                      (.splitA
                        (.box 103 95)
                        (.box 99 94)
                      )
                    )
                  )
                )
              )
              (.splitA
                (.splitB
                  (.splitA
                    (.splitB
                      (.box 125 101)
                      (.box 123 111)
                    )
                    (.splitB
                      (.box 115 103)
                      (.splitA
                        (.splitB
                          (.box 119 107)
                          (.box 119 112)
                        )
                        (.splitB
                          (.box 115 107)
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
                          (.box 126 120)
                        )
                        (.splitB
                          (.box 122 116)
                          (.splitA
                            (.splitB
                              (.box 124 118)
                              (.splitA
                                (.box 125 120)
                                (.box 123 120)
                              )
                            )
                            (.splitB
                              (.box 122 118)
                              (.splitA
                                (.splitB
                                  (.box 123 120)
                                  (.box 122 121)
                                )
                                (.splitB
                                  (.box 122 120)
                                  (.splitA
                                    (.box 122 121)
                                    (.box 121 121)
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
                              (.splitA
                                (.box 1 124)
                                (.splitB
                                  (.box 128 124)
                                  (.box 127 125)
                                )
                              )
                            )
                            (.splitB
                              (.splitA
                                (.box 127 122)
                                (.box 125 122)
                              )
                              (.splitA
                                (.splitB
                                  (.box 127 124)
                                  (.splitA
                                    (.box 127 125)
                                    (.box 126 125)
                                  )
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
                                  (.box 128 126)
                                  (.splitA
                                    (.box 1 127)
                                    (.splitB
                                      (.box 128 126)
                                      (.box 128 127)
                                    )
                                  )
                                )
                                (.splitB
                                  (.splitA
                                    (.box 128 126)
                                    (.splitB
                                      (.box 127 125)
                                      (.box 127 126)
                                    )
                                  )
                                  (.splitA
                                    (.splitB
                                      (.box 10000 0)
                                      (.splitA
                                        (.box 128 127)
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
                                          (.box 10000 0)
                                          (.box 10001 0)
                                        )
                                        (.splitB
                                          (.box 10000 0)
                                          (.box 10000 0)
                                        )
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
                                      (.box 10000 0)
                                    )
                                  )
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
                                      (.box 126 126)
                                      (.box 126 127)
                                    )
                                    (.box 10000 0)
                                  )
                                )
                              )
                              (.splitA
                                (.splitB
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
                                  (.box 10000 0)
                                )
                              )
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
                            )
                            (.splitB
                              (.splitA
                                (.splitB
                                  (.box 10000 0)
                                  (.box 10000 0)
                                )
                                (.splitB
                                  (.box 10000 0)
                                  (.box 122 122)
                                )
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
                                    (.box 10000 0)
                                    (.box 10000 0)
                                  )
                                  (.box 125 126)
                                )
                                (.splitB
                                  (.box 124 125)
                                  (.box 124 127)
                                )
                              )
                              (.box 125 128)
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
                              (.box 120 116)
                            )
                            (.splitB
                              (.box 118 114)
                              (.box 118 116)
                            )
                          )
                          (.splitA
                            (.splitB
                              (.box 120 118)
                              (.splitA
                                (.splitB
                                  (.box 120 120)
                                  (.box 121 120)
                                )
                                (.box 120 120)
                              )
                            )
                            (.splitB
                              (.box 118 118)
                              (.box 118 120)
                            )
                          )
                        )
                        (.splitB
                          (.splitA
                            (.splitB
                              (.box 116 114)
                              (.box 116 116)
                            )
                            (.splitB
                              (.box 114 114)
                              (.box 114 116)
                            )
                          )
                          (.splitA
                            (.splitB
                              (.box 116 118)
                              (.box 116 120)
                            )
                            (.box 114 119)
                          )
                        )
                      )
                      (.splitA
                        (.splitB
                          (.splitA
                            (.splitB
                              (.splitA
                                (.box 121 122)
                                (.box 120 122)
                              )
                              (.box 120 124)
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
                          (.box 107 103)
                        )
                      )
                      (.splitA
                        (.splitB
                          (.box 111 107)
                          (.splitA
                            (.box 112 111)
                            (.box 110 111)
                          )
                        )
                        (.splitB
                          (.box 107 107)
                          (.box 107 111)
                        )
                      )
                    )
                    (.splitB
                      (.splitA
                        (.splitB
                          (.box 103 99)
                          (.box 103 103)
                        )
                        (.splitB
                          (.box 99 99)
                          (.box 99 103)
                        )
                      )
                      (.splitA
                        (.box 104 108)
                        (.box 99 109)
                      )
                    )
                  )
                  (.splitA
                    (.splitB
                      (.splitA
                        (.splitB
                          (.box 112 115)
                          (.box 111 119)
                        )
                        (.box 107 115)
                      )
                      (.box 109 123)
                    )
                    (.box 101 117)
                  )
                )
              )
            )
            (.splitB
              (.splitA
                (.splitB
                  (.splitA
                    (.box 93 76)
                    (.splitB
                      (.box 85 69)
                      (.box 85 77)
                    )
                  )
                  (.splitA
                    (.splitB
                      (.box 93 86)
                      (.splitA
                        (.box 95 93)
                        (.box 91 93)
                      )
                    )
                    (.splitB
                      (.box 85 85)
                      (.box 85 93)
                    )
                  )
                )
                (.splitB
                  (.splitA
                    (.splitB
                      (.box 77 69)
                      (.box 77 77)
                    )
                    (.splitB
                      (.box 69 69)
                      (.box 69 77)
                    )
                  )
                  (.splitA
                    (.box 79 86)
                    (.box 69 89)
                  )
                )
              )
              (.splitA
                (.splitB
                  (.splitA
                    (.splitB
                      (.box 95 101)
                      (.box 93 109)
                    )
                    (.box 85 101)
                  )
                  (.box 89 117)
                )
                (.box 73 105)
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
                  (.box 145 289)
                  (.box 145 226)
                )
              )
              (.splitA
                (.splitB
                  (.splitA
                    (.box 185 145)
                    (.box 169 145)
                  )
                  (.splitA
                    (.box 185 178)
                    (.box 169 177)
                  )
                )
                (.splitB
                  (.splitA
                    (.box 153 145)
                    (.box 137 145)
                  )
                  (.box 145 170)
                )
              )
            )
            (.splitB
              (.splitA
                (.splitB
                  (.splitA
                    (.box 241 257)
                    (.box 202 258)
                  )
                  (.splitA
                    (.box 241 225)
                    (.box 209 225)
                  )
                )
                (.splitB
                  (.splitA
                    (.splitB
                      (.box 289 385)
                      (.box 289 289)
                    )
                    (.splitB
                      (.splitA
                        (.box 353 385)
                        (.box 385 385)
                      )
                      (.box 321 289)
                    )
                  )
                  (.box 257 209)
                )
              )
              (.splitA
                (.splitB
                  (.box 225 137)
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
                  (.box 185 69)
                  (.box 177 89)
                )
                (.box 145 73)
              )
              (.box 161 105)
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
            (.box 177 82)
          )
          (.splitA
            (.splitB
              (.splitA
                (.box 257 161)
                (.box 225 161)
              )
              (.splitA
                (.splitB
                  (.box 257 209)
                  (.splitA
                    (.splitB
                      (.box 321 289)
                      (.splitA
                        (.box 0 321)
                        (.box 353 321)
                      )
                    )
                    (.box 289 257)
                  )
                )
                (.box 225 193)
              )
            )
            (.splitB
              (.box 161 161)
              (.box 161 225)
            )
          )
        )
        (.splitB
          (.splitA
            (.box 81 96)
            (.box 113 97)
          )
          (.splitA
            (.splitB
              (.box 81 161)
              (.box 81 193)
            )
            (.box 113 129)
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
                    (.box 0 321)
                    (.box 289 257)
                  )
                  (.box 257 225)
                )
                (.box 225 193)
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

theorem k102w25HighChart2_ok : checkChart k102w25High 2 k102w25HighChart2 = true := by decide +kernel

end HlawkaSchatten.BelowExponent.FSlabCheck
