/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.FSlabCheck

/-! Exact data for the weighted F-slab facet checks: `Knot64Weight23`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.FSlabCheck

set_option maxRecDepth 40000
set_option maxHeartbeats 0

def k64w23Low : Band := ⟨64, 23, false⟩

def k64w23LowChart0 : FacetNumeric.RowTree :=
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
                                  (.box 1 121)
                                  (.box 1 120)
                                )
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
                        (.splitB
                          (.box 127 103)
                          (.box 127 99)
                        )
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
                      (.box 126 94)
                      (.box 125 85)
                    )
                    (.box 119 90)
                  )
                  (.splitA
                    (.splitB
                      (.box 125 77)
                      (.box 125 69)
                    )
                    (.box 117 74)
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
              (.box 97 81)
            )
          )
          (.splitA
            (.splitB
              (.splitA
                (.splitB
                  (.splitA
                    (.box 125 177)
                    (.box 117 177)
                  )
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
          (.box 65 81)
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
                (.box 121 257)
                (.box 105 257)
              )
              (.box 113 161)
            )
            (.splitB
              (.splitA
                (.box 88 257)
                (.box 77 257)
              )
              (.box 81 161)
            )
          )
          (.splitA
            (.box 113 97)
            (.box 81 97)
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
          (.box 129 97)
        )
      )
    )
    (.splitB
      (.box 0 65)
      (.box 0 65)
    )
  )

theorem k64w23LowChart0_ok : checkChart k64w23Low 0 k64w23LowChart0 = true := by decide +kernel

def k64w23LowChart1 : FacetNumeric.RowTree :=
  (.splitA
    (.splitB
      (.splitA
        (.splitB
          (.splitA
            (.box 113 97)
            (.box 81 97)
          )
          (.splitA
            (.splitB
              (.box 113 161)
              (.splitA
                (.box 121 257)
                (.box 105 257)
              )
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
          (.box 65 81)
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
                    (.splitB
                      (.box 125 69)
                      (.box 125 77)
                    )
                    (.box 117 74)
                  )
                  (.splitA
                    (.splitB
                      (.box 125 85)
                      (.splitA
                        (.box 127 93)
                        (.box 123 93)
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
                          (.box 127 103)
                        )
                        (.box 124 101)
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
                                  (.splitA
                                    (.box 1 121)
                                    (.box 128 121)
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
                                  (.box 10000 0)
                                )
                                (.splitB
                                  (.box 128 122)
                                  (.box 128 123)
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
              (.box 97 81)
              (.box 97 113)
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
          (.box 65 97)
        )
      )
    )
    (.splitB
      (.box 0 65)
      (.box 0 65)
    )
  )

theorem k64w23LowChart1_ok : checkChart k64w23Low 1 k64w23LowChart1 = true := by decide +kernel

def k64w23LowChart2 : FacetNumeric.RowTree :=
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
                (.box 89 178)
                (.splitB
                  (.box 73 145)
                  (.splitA
                    (.box 77 185)
                    (.box 67 184)
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
                    (.box 121 109)
                    (.splitB
                      (.box 117 105)
                      (.splitA
                        (.box 117 111)
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
                        (.box 125 119)
                        (.splitB
                          (.box 123 117)
                          (.splitA
                            (.box 123 120)
                            (.splitB
                              (.box 122 118)
                              (.splitA
                                (.splitB
                                  (.box 123 120)
                                  (.box 123 121)
                                )
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
                                        (.splitB
                                          (.box 10000 0)
                                          (.box 10000 0)
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
                                          (.box 127 127)
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
                                  (.box 10000 0)
                                  (.box 123 124)
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
                              (.splitA
                                (.box 120 118)
                                (.splitB
                                  (.box 120 118)
                                  (.box 119 119)
                                )
                              )
                              (.splitA
                                (.splitB
                                  (.box 120 120)
                                  (.splitA
                                    (.box 121 121)
                                    (.box 120 121)
                                  )
                                )
                                (.splitB
                                  (.splitA
                                    (.box 120 120)
                                    (.box 119 120)
                                  )
                                  (.box 120 120)
                                )
                              )
                            )
                            (.splitB
                              (.splitA
                                (.box 119 118)
                                (.box 118 118)
                              )
                              (.splitA
                                (.box 119 120)
                                (.box 118 120)
                              )
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
                          (.splitA
                            (.box 112 107)
                            (.box 110 107)
                          )
                          (.splitA
                            (.splitB
                              (.box 112 110)
                              (.box 112 112)
                            )
                            (.box 110 111)
                          )
                        )
                        (.splitB
                          (.splitA
                            (.box 108 107)
                            (.box 106 107)
                          )
                          (.box 108 111)
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
                        (.splitB
                          (.box 103 107)
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
                    (.splitB
                      (.box 85 69)
                      (.box 85 77)
                    )
                  )
                  (.splitA
                    (.splitB
                      (.box 92 87)
                      (.splitA
                        (.splitB
                          (.box 95 91)
                          (.box 95 95)
                        )
                        (.box 91 93)
                      )
                    )
                    (.splitB
                      (.splitA
                        (.box 87 85)
                        (.box 83 85)
                      )
                      (.box 87 93)
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
                    (.splitB
                      (.box 77 85)
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
                        (.box 95 100)
                        (.box 91 101)
                      )
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
                  (.box 137 242)
                )
              )
              (.splitA
                (.splitB
                  (.splitA
                    (.box 185 145)
                    (.box 169 153)
                  )
                  (.splitA
                    (.splitB
                      (.box 185 169)
                      (.box 185 185)
                    )
                    (.box 169 177)
                  )
                )
                (.splitB
                  (.splitA
                    (.box 153 146)
                    (.box 137 145)
                  )
                  (.box 153 169)
                )
              )
            )
            (.splitB
              (.splitA
                (.splitB
                  (.splitA
                    (.box 241 257)
                    (.box 209 257)
                  )
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
                  (.box 289 225)
                )
              )
              (.splitA
                (.splitB
                  (.box 241 145)
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
            (.box 177 81)
          )
          (.splitA
            (.splitB
              (.splitA
                (.box 257 161)
                (.box 225 161)
              )
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
                (.splitB
                  (.box 225 225)
                  (.box 225 257)
                )
              )
            )
            (.splitB
              (.splitA
                (.box 145 161)
                (.box 177 161)
              )
              (.box 145 225)
            )
          )
        )
        (.splitB
          (.splitA
            (.splitB
              (.box 81 113)
              (.box 81 81)
            )
            (.box 113 97)
          )
          (.splitA
            (.splitB
              (.box 81 161)
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

theorem k64w23LowChart2_ok : checkChart k64w23Low 2 k64w23LowChart2 = true := by decide +kernel

def k64w23High : Band := ⟨64, 23, true⟩

def k64w23HighChart0 : FacetNumeric.RowTree :=
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
                                  (.box 10000 0)
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
                                (.splitB
                                  (.box 1 121)
                                  (.box 1 120)
                                )
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
                        (.splitB
                          (.box 123 111)
                          (.box 123 107)
                        )
                      )
                      (.splitA
                        (.splitB
                          (.box 127 103)
                          (.box 127 99)
                        )
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
                      (.box 126 94)
                      (.box 125 85)
                    )
                    (.box 119 90)
                  )
                  (.splitA
                    (.box 126 74)
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
                  (.splitA
                    (.box 125 177)
                    (.box 117 177)
                  )
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
              (.box 88 161)
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
              (.box 178 258)
            )
            (.box 129 129)
          )
        )
      )
      (.splitA
        (.splitB
          (.splitA
            (.splitB
              (.splitA
                (.box 121 257)
                (.box 105 257)
              )
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
          (.splitA
            (.box 113 97)
            (.box 81 97)
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
          (.box 129 97)
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

theorem k64w23HighChart0_ok : checkChart k64w23High 0 k64w23HighChart0 = true := by decide +kernel

def k64w23HighChart1 : FacetNumeric.RowTree :=
  (.splitA
    (.splitB
      (.splitA
        (.splitB
          (.splitA
            (.box 113 97)
            (.box 81 97)
          )
          (.splitA
            (.splitB
              (.box 113 161)
              (.splitA
                (.box 121 257)
                (.box 105 257)
              )
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
          (.box 161 97)
          (.splitA
            (.splitB
              (.box 161 161)
              (.splitA
                (.box 65 257)
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
                  (.box 90 321)
                  (.box 89 225)
                )
                (.splitB
                  (.box 73 321)
                  (.box 73 225)
                )
              )
              (.splitA
                (.box 97 161)
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
                    (.splitB
                      (.box 117 69)
                      (.box 117 77)
                    )
                  )
                  (.splitA
                    (.splitB
                      (.box 125 85)
                      (.splitA
                        (.box 127 93)
                        (.box 123 93)
                      )
                    )
                    (.splitB
                      (.box 117 85)
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
                          (.box 127 103)
                        )
                        (.splitB
                          (.box 123 99)
                          (.box 123 103)
                        )
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
                                  (.box 128 120)
                                  (.splitA
                                    (.box 1 121)
                                    (.box 128 121)
                                  )
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
              (.box 90 81)
              (.box 89 113)
            )
          )
        )
        (.splitB
          (.splitA
            (.splitB
              (.splitA
                (.box 65 257)
                (.box 145 257)
              )
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

theorem k64w23HighChart1_ok : checkChart k64w23High 1 k64w23HighChart1 = true := by decide +kernel

def k64w23HighChart2 : FacetNumeric.RowTree :=
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
                (.box 193 257)
                (.splitB
                  (.box 257 193)
                  (.splitA
                    (.box 257 321)
                    (.splitB
                      (.box 321 289)
                      (.splitA
                        (.box 353 385)
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
              (.box 97 65)
            )
            (.splitB
              (.box 81 225)
              (.splitA
                (.box 85 177)
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
                  (.box 113 97)
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
                    (.splitB
                      (.box 125 101)
                      (.box 121 113)
                    )
                    (.splitB
                      (.box 117 104)
                      (.splitA
                        (.splitB
                          (.box 119 107)
                          (.box 119 112)
                        )
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
                          (.box 126 120)
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
                                  (.box 128 125)
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
                                          (.box 127 127)
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
                                  (.box 10000 0)
                                  (.box 123 124)
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
                                    (.box 121 120)
                                    (.box 120 120)
                                  )
                                )
                                (.splitB
                                  (.splitA
                                    (.box 120 120)
                                    (.box 119 120)
                                  )
                                  (.box 120 120)
                                )
                              )
                            )
                            (.splitB
                              (.splitA
                                (.box 119 118)
                                (.box 118 118)
                              )
                              (.splitA
                                (.box 119 120)
                                (.box 118 120)
                              )
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
                                  (.box 121 121)
                                  (.box 121 123)
                                )
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
                          (.splitA
                            (.box 112 107)
                            (.box 110 107)
                          )
                          (.splitA
                            (.splitB
                              (.box 112 110)
                              (.box 112 112)
                            )
                            (.box 110 111)
                          )
                        )
                        (.splitB
                          (.splitA
                            (.box 108 107)
                            (.box 106 107)
                          )
                          (.box 108 111)
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
                        (.splitB
                          (.box 103 107)
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
                            (.box 113 114)
                            (.box 110 115)
                          )
                          (.box 111 119)
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
                      (.box 85 69)
                      (.box 85 77)
                    )
                  )
                  (.splitA
                    (.splitB
                      (.splitA
                        (.box 95 85)
                        (.box 91 85)
                      )
                      (.splitA
                        (.splitB
                          (.box 95 91)
                          (.box 95 95)
                        )
                        (.box 91 93)
                      )
                    )
                    (.splitB
                      (.splitA
                        (.box 87 85)
                        (.box 83 85)
                      )
                      (.box 87 93)
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
                    (.splitB
                      (.box 77 85)
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
                      (.box 95 100)
                      (.box 93 109)
                    )
                    (.box 85 101)
                  )
                  (.box 89 117)
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
                (.box 169 225)
                (.splitB
                  (.box 145 289)
                  (.splitA
                    (.box 153 241)
                    (.box 137 226)
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
                      (.box 185 185)
                    )
                    (.box 170 176)
                  )
                )
                (.splitB
                  (.splitA
                    (.box 153 146)
                    (.box 137 145)
                  )
                  (.box 153 169)
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
                  (.box 257 210)
                )
              )
              (.splitA
                (.splitB
                  (.box 225 138)
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
            (.splitB
              (.box 161 113)
              (.box 161 81)
            )
          )
          (.splitA
            (.splitB
              (.splitA
                (.box 257 145)
                (.box 225 161)
              )
              (.splitA
                (.splitB
                  (.box 257 209)
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
                    (.box 289 257)
                  )
                )
                (.splitB
                  (.box 225 225)
                  (.box 225 257)
                )
              )
            )
            (.splitB
              (.splitA
                (.box 145 161)
                (.box 177 161)
              )
              (.box 145 225)
            )
          )
        )
        (.splitB
          (.splitA
            (.splitB
              (.box 81 113)
              (.box 81 81)
            )
            (.box 113 97)
          )
          (.splitA
            (.splitB
              (.box 81 161)
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
                      (.box 0 385)
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
        (.box 97 129)
      )
    )
  )

theorem k64w23HighChart2_ok : checkChart k64w23High 2 k64w23HighChart2 = true := by decide +kernel

end HlawkaSchatten.BelowExponent.FSlabCheck
