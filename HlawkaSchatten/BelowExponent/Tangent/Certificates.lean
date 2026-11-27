/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Tangent.Tree
public import HlawkaSchatten.BelowExponent.Tangent.Cells.Cells000_009
public import HlawkaSchatten.BelowExponent.Tangent.Cells.Cells010_019
public import HlawkaSchatten.BelowExponent.Tangent.Cells.Cells020_023
public import HlawkaSchatten.BelowExponent.Tangent.Cells.Cells024_029
public import HlawkaSchatten.BelowExponent.Tangent.Cells.Cells030_039
public import HlawkaSchatten.BelowExponent.Tangent.Cells.Cells040_049
public import HlawkaSchatten.BelowExponent.Tangent.Cells.Cells050_058
public import HlawkaSchatten.BelowExponent.Tangent.Cells.Cells059_064
public import HlawkaSchatten.BelowExponent.Tangent.Cells.Cells065_068
public import HlawkaSchatten.BelowExponent.Tangent.Cells.Cells069_072
public import HlawkaSchatten.BelowExponent.Tangent.Cells.Cells073_077
public import HlawkaSchatten.BelowExponent.Tangent.Cells.Cells078_080
public import HlawkaSchatten.BelowExponent.Tangent.Cells.Cells081_082
public import HlawkaSchatten.BelowExponent.Tangent.Cells.Cells083_084
public import HlawkaSchatten.BelowExponent.Tangent.Cells.Cells085_086
public import HlawkaSchatten.BelowExponent.Tangent.Cells.Cells087_089
public import HlawkaSchatten.BelowExponent.Tangent.Cells.Cells090_092
public import HlawkaSchatten.BelowExponent.Tangent.Cells.Cells093_095
public import HlawkaSchatten.BelowExponent.Tangent.Cells.Cells096_097
public import HlawkaSchatten.BelowExponent.Tangent.Cells.Cells098_100
public import HlawkaSchatten.BelowExponent.Tangent.Cells.Cells101_106
public import HlawkaSchatten.BelowExponent.Tangent.Cells.Cells107_111
public import HlawkaSchatten.BelowExponent.Tangent.Cells.Cells112_114
public import HlawkaSchatten.BelowExponent.Tangent.Cells.Cells115_119
public import HlawkaSchatten.BelowExponent.Tangent.Cells.Cells120_122
public import HlawkaSchatten.BelowExponent.Tangent.Cells.Cells123_124
public import HlawkaSchatten.BelowExponent.Tangent.Cells.Cells125_126
public import HlawkaSchatten.BelowExponent.Tangent.Cells.Cells127_128
public import HlawkaSchatten.BelowExponent.Tangent.Cells.Cells129_130
public import HlawkaSchatten.BelowExponent.Tangent.Cells.Cells131_132
public import HlawkaSchatten.BelowExponent.Tangent.Cells.Cell133
public import HlawkaSchatten.BelowExponent.Tangent.Cells.Cells134_136
public import HlawkaSchatten.BelowExponent.Tangent.Cells.Cells137_138
public import HlawkaSchatten.BelowExponent.Tangent.Cells.Cell139
public import HlawkaSchatten.BelowExponent.Tangent.Cells.Cells140_142
public import HlawkaSchatten.BelowExponent.Tangent.Cells.Cells143_144
public import HlawkaSchatten.BelowExponent.Tangent.Cells.Cell145
public import HlawkaSchatten.BelowExponent.Tangent.Cells.Cell146
public import HlawkaSchatten.BelowExponent.Tangent.Cells.Cell147
public import HlawkaSchatten.BelowExponent.Tangent.Cells.Cell148
public import HlawkaSchatten.BelowExponent.Tangent.Cells.Cells149_150
public import HlawkaSchatten.BelowExponent.Tangent.Cells.Cell151
public import HlawkaSchatten.BelowExponent.Tangent.Cells.Cells152_153
public import HlawkaSchatten.BelowExponent.Tangent.Cells.Cell154
public import HlawkaSchatten.BelowExponent.Tangent.Cells.Cell155
public import HlawkaSchatten.BelowExponent.Tangent.Cells.Cell156
public import HlawkaSchatten.BelowExponent.Tangent.Cells.Cell157
public import HlawkaSchatten.BelowExponent.Tangent.Cells.Cell158
public import HlawkaSchatten.BelowExponent.Tangent.Cells.Cell159
public import HlawkaSchatten.BelowExponent.Tangent.Cells.Cell160
public import HlawkaSchatten.BelowExponent.Tangent.Cells.Cell161
public import HlawkaSchatten.BelowExponent.Tangent.Cells.Cell162
public import HlawkaSchatten.BelowExponent.Tangent.Cells.Cell163
public import HlawkaSchatten.BelowExponent.Tangent.Cells.Cell164
public import HlawkaSchatten.BelowExponent.Tangent.Cells.Cell165
public import HlawkaSchatten.BelowExponent.Tangent.Cells.Cell166

set_option autoImplicit true
set_option relaxedAutoImplicit true

@[expose] public section

namespace HlawkaSchatten.BelowExponent.TC

/-- Cell data in the order of the checked partition's non-centre leaves. -/
def R002_cells : List CellData := [
  R002_c0,
  R002_c1,
  R002_c2,
  R002_c3,
  R002_c4,
  R002_c5,
  R002_c6,
  R002_c7,
  R002_c8,
  R002_c9,
  R002_c10,
  R002_c11,
  R002_c12,
  R002_c13,
  R002_c14,
  R002_c15,
  R002_c16,
  R002_c17,
  R002_c18,
  R002_c19,
  R002_c20,
  R002_c21,
  R002_c22,
  R002_c23,
  R002_c24,
  R002_c25,
  R002_c26,
  R002_c27,
  R002_c28,
  R002_c29,
  R002_c30,
  R002_c31,
  R002_c32,
  R002_c33,
  R002_c34,
  R002_c35,
  R002_c36,
  R002_c37,
  R002_c38,
  R002_c39,
  R002_c40,
  R002_c41,
  R002_c42,
  R002_c43,
  R002_c44,
  R002_c45,
  R002_c46,
  R002_c47,
  R002_c48,
  R002_c49,
  R002_c50,
  R002_c51,
  R002_c52,
  R002_c53,
  R002_c54,
  R002_c55,
  R002_c56,
  R002_c57,
  R002_c58,
  R002_c59,
  R002_c60,
  R002_c61,
  R002_c62,
  R002_c63,
  R002_c64,
  R002_c65,
  R002_c66,
  R002_c67,
  R002_c68,
  R002_c69,
  R002_c70,
  R002_c71,
  R002_c72,
  R002_c73,
  R002_c74,
  R002_c75,
  R002_c76,
  R002_c77,
  R002_c78,
  R002_c79,
  R002_c80,
  R002_c81,
  R002_c82,
  R002_c83,
  R002_c84,
  R002_c85,
  R002_c86,
  R002_c87,
  R002_c88,
  R002_c89,
  R002_c90,
  R002_c91,
  R002_c92,
  R002_c93,
  R002_c94,
  R002_c95,
  R002_c96,
  R002_c97,
  R002_c98,
  R002_c99,
  R002_c100,
  R002_c101,
  R002_c102,
  R002_c103,
  R002_c104,
  R002_c105,
  R002_c106,
  R002_c107,
  R002_c108,
  R002_c109,
  R002_c110,
  R002_c111,
  R002_c112,
  R002_c113,
  R002_c114,
  R002_c115,
  R002_c116,
  R002_c117,
  R002_c118,
  R002_c119,
  R002_c120,
  R002_c121,
  R002_c122,
  R002_c123,
  R002_c124,
  R002_c125,
  R002_c126,
  R002_c127,
  R002_c128,
  R002_c129,
  R002_c130,
  R002_c131,
  R002_c132,
  R002_c133,
  R002_c134,
  R002_c135,
  R002_c136,
  R002_c137,
  R002_c138,
  R002_c139,
  R002_c140,
  R002_c141,
  R002_c142,
  R002_c143,
  R002_c144,
  R002_c145,
  R002_c146,
  R002_c147,
  R002_c148,
  R002_c149,
  R002_c150,
  R002_c151,
  R002_c152,
  R002_c153,
  R002_c154,
  R002_c155,
  R002_c156,
  R002_c157,
  R002_c158,
  R002_c159,
  R002_c160,
  R002_c161,
  R002_c162,
  R002_c163,
  R002_c164,
  R002_c165,
  R002_c166]

set_option maxRecDepth 10000 in
theorem R002_cells_length : R002_cells.length = R002_geoms.length := by rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Symbolic assembly from the separately replayable arithmetic lemmas. -/
theorem R002_leaf_set_of_checks
    (h000 : cellOK R002_hdr (R002_geoms.getD 0 default) R002_c0 = true)
    (h001 : cellOK R002_hdr (R002_geoms.getD 1 default) R002_c1 = true)
    (h002 : cellOK R002_hdr (R002_geoms.getD 2 default) R002_c2 = true)
    (h003 : cellOK R002_hdr (R002_geoms.getD 3 default) R002_c3 = true)
    (h004 : cellOK R002_hdr (R002_geoms.getD 4 default) R002_c4 = true)
    (h005 : cellOK R002_hdr (R002_geoms.getD 5 default) R002_c5 = true)
    (h006 : cellOK R002_hdr (R002_geoms.getD 6 default) R002_c6 = true)
    (h007 : cellOK R002_hdr (R002_geoms.getD 7 default) R002_c7 = true)
    (h008 : cellOK R002_hdr (R002_geoms.getD 8 default) R002_c8 = true)
    (h009 : cellOK R002_hdr (R002_geoms.getD 9 default) R002_c9 = true)
    (h010 : cellOK R002_hdr (R002_geoms.getD 10 default) R002_c10 = true)
    (h011 : cellOK R002_hdr (R002_geoms.getD 11 default) R002_c11 = true)
    (h012 : cellOK R002_hdr (R002_geoms.getD 12 default) R002_c12 = true)
    (h013 : cellOK R002_hdr (R002_geoms.getD 13 default) R002_c13 = true)
    (h014 : cellOK R002_hdr (R002_geoms.getD 14 default) R002_c14 = true)
    (h015 : cellOK R002_hdr (R002_geoms.getD 15 default) R002_c15 = true)
    (h016 : cellOK R002_hdr (R002_geoms.getD 16 default) R002_c16 = true)
    (h017 : cellOK R002_hdr (R002_geoms.getD 17 default) R002_c17 = true)
    (h018 : cellOK R002_hdr (R002_geoms.getD 18 default) R002_c18 = true)
    (h019 : cellOK R002_hdr (R002_geoms.getD 19 default) R002_c19 = true)
    (h020 : cellOK R002_hdr (R002_geoms.getD 20 default) R002_c20 = true)
    (h021 : cellOK R002_hdr (R002_geoms.getD 21 default) R002_c21 = true)
    (h022 : cellOK R002_hdr (R002_geoms.getD 22 default) R002_c22 = true)
    (h023 : cellOK R002_hdr (R002_geoms.getD 23 default) R002_c23 = true)
    (h024 : cellOK R002_hdr (R002_geoms.getD 24 default) R002_c24 = true)
    (h025 : cellOK R002_hdr (R002_geoms.getD 25 default) R002_c25 = true)
    (h026 : cellOK R002_hdr (R002_geoms.getD 26 default) R002_c26 = true)
    (h027 : cellOK R002_hdr (R002_geoms.getD 27 default) R002_c27 = true)
    (h028 : cellOK R002_hdr (R002_geoms.getD 28 default) R002_c28 = true)
    (h029 : cellOK R002_hdr (R002_geoms.getD 29 default) R002_c29 = true)
    (h030 : cellOK R002_hdr (R002_geoms.getD 30 default) R002_c30 = true)
    (h031 : cellOK R002_hdr (R002_geoms.getD 31 default) R002_c31 = true)
    (h032 : cellOK R002_hdr (R002_geoms.getD 32 default) R002_c32 = true)
    (h033 : cellOK R002_hdr (R002_geoms.getD 33 default) R002_c33 = true)
    (h034 : cellOK R002_hdr (R002_geoms.getD 34 default) R002_c34 = true)
    (h035 : cellOK R002_hdr (R002_geoms.getD 35 default) R002_c35 = true)
    (h036 : cellOK R002_hdr (R002_geoms.getD 36 default) R002_c36 = true)
    (h037 : cellOK R002_hdr (R002_geoms.getD 37 default) R002_c37 = true)
    (h038 : cellOK R002_hdr (R002_geoms.getD 38 default) R002_c38 = true)
    (h039 : cellOK R002_hdr (R002_geoms.getD 39 default) R002_c39 = true)
    (h040 : cellOK R002_hdr (R002_geoms.getD 40 default) R002_c40 = true)
    (h041 : cellOK R002_hdr (R002_geoms.getD 41 default) R002_c41 = true)
    (h042 : cellOK R002_hdr (R002_geoms.getD 42 default) R002_c42 = true)
    (h043 : cellOK R002_hdr (R002_geoms.getD 43 default) R002_c43 = true)
    (h044 : cellOK R002_hdr (R002_geoms.getD 44 default) R002_c44 = true)
    (h045 : cellOK R002_hdr (R002_geoms.getD 45 default) R002_c45 = true)
    (h046 : cellOK R002_hdr (R002_geoms.getD 46 default) R002_c46 = true)
    (h047 : cellOK R002_hdr (R002_geoms.getD 47 default) R002_c47 = true)
    (h048 : cellOK R002_hdr (R002_geoms.getD 48 default) R002_c48 = true)
    (h049 : cellOK R002_hdr (R002_geoms.getD 49 default) R002_c49 = true)
    (h050 : cellOK R002_hdr (R002_geoms.getD 50 default) R002_c50 = true)
    (h051 : cellOK R002_hdr (R002_geoms.getD 51 default) R002_c51 = true)
    (h052 : cellOK R002_hdr (R002_geoms.getD 52 default) R002_c52 = true)
    (h053 : cellOK R002_hdr (R002_geoms.getD 53 default) R002_c53 = true)
    (h054 : cellOK R002_hdr (R002_geoms.getD 54 default) R002_c54 = true)
    (h055 : cellOK R002_hdr (R002_geoms.getD 55 default) R002_c55 = true)
    (h056 : cellOK R002_hdr (R002_geoms.getD 56 default) R002_c56 = true)
    (h057 : cellOK R002_hdr (R002_geoms.getD 57 default) R002_c57 = true)
    (h058 : cellOK R002_hdr (R002_geoms.getD 58 default) R002_c58 = true)
    (h059 : cellOK R002_hdr (R002_geoms.getD 59 default) R002_c59 = true)
    (h060 : cellOK R002_hdr (R002_geoms.getD 60 default) R002_c60 = true)
    (h061 : cellOK R002_hdr (R002_geoms.getD 61 default) R002_c61 = true)
    (h062 : cellOK R002_hdr (R002_geoms.getD 62 default) R002_c62 = true)
    (h063 : cellOK R002_hdr (R002_geoms.getD 63 default) R002_c63 = true)
    (h064 : cellOK R002_hdr (R002_geoms.getD 64 default) R002_c64 = true)
    (h065 : cellOK R002_hdr (R002_geoms.getD 65 default) R002_c65 = true)
    (h066 : cellOK R002_hdr (R002_geoms.getD 66 default) R002_c66 = true)
    (h067 : cellOK R002_hdr (R002_geoms.getD 67 default) R002_c67 = true)
    (h068 : cellOK R002_hdr (R002_geoms.getD 68 default) R002_c68 = true)
    (h069 : cellOK R002_hdr (R002_geoms.getD 69 default) R002_c69 = true)
    (h070 : cellOK R002_hdr (R002_geoms.getD 70 default) R002_c70 = true)
    (h071 : cellOK R002_hdr (R002_geoms.getD 71 default) R002_c71 = true)
    (h072 : cellOK R002_hdr (R002_geoms.getD 72 default) R002_c72 = true)
    (h073 : cellOK R002_hdr (R002_geoms.getD 73 default) R002_c73 = true)
    (h074 : cellOK R002_hdr (R002_geoms.getD 74 default) R002_c74 = true)
    (h075 : cellOK R002_hdr (R002_geoms.getD 75 default) R002_c75 = true)
    (h076 : cellOK R002_hdr (R002_geoms.getD 76 default) R002_c76 = true)
    (h077 : cellOK R002_hdr (R002_geoms.getD 77 default) R002_c77 = true)
    (h078 : cellOK R002_hdr (R002_geoms.getD 78 default) R002_c78 = true)
    (h079 : cellOK R002_hdr (R002_geoms.getD 79 default) R002_c79 = true)
    (h080 : cellOK R002_hdr (R002_geoms.getD 80 default) R002_c80 = true)
    (h081 : cellOK R002_hdr (R002_geoms.getD 81 default) R002_c81 = true)
    (h082 : cellOK R002_hdr (R002_geoms.getD 82 default) R002_c82 = true)
    (h083 : cellOK R002_hdr (R002_geoms.getD 83 default) R002_c83 = true)
    (h084 : cellOK R002_hdr (R002_geoms.getD 84 default) R002_c84 = true)
    (h085 : cellOK R002_hdr (R002_geoms.getD 85 default) R002_c85 = true)
    (h086 : cellOK R002_hdr (R002_geoms.getD 86 default) R002_c86 = true)
    (h087 : cellOK R002_hdr (R002_geoms.getD 87 default) R002_c87 = true)
    (h088 : cellOK R002_hdr (R002_geoms.getD 88 default) R002_c88 = true)
    (h089 : cellOK R002_hdr (R002_geoms.getD 89 default) R002_c89 = true)
    (h090 : cellOK R002_hdr (R002_geoms.getD 90 default) R002_c90 = true)
    (h091 : cellOK R002_hdr (R002_geoms.getD 91 default) R002_c91 = true)
    (h092 : cellOK R002_hdr (R002_geoms.getD 92 default) R002_c92 = true)
    (h093 : cellOK R002_hdr (R002_geoms.getD 93 default) R002_c93 = true)
    (h094 : cellOK R002_hdr (R002_geoms.getD 94 default) R002_c94 = true)
    (h095 : cellOK R002_hdr (R002_geoms.getD 95 default) R002_c95 = true)
    (h096 : cellOK R002_hdr (R002_geoms.getD 96 default) R002_c96 = true)
    (h097 : cellOK R002_hdr (R002_geoms.getD 97 default) R002_c97 = true)
    (h098 : cellOK R002_hdr (R002_geoms.getD 98 default) R002_c98 = true)
    (h099 : cellOK R002_hdr (R002_geoms.getD 99 default) R002_c99 = true)
    (h100 : cellOK R002_hdr (R002_geoms.getD 100 default) R002_c100 = true)
    (h101 : cellOK R002_hdr (R002_geoms.getD 101 default) R002_c101 = true)
    (h102 : cellOK R002_hdr (R002_geoms.getD 102 default) R002_c102 = true)
    (h103 : cellOK R002_hdr (R002_geoms.getD 103 default) R002_c103 = true)
    (h104 : cellOK R002_hdr (R002_geoms.getD 104 default) R002_c104 = true)
    (h105 : cellOK R002_hdr (R002_geoms.getD 105 default) R002_c105 = true)
    (h106 : cellOK R002_hdr (R002_geoms.getD 106 default) R002_c106 = true)
    (h107 : cellOK R002_hdr (R002_geoms.getD 107 default) R002_c107 = true)
    (h108 : cellOK R002_hdr (R002_geoms.getD 108 default) R002_c108 = true)
    (h109 : cellOK R002_hdr (R002_geoms.getD 109 default) R002_c109 = true)
    (h110 : cellOK R002_hdr (R002_geoms.getD 110 default) R002_c110 = true)
    (h111 : cellOK R002_hdr (R002_geoms.getD 111 default) R002_c111 = true)
    (h112 : cellOK R002_hdr (R002_geoms.getD 112 default) R002_c112 = true)
    (h113 : cellOK R002_hdr (R002_geoms.getD 113 default) R002_c113 = true)
    (h114 : cellOK R002_hdr (R002_geoms.getD 114 default) R002_c114 = true)
    (h115 : cellOK R002_hdr (R002_geoms.getD 115 default) R002_c115 = true)
    (h116 : cellOK R002_hdr (R002_geoms.getD 116 default) R002_c116 = true)
    (h117 : cellOK R002_hdr (R002_geoms.getD 117 default) R002_c117 = true)
    (h118 : cellOK R002_hdr (R002_geoms.getD 118 default) R002_c118 = true)
    (h119 : cellOK R002_hdr (R002_geoms.getD 119 default) R002_c119 = true)
    (h120 : cellOK R002_hdr (R002_geoms.getD 120 default) R002_c120 = true)
    (h121 : cellOK R002_hdr (R002_geoms.getD 121 default) R002_c121 = true)
    (h122 : cellOK R002_hdr (R002_geoms.getD 122 default) R002_c122 = true)
    (h123 : cellOK R002_hdr (R002_geoms.getD 123 default) R002_c123 = true)
    (h124 : cellOK R002_hdr (R002_geoms.getD 124 default) R002_c124 = true)
    (h125 : cellOK R002_hdr (R002_geoms.getD 125 default) R002_c125 = true)
    (h126 : cellOK R002_hdr (R002_geoms.getD 126 default) R002_c126 = true)
    (h127 : cellOK R002_hdr (R002_geoms.getD 127 default) R002_c127 = true)
    (h128 : cellOK R002_hdr (R002_geoms.getD 128 default) R002_c128 = true)
    (h129 : cellOK R002_hdr (R002_geoms.getD 129 default) R002_c129 = true)
    (h130 : cellOK R002_hdr (R002_geoms.getD 130 default) R002_c130 = true)
    (h131 : cellOK R002_hdr (R002_geoms.getD 131 default) R002_c131 = true)
    (h132 : cellOK R002_hdr (R002_geoms.getD 132 default) R002_c132 = true)
    (h133 : cellOK R002_hdr (R002_geoms.getD 133 default) R002_c133 = true)
    (h134 : cellOK R002_hdr (R002_geoms.getD 134 default) R002_c134 = true)
    (h135 : cellOK R002_hdr (R002_geoms.getD 135 default) R002_c135 = true)
    (h136 : cellOK R002_hdr (R002_geoms.getD 136 default) R002_c136 = true)
    (h137 : cellOK R002_hdr (R002_geoms.getD 137 default) R002_c137 = true)
    (h138 : cellOK R002_hdr (R002_geoms.getD 138 default) R002_c138 = true)
    (h139 : cellOK R002_hdr (R002_geoms.getD 139 default) R002_c139 = true)
    (h140 : cellOK R002_hdr (R002_geoms.getD 140 default) R002_c140 = true)
    (h141 : cellOK R002_hdr (R002_geoms.getD 141 default) R002_c141 = true)
    (h142 : cellOK R002_hdr (R002_geoms.getD 142 default) R002_c142 = true)
    (h143 : cellOK R002_hdr (R002_geoms.getD 143 default) R002_c143 = true)
    (h144 : cellOK R002_hdr (R002_geoms.getD 144 default) R002_c144 = true)
    (h145 : cellOK R002_hdr (R002_geoms.getD 145 default) R002_c145 = true)
    (h146 : cellOK R002_hdr (R002_geoms.getD 146 default) R002_c146 = true)
    (h147 : cellOK R002_hdr (R002_geoms.getD 147 default) R002_c147 = true)
    (h148 : cellOK R002_hdr (R002_geoms.getD 148 default) R002_c148 = true)
    (h149 : cellOK R002_hdr (R002_geoms.getD 149 default) R002_c149 = true)
    (h150 : cellOK R002_hdr (R002_geoms.getD 150 default) R002_c150 = true)
    (h151 : cellOK R002_hdr (R002_geoms.getD 151 default) R002_c151 = true)
    (h152 : cellOK R002_hdr (R002_geoms.getD 152 default) R002_c152 = true)
    (h153 : cellOK R002_hdr (R002_geoms.getD 153 default) R002_c153 = true)
    (h154 : cellOK R002_hdr (R002_geoms.getD 154 default) R002_c154 = true)
    (h155 : cellOK R002_hdr (R002_geoms.getD 155 default) R002_c155 = true)
    (h156 : cellOK R002_hdr (R002_geoms.getD 156 default) R002_c156 = true)
    (h157 : cellOK R002_hdr (R002_geoms.getD 157 default) R002_c157 = true)
    (h158 : cellOK R002_hdr (R002_geoms.getD 158 default) R002_c158 = true)
    (h159 : cellOK R002_hdr (R002_geoms.getD 159 default) R002_c159 = true)
    (h160 : cellOK R002_hdr (R002_geoms.getD 160 default) R002_c160 = true)
    (h161 : cellOK R002_hdr (R002_geoms.getD 161 default) R002_c161 = true)
    (h162 : cellOK R002_hdr (R002_geoms.getD 162 default) R002_c162 = true)
    (h163 : cellOK R002_hdr (R002_geoms.getD 163 default) R002_c163 = true)
    (h164 : cellOK R002_hdr (R002_geoms.getD 164 default) R002_c164 = true)
    (h165 : cellOK R002_hdr (R002_geoms.getD 165 default) R002_c165 = true)
    (h166 : cellOK R002_hdr (R002_geoms.getD 166 default) R002_c166 = true) :
    walkCT R002_hdr R002_tree (root R002_hdr) = some R002_geoms ∧
    R002_cells.length = R002_geoms.length ∧
    ∀ i < R002_geoms.length,
      cellOK R002_hdr (R002_geoms.getD i default) (R002_cells.getD i default) = true := by
  have checked : CertifiedCells R002_hdr R002_geoms R002_cells := by
    exact ⟨
      h000,
      h001,
      h002,
      h003,
      h004,
      h005,
      h006,
      h007,
      h008,
      h009,
      h010,
      h011,
      h012,
      h013,
      h014,
      h015,
      h016,
      h017,
      h018,
      h019,
      h020,
      h021,
      h022,
      h023,
      h024,
      h025,
      h026,
      h027,
      h028,
      h029,
      h030,
      h031,
      h032,
      h033,
      h034,
      h035,
      h036,
      h037,
      h038,
      h039,
      h040,
      h041,
      h042,
      h043,
      h044,
      h045,
      h046,
      h047,
      h048,
      h049,
      h050,
      h051,
      h052,
      h053,
      h054,
      h055,
      h056,
      h057,
      h058,
      h059,
      h060,
      h061,
      h062,
      h063,
      h064,
      h065,
      h066,
      h067,
      h068,
      h069,
      h070,
      h071,
      h072,
      h073,
      h074,
      h075,
      h076,
      h077,
      h078,
      h079,
      h080,
      h081,
      h082,
      h083,
      h084,
      h085,
      h086,
      h087,
      h088,
      h089,
      h090,
      h091,
      h092,
      h093,
      h094,
      h095,
      h096,
      h097,
      h098,
      h099,
      h100,
      h101,
      h102,
      h103,
      h104,
      h105,
      h106,
      h107,
      h108,
      h109,
      h110,
      h111,
      h112,
      h113,
      h114,
      h115,
      h116,
      h117,
      h118,
      h119,
      h120,
      h121,
      h122,
      h123,
      h124,
      h125,
      h126,
      h127,
      h128,
      h129,
      h130,
      h131,
      h132,
      h133,
      h134,
      h135,
      h136,
      h137,
      h138,
      h139,
      h140,
      h141,
      h142,
      h143,
      h144,
      h145,
      h146,
      h147,
      h148,
      h149,
      h150,
      h151,
      h152,
      h153,
      h154,
      h155,
      h156,
      h157,
      h158,
      h159,
      h160,
      h161,
      h162,
      h163,
      h164,
      h165,
      h166,
      True.intro⟩
  exact ⟨R002_walkCT_eq, R002_cells_length, fun _ hi => checked.getD hi⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The checked partition lists exactly the geometries with indexed numeric certificates. -/
theorem R002_leaf_set :
    walkCT R002_hdr R002_tree (root R002_hdr) = some R002_geoms ∧
    R002_cells.length = R002_geoms.length ∧
    ∀ i < R002_geoms.length,
      cellOK R002_hdr (R002_geoms.getD i default) (R002_cells.getD i default) = true :=
  R002_leaf_set_of_checks
    R002_c0_ok
    R002_c1_ok
    R002_c2_ok
    R002_c3_ok
    R002_c4_ok
    R002_c5_ok
    R002_c6_ok
    R002_c7_ok
    R002_c8_ok
    R002_c9_ok
    R002_c10_ok
    R002_c11_ok
    R002_c12_ok
    R002_c13_ok
    R002_c14_ok
    R002_c15_ok
    R002_c16_ok
    R002_c17_ok
    R002_c18_ok
    R002_c19_ok
    R002_c20_ok
    R002_c21_ok
    R002_c22_ok
    R002_c23_ok
    R002_c24_ok
    R002_c25_ok
    R002_c26_ok
    R002_c27_ok
    R002_c28_ok
    R002_c29_ok
    R002_c30_ok
    R002_c31_ok
    R002_c32_ok
    R002_c33_ok
    R002_c34_ok
    R002_c35_ok
    R002_c36_ok
    R002_c37_ok
    R002_c38_ok
    R002_c39_ok
    R002_c40_ok
    R002_c41_ok
    R002_c42_ok
    R002_c43_ok
    R002_c44_ok
    R002_c45_ok
    R002_c46_ok
    R002_c47_ok
    R002_c48_ok
    R002_c49_ok
    R002_c50_ok
    R002_c51_ok
    R002_c52_ok
    R002_c53_ok
    R002_c54_ok
    R002_c55_ok
    R002_c56_ok
    R002_c57_ok
    R002_c58_ok
    R002_c59_ok
    R002_c60_ok
    R002_c61_ok
    R002_c62_ok
    R002_c63_ok
    R002_c64_ok
    R002_c65_ok
    R002_c66_ok
    R002_c67_ok
    R002_c68_ok
    R002_c69_ok
    R002_c70_ok
    R002_c71_ok
    R002_c72_ok
    R002_c73_ok
    R002_c74_ok
    R002_c75_ok
    R002_c76_ok
    R002_c77_ok
    R002_c78_ok
    R002_c79_ok
    R002_c80_ok
    R002_c81_ok
    R002_c82_ok
    R002_c83_ok
    R002_c84_ok
    R002_c85_ok
    R002_c86_ok
    R002_c87_ok
    R002_c88_ok
    R002_c89_ok
    R002_c90_ok
    R002_c91_ok
    R002_c92_ok
    R002_c93_ok
    R002_c94_ok
    R002_c95_ok
    R002_c96_ok
    R002_c97_ok
    R002_c98_ok
    R002_c99_ok
    R002_c100_ok
    R002_c101_ok
    R002_c102_ok
    R002_c103_ok
    R002_c104_ok
    R002_c105_ok
    R002_c106_ok
    R002_c107_ok
    R002_c108_ok
    R002_c109_ok
    R002_c110_ok
    R002_c111_ok
    R002_c112_ok
    R002_c113_ok
    R002_c114_ok
    R002_c115_ok
    R002_c116_ok
    R002_c117_ok
    R002_c118_ok
    R002_c119_ok
    R002_c120_ok
    R002_c121_ok
    R002_c122_ok
    R002_c123_ok
    R002_c124_ok
    R002_c125_ok
    R002_c126_ok
    R002_c127_ok
    R002_c128_ok
    R002_c129_ok
    R002_c130_ok
    R002_c131_ok
    R002_c132_ok
    R002_c133_ok
    R002_c134_ok
    R002_c135_ok
    R002_c136_ok
    R002_c137_ok
    R002_c138_ok
    R002_c139_ok
    R002_c140_ok
    R002_c141_ok
    R002_c142_ok
    R002_c143_ok
    R002_c144_ok
    R002_c145_ok
    R002_c146_ok
    R002_c147_ok
    R002_c148_ok
    R002_c149_ok
    R002_c150_ok
    R002_c151_ok
    R002_c152_ok
    R002_c153_ok
    R002_c154_ok
    R002_c155_ok
    R002_c156_ok
    R002_c157_ok
    R002_c158_ok
    R002_c159_ok
    R002_c160_ok
    R002_c161_ok
    R002_c162_ok
    R002_c163_ok
    R002_c164_ok
    R002_c165_ok
    R002_c166_ok

theorem R002_cellOK {i : Nat} (hi : i < R002_geoms.length) :
    cellOK R002_hdr (R002_geoms.getD i default) (R002_cells.getD i default) = true :=
  R002_leaf_set.2.2 i hi

end HlawkaSchatten.BelowExponent.TC
