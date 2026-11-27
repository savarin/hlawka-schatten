/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G1CompactDataCore

/-! Packed signed ordinates for the compact G1 integer corner check. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G1CompactData

def compactOrdinateBias : Nat := 2044420
def compactOrdinateBits : Nat := 33
def packedLowerOrdinates : Nat := 0x1c6f6c9f0dddfc44b6c28b55334b41baa39ab9cef0c7f6ecc4e14f4b686f54ff9cd702e7a42b2e86cf3d6e3d4572a2d42f1d476164dd9ebab999cce99f83a53e9853d20607fd18b74fb36c3645a4a208ae3988fb3b5826791f323c3a5823525c1444158d8036f6467c2668331c9a40bd7dd22550b6ccb1a95768e702a9be331dd3e842bba97ae178c481ea1d1223c04599038dfb627ac28b6139f1a1f19b4a6defccd2cfe8e602a3b4f2cf2cb0494f250ff09bac0a4a480ca63e213701240f3ec11406f695322329c03f716d91e9b8a3e26a2048e1029a201b7cea0dfda31986047349028c28b8610ec39c206dad0a602b041d481025827e05b0498e01d06f41807bab9d401511c6200000000

end HlawkaSchatten.BelowExponent.G1CompactData
