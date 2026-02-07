import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Crypto.SECP256K1_XONLY_PUBKEY_TWEAK_ADD

def suite : InstrSuite where
  id := { name := "SECP256K1_XONLY_PUBKEY_TWEAK_ADD" }
  unit := #[]
  oracle := #[]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Crypto.SECP256K1_XONLY_PUBKEY_TWEAK_ADD
