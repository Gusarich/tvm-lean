import TvmLean.Model

namespace TvmLean

@[extern "tvmlean_ed25519_verify"]
opaque ed25519VerifyNative (msg pk sig : ByteArray) : Bool

@[extern "tvmlean_secp256k1_ecrecover"]
opaque secp256k1EcrecoverNative (hash sig : ByteArray) : ByteArray

@[extern "tvmlean_secp256k1_xonly_pubkey_tweak_add"]
opaque secp256k1XonlyPubkeyTweakAddNative (key tweak : ByteArray) : ByteArray

@[extern "tvmlean_p256_verify"]
opaque p256VerifyNative (data pk sig : ByteArray) : Bool

@[extern "tvmlean_rist255_from_hash"]
opaque rist255FromHashNative (x1 x2 : ByteArray) : ByteArray

@[extern "tvmlean_rist255_is_valid_point"]
opaque rist255IsValidPointNative (x : ByteArray) : Bool

@[extern "tvmlean_rist255_add"]
opaque rist255AddBytesNative (x y : ByteArray) : ByteArray

@[extern "tvmlean_rist255_sub"]
opaque rist255SubBytesNative (x y : ByteArray) : ByteArray

@[extern "tvmlean_rist255_mul"]
opaque rist255MulBytesNative (nLe x : ByteArray) : ByteArray

@[extern "tvmlean_rist255_mul_base"]
opaque rist255MulBaseBytesNative (nLe : ByteArray) : ByteArray

@[extern "tvmlean_bls_verify"]
opaque blsVerifyNative (pub msg sig : ByteArray) : Bool

@[extern "tvmlean_bls_aggregate"]
opaque blsAggregateNative (sigs : Array ByteArray) : ByteArray

@[extern "tvmlean_bls_fast_aggregate_verify"]
opaque blsFastAggregateVerifyNative (pubs : Array ByteArray) (msg sig : ByteArray) : Bool

@[extern "tvmlean_bls_aggregate_verify"]
opaque blsAggregateVerifyNative (pubs msgs : Array ByteArray) (sig : ByteArray) : Bool

@[extern "tvmlean_bls_g1_add"]
opaque blsG1AddBytesNative (a b : ByteArray) : ByteArray

@[extern "tvmlean_bls_g1_sub"]
opaque blsG1SubBytesNative (a b : ByteArray) : ByteArray

@[extern "tvmlean_bls_g1_neg"]
opaque blsG1NegBytesNative (a : ByteArray) : ByteArray

@[extern "tvmlean_bls_g1_mul"]
opaque blsG1MulBytesNative (p x : ByteArray) : ByteArray

@[extern "tvmlean_bls_g1_multiexp"]
opaque blsG1MultiExpBytesNative (ps xs : Array ByteArray) : ByteArray

@[extern "tvmlean_bls_g1_zero"]
opaque blsG1ZeroBytesNative (_ : Unit) : ByteArray

@[extern "tvmlean_bls_map_to_g1"]
opaque blsMapToG1BytesNative (a : ByteArray) : ByteArray

@[extern "tvmlean_bls_g1_in_group"]
opaque blsG1InGroupNative (a : ByteArray) : Bool

@[extern "tvmlean_bls_g1_is_zero"]
opaque blsG1IsZeroNative (a : ByteArray) : Bool

@[extern "tvmlean_bls_g2_add"]
opaque blsG2AddBytesNative (a b : ByteArray) : ByteArray

@[extern "tvmlean_bls_g2_sub"]
opaque blsG2SubBytesNative (a b : ByteArray) : ByteArray

@[extern "tvmlean_bls_g2_neg"]
opaque blsG2NegBytesNative (a : ByteArray) : ByteArray

@[extern "tvmlean_bls_g2_mul"]
opaque blsG2MulBytesNative (p x : ByteArray) : ByteArray

@[extern "tvmlean_bls_g2_multiexp"]
opaque blsG2MultiExpBytesNative (ps xs : Array ByteArray) : ByteArray

@[extern "tvmlean_bls_g2_zero"]
opaque blsG2ZeroBytesNative (_ : Unit) : ByteArray

@[extern "tvmlean_bls_map_to_g2"]
opaque blsMapToG2BytesNative (a : ByteArray) : ByteArray

@[extern "tvmlean_bls_g2_in_group"]
opaque blsG2InGroupNative (a : ByteArray) : Bool

@[extern "tvmlean_bls_g2_is_zero"]
opaque blsG2IsZeroNative (a : ByteArray) : Bool

@[extern "tvmlean_bls_pairing"]
opaque blsPairingNative (p1s p2s : Array ByteArray) : UInt8

end TvmLean
