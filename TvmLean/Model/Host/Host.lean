import Std

namespace TvmLean

/-- Host hooks used by semantics for crypto/hash/external environment operations. -/
structure Host where
  ed25519Verify : ByteArray → ByteArray → ByteArray → Bool
  secp256k1Ecrecover : ByteArray → ByteArray → ByteArray
  secp256k1XonlyPubkeyTweakAdd : ByteArray → ByteArray → ByteArray
  p256Verify : ByteArray → ByteArray → ByteArray → Bool
  rist255FromHash : ByteArray → ByteArray → ByteArray
  rist255IsValidPoint : ByteArray → Bool
  rist255AddBytes : ByteArray → ByteArray → ByteArray
  rist255SubBytes : ByteArray → ByteArray → ByteArray
  rist255MulBytes : ByteArray → ByteArray → ByteArray
  rist255MulBaseBytes : ByteArray → ByteArray
  blsVerify : ByteArray → ByteArray → ByteArray → Bool
  blsAggregate : Array ByteArray → ByteArray
  blsFastAggregateVerify : Array ByteArray → ByteArray → ByteArray → Bool
  blsAggregateVerify : Array ByteArray → Array ByteArray → ByteArray → Bool
  blsG1AddBytes : ByteArray → ByteArray → ByteArray
  blsG1SubBytes : ByteArray → ByteArray → ByteArray
  blsG1NegBytes : ByteArray → ByteArray
  blsG1MulBytes : ByteArray → ByteArray → ByteArray
  blsG1MultiExpBytes : Array ByteArray → Array ByteArray → ByteArray
  blsG1ZeroBytes : Unit → ByteArray
  blsMapToG1Bytes : ByteArray → ByteArray
  blsG1InGroup : ByteArray → Bool
  blsG1IsZero : ByteArray → Bool
  blsG2AddBytes : ByteArray → ByteArray → ByteArray
  blsG2SubBytes : ByteArray → ByteArray → ByteArray
  blsG2NegBytes : ByteArray → ByteArray
  blsG2MulBytes : ByteArray → ByteArray → ByteArray
  blsG2MultiExpBytes : Array ByteArray → Array ByteArray → ByteArray
  blsG2ZeroBytes : Unit → ByteArray
  blsMapToG2Bytes : ByteArray → ByteArray
  blsG2InGroup : ByteArray → Bool
  blsG2IsZero : ByteArray → Bool
  blsPairing : Array ByteArray → Array ByteArray → UInt8
  hashSha256 : ByteArray → ByteArray
  hashSha512 : ByteArray → ByteArray
  hashBlake2b : ByteArray → ByteArray
  hashKeccak256 : ByteArray → ByteArray
  hashKeccak512 : ByteArray → ByteArray

end TvmLean
