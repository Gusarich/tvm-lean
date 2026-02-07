import TvmLean.Model.Host.Host
import TvmLean.Native.Extern.Crypto
import TvmLean.Native.Extern.Hash

namespace TvmLean

def nativeHost : Host where
  ed25519Verify := ed25519VerifyNative
  secp256k1Ecrecover := secp256k1EcrecoverNative
  secp256k1XonlyPubkeyTweakAdd := secp256k1XonlyPubkeyTweakAddNative
  p256Verify := p256VerifyNative
  rist255FromHash := rist255FromHashNative
  rist255IsValidPoint := rist255IsValidPointNative
  rist255AddBytes := rist255AddBytesNative
  rist255SubBytes := rist255SubBytesNative
  rist255MulBytes := rist255MulBytesNative
  rist255MulBaseBytes := rist255MulBaseBytesNative
  blsVerify := blsVerifyNative
  blsAggregate := blsAggregateNative
  blsFastAggregateVerify := blsFastAggregateVerifyNative
  blsAggregateVerify := blsAggregateVerifyNative
  blsG1AddBytes := blsG1AddBytesNative
  blsG1SubBytes := blsG1SubBytesNative
  blsG1NegBytes := blsG1NegBytesNative
  blsG1MulBytes := blsG1MulBytesNative
  blsG1MultiExpBytes := blsG1MultiExpBytesNative
  blsG1ZeroBytes := blsG1ZeroBytesNative
  blsMapToG1Bytes := blsMapToG1BytesNative
  blsG1InGroup := blsG1InGroupNative
  blsG1IsZero := blsG1IsZeroNative
  blsG2AddBytes := blsG2AddBytesNative
  blsG2SubBytes := blsG2SubBytesNative
  blsG2NegBytes := blsG2NegBytesNative
  blsG2MulBytes := blsG2MulBytesNative
  blsG2MultiExpBytes := blsG2MultiExpBytesNative
  blsG2ZeroBytes := blsG2ZeroBytesNative
  blsMapToG2Bytes := blsMapToG2BytesNative
  blsG2InGroup := blsG2InGroupNative
  blsG2IsZero := blsG2IsZeroNative
  blsPairing := blsPairingNative
  hashSha256 := hashSha256Native
  hashSha512 := hashSha512Native
  hashBlake2b := hashBlake2bNative
  hashKeccak256 := hashKeccak256Native
  hashKeccak512 := hashKeccak512Native

end TvmLean
