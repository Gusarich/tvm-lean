import TvmLean.Model

namespace TvmLean

@[extern "tvmlean_hash_sha256"]
opaque hashSha256Native (data : ByteArray) : ByteArray

@[extern "tvmlean_hash_sha512"]
opaque hashSha512Native (data : ByteArray) : ByteArray

@[extern "tvmlean_hash_blake2b"]
opaque hashBlake2bNative (data : ByteArray) : ByteArray

@[extern "tvmlean_hash_keccak256"]
opaque hashKeccak256Native (data : ByteArray) : ByteArray

@[extern "tvmlean_hash_keccak512"]
opaque hashKeccak512Native (data : ByteArray) : ByteArray

end TvmLean
