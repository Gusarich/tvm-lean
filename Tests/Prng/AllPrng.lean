import Tests.Config.Util

open TvmLean Tests
open Tests.Config

namespace Tests.Prng

def vInt (n : Int) : Value := .int (.num n)

def mkParamsWithSeed (seed : Int) : Array Value :=
  mkParamsWith 6 (vInt seed)

def getSeedFromC7 (c7 : Array Value) : Except String Int := do
  if 0 < c7.size then
    match c7[0]! with
    | .tuple params =>
        if 6 < params.size then
          match params[6]! with
          | .int (.num n) => return n
          | .int .nan => throw "seed is NaN"
          | _ => throw "seed not int"
        else
          throw "params too short"
    | _ => throw "c7[0] not tuple"
  else
    throw "c7 empty"

def sha512Step (seed : Int) : Except String (Int × Int) := do
  if seed < 0 ∨ seed ≥ intPow2 256 then
    throw "seed out of range"
  let seedBytes := natToBytesBEFixed seed.toNat 32
  let digest := sha512Digest seedBytes
  let newSeedNat := bytesToNatBE (digest.extract 0 32)
  let randNat := bytesToNatBE (digest.extract 32 64)
  return (Int.ofNat newSeedNat, Int.ofNat randNat)

def sha256Mix (seed x : Int) : Except String Int := do
  if seed < 0 ∨ seed ≥ intPow2 256 then throw "seed out of range"
  if x < 0 ∨ x ≥ intPow2 256 then throw "x out of range"
  let seedBytes := natToBytesBEFixed seed.toNat 32
  let xBytes := natToBytesBEFixed x.toNat 32
  let digest := sha256Digest (seedBytes ++ xBytes)
  return Int.ofNat (bytesToNatBE digest)

def testPrng : IO Unit := do
  -- RANDU256: deterministic based on seed in c7 params[6].
  let seed0 : Int := 123
  let (newSeed0, rand0) ←
    match sha512Step seed0 with
    | .ok v => pure v
    | .error e => throw (IO.userError s!"sha512Step failed: {e}")
  let (code0, st0) ← runInstrWithC7 (.tonEnvOp .randu256) (mkC7Params (mkParamsWithSeed seed0))
  assert (code0 == -1) s!"randu256: unexpected exitCode={code0}"
  assert (st0.stack.size == 1) s!"randu256: unexpected stack size={st0.stack.size}"
  assert (st0.stack[0]! == vInt rand0) s!"randu256: expected {rand0}, got {st0.stack[0]!.pretty}"
  let seedAfter0 ←
    match getSeedFromC7 st0.regs.c7 with
    | .ok s => pure s
    | .error e => throw (IO.userError s!"randu256: failed reading seed from c7: {e}")
  assert (seedAfter0 == newSeed0) s!"randu256: expected new seed {newSeed0}, got {seedAfter0}"

  -- RAND: pops x, pushes floor((x*rand)/2^256), and updates seed.
  let x : Int := 42
  let expectedRandRes : Int := floorDivPow2 (x * rand0) 256
  let (code1, st1) ← runInstrWithC7 (.tonEnvOp .rand) (mkC7Params (mkParamsWithSeed seed0)) (stack := #[vInt x])
  assert (code1 == -1) s!"rand: unexpected exitCode={code1}"
  assert (st1.stack.size == 1) s!"rand: unexpected stack size={st1.stack.size}"
  assert (st1.stack[0]! == vInt expectedRandRes) s!"rand: expected {expectedRandRes}, got {st1.stack[0]!.pretty}"
  let seedAfter1 ←
    match getSeedFromC7 st1.regs.c7 with
    | .ok s => pure s
    | .error e => throw (IO.userError s!"rand: failed reading seed from c7: {e}")
  assert (seedAfter1 == newSeed0) s!"rand: expected new seed {newSeed0}, got {seedAfter1}"

  -- SETRAND: sets seed to x (no mixing).
  let seedSet : Int := 999
  let (code2, st2) ←
    runInstrWithC7 (.tonEnvOp (.setRand false)) (mkC7Params (mkParamsWithSeed seed0)) (stack := #[vInt seedSet])
  assert (code2 == -1) s!"setrand: unexpected exitCode={code2}"
  let seedAfter2 ←
    match getSeedFromC7 st2.regs.c7 with
    | .ok s => pure s
    | .error e => throw (IO.userError s!"setrand: failed reading seed from c7: {e}")
  assert (seedAfter2 == seedSet) s!"setrand: expected seed {seedSet}, got {seedAfter2}"

  -- ADDRAND: mixes seed := sha256(seed||x).
  let xMix : Int := 456
  let expectedMix ←
    match sha256Mix seed0 xMix with
    | .ok s => pure s
    | .error e => throw (IO.userError s!"sha256Mix failed: {e}")
  let (code3, st3) ←
    runInstrWithC7 (.tonEnvOp (.setRand true)) (mkC7Params (mkParamsWithSeed seed0)) (stack := #[vInt xMix])
  assert (code3 == -1) s!"addrand: unexpected exitCode={code3}"
  let seedAfter3 ←
    match getSeedFromC7 st3.regs.c7 with
    | .ok s => pure s
    | .error e => throw (IO.userError s!"addrand: failed reading seed from c7: {e}")
  assert (seedAfter3 == expectedMix) s!"addrand: expected mixed seed {expectedMix}, got {seedAfter3}"

  -- Range errors.
  let (code4, _st4) ←
    runInstrWithC7 (.tonEnvOp (.setRand false)) (mkC7Params (mkParamsWithSeed seed0)) (stack := #[vInt (-1)])
  assert (code4 == (~~~ Excno.rangeChk.toInt)) s!"setrand(-1): expected rangeChk, got exitCode={code4}"

initialize
  Tests.registerTest "prng/all" testPrng
  Tests.registerRoundtrip (.tonEnvOp .randu256)
  Tests.registerRoundtrip (.tonEnvOp .rand)
  Tests.registerRoundtrip (.tonEnvOp (.setRand false))
  Tests.registerRoundtrip (.tonEnvOp (.setRand true))

end Tests.Prng
