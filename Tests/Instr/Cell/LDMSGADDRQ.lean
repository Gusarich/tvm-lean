import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.LDMSGADDRQ

/-
LDMSGADDRQ branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/TonEnv/LdMsgAddr.lean`
    (`execInstrTonEnvLdMsgAddr`, quiet success/failure stack contracts)
  - `TvmLean/Model/Cell/Primitives.lean`
    (`Slice.skipMessageAddr`, `Slice.skipMaybeAnycast`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean`
    (`LDMSGADDR`/`LDMSGADDRQ` encode as `0xfa40`/`0xfa41`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean`
    (`0xfa40`/`0xfa41` decode to `.tonEnvOp (.ldMsgAddr false/true)`)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/tonops.cpp`
    (`exec_load_message_addr`, `util::load_msg_addr_q`,
     `skip_message_addr`, `skip_maybe_anycast`)

Branch map used for this suite (`quiet = true`):
- dispatch split: `.tonEnvOp (.ldMsgAddr _)` vs fallback to `next`;
- hard stack pre-guard (`popSlice`): underflow/type are never quiet-softened;
- parser split by MsgAddress tag (`00`, `01`, `10`, `11`) with all len/depth/payload guards;
- quiet success contract: pushes `[addr_slice, remainder_slice, -1]`;
- quiet parse-failure contract: restores original slice and pushes `0`.

Key risk areas covered:
- exact stack order/status polarity for quiet success/failure;
- broad malformed-shape coverage (`cellUnd`) across tag and anycast branches;
- decode/assembler boundary for `0xfa41` and adjacent opcodes;
- dispatch fallback behavior when handler receives non-`ldMsgAddr` instruction.

Note:
- Modern C++ (`global_version >= 10`) rejects anycast `just$1` and `addr_var$11`.
- Lean mirrors this modern behavior, so those shapes are covered as quiet-failure paths.
-/

private def ldmsgaddrqId : InstrId := { name := "LDMSGADDRQ" }

private def ldmsgaddrqInstr : Instr :=
  .tonEnvOp (.ldMsgAddr true)

private def ldmsgaddrInstr : Instr :=
  .tonEnvOp (.ldMsgAddr false)

private def mkLdmsgaddrqCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[ldmsgaddrqInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := ldmsgaddrqId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runLdmsgaddrqDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrTonEnvLdMsgAddr ldmsgaddrqInstr stack

private def runLdmsgaddrDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrTonEnvLdMsgAddr ldmsgaddrInstr stack

private def runLdmsgaddrqDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrTonEnvLdMsgAddr .add (VM.push (intV 441)) stack

private def patternedBits (n : Nat) (offset : Nat := 0) : BitString := Id.run do
  let mut out : BitString := #[]
  for i in [0:n] do
    out := out.push (((i + offset) % 2) = 1)
  out

private def addr256A : BitString := patternedBits 256

private def addr256B : BitString := patternedBits 256 1

private def extPayload9 : BitString := patternedBits 9 2

private def extPayload255 : BitString := patternedBits 255 3

private def extPayload511 : BitString := patternedBits 511 4

private def varPayload73 : BitString := patternedBits 73 5

private def varPayload255 : BitString := patternedBits 255 6

private def anycastPfx1 : BitString := patternedBits 1 1

private def anycastPfx3 : BitString := patternedBits 3 1

private def anycastPfx5 : BitString := patternedBits 5 2

private def anycastPfx30 : BitString := patternedBits 30 3

private def refLeafA : Cell := Cell.empty

private def refLeafB : Cell := Cell.mkOrdinary (natToBits 0b101 3) #[]

private def ldmsgaddrqSetGasExact : Int :=
  computeExactGasBudget ldmsgaddrqInstr

private def ldmsgaddrqSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne ldmsgaddrqInstr

private def mkAddrNoneBits : BitString :=
  natToBits 0 2

private def mkAddrExternBits (payload : BitString) : BitString :=
  natToBits 1 2 ++ natToBits payload.size 9 ++ payload

private def mkAddrExternBitsWithLen (len : Nat) (payloadBits : Nat) : BitString :=
  natToBits 1 2 ++ natToBits len 9 ++ Array.replicate payloadBits false

private def mkAddrStdBits (wc8 : Nat) (addr : BitString := addr256A) : BitString :=
  natToBits 2 2 ++ natToBits 0 1 ++ natToBits (wc8 % 256) 8 ++ addr

private def mkAddrStdAnycastBits
    (depth : Nat)
    (pfx : BitString)
    (wc8 : Nat)
    (addr : BitString := addr256A) : BitString :=
  natToBits 2 2 ++ natToBits 1 1 ++ natToBits depth 5 ++ pfx ++ natToBits (wc8 % 256) 8 ++ addr

private def mkAddrVarBits (wc32 : Nat) (addr : BitString) : BitString :=
  natToBits 3 2 ++ natToBits 0 1 ++ natToBits addr.size 9 ++ natToBits wc32 32 ++ addr

private def mkAddrVarAnycastBits
    (depth : Nat)
    (pfx : BitString)
    (wc32 : Nat)
    (addr : BitString) : BitString :=
  natToBits 3 2 ++ natToBits 1 1 ++ natToBits depth 5 ++ pfx ++ natToBits addr.size 9 ++ natToBits wc32 32 ++ addr

private def mkTruncatedStdBits (bodyBits : Nat) : BitString :=
  natToBits 2 2 ++ natToBits 0 1 ++ Array.replicate bodyBits false

private def mkAddrSlice
    (addrBits : BitString)
    (tailBits : BitString := #[])
    (refs : Array Cell := #[]) : Slice :=
  Slice.ofCell (Cell.mkOrdinary (addrBits ++ tailBits) refs)

private def consumedExternBits (payloadLen : Nat) : Nat :=
  2 + 9 + payloadLen

private def consumedStdBits : Nat :=
  2 + 1 + 8 + 256

private def consumedStdAnycastBits (depth : Nat) : Nat :=
  2 + 1 + 5 + depth + 8 + 256

private def consumedVarBits (len : Nat) : Nat :=
  2 + 1 + 9 + 32 + len

private def consumedVarAnycastBits (depth : Nat) (len : Nat) : Nat :=
  2 + 1 + 5 + depth + 9 + 32 + len

private def expectedSuccessStack (below : Array Value) (input : Slice) (consumedBits : Nat) : Array Value :=
  let rest := input.advanceBits consumedBits
  let addrCell := Slice.prefixCell input rest
  below ++ #[.slice (Slice.ofCell addrCell), .slice rest, intV (-1)]

private def expectedQuietFailStack (below : Array Value) (input : Slice) : Array Value :=
  below ++ #[.slice input, intV 0]

private def invalidPrefixShort0 : Slice :=
  mkSliceFromBits #[]

private def invalidPrefixShort1 : Slice :=
  mkSliceFromBits #[false]

private def invalidExternLenPrefixShort : Slice :=
  mkSliceFromBits (natToBits 1 2 ++ Array.replicate 8 false)

private def invalidExternLen1NoPayload : Slice :=
  mkSliceFromBits (mkAddrExternBitsWithLen 1 0)

private def invalidExternLen9PayloadShort : Slice :=
  mkSliceFromBits (mkAddrExternBitsWithLen 9 8)

private def invalidStdMissingOneBit : Slice :=
  mkSliceFromBits (mkTruncatedStdBits 263)

private def invalidStdAnycastDepth0 : Slice :=
  mkSliceFromBits (natToBits 2 2 ++ natToBits 1 1 ++ natToBits 0 5)

private def invalidStdAnycastDepth31 : Slice :=
  mkSliceFromBits (natToBits 2 2 ++ natToBits 1 1 ++ natToBits 31 5)

private def invalidStdAnycastPrefixShort : Slice :=
  mkSliceFromBits (natToBits 2 2 ++ natToBits 1 1 ++ natToBits 5 5 ++ Array.replicate 4 false)

private def invalidVarTagOnly : Slice :=
  mkSliceFromBits (natToBits 3 2)

private def invalidVarMissingLen : Slice :=
  mkSliceFromBits (natToBits 3 2 ++ natToBits 0 1)

private def invalidVarMissingWc : Slice :=
  mkSliceFromBits (natToBits 3 2 ++ natToBits 0 1 ++ natToBits 73 9)

private def invalidVarLen73NoPayload : Slice :=
  mkSliceFromBits (natToBits 3 2 ++ natToBits 0 1 ++ natToBits 73 9 ++ natToBits 0x11223344 32)

private def invalidVarAnycastDepth31 : Slice :=
  mkSliceFromBits (natToBits 3 2 ++ natToBits 1 1 ++ natToBits 31 5)

private def invalidVarAnycastPrefixShort : Slice :=
  mkSliceFromBits (natToBits 3 2 ++ natToBits 1 1 ++ natToBits 7 5 ++ Array.replicate 6 false)

private def invalidStdAnycastDepth1Full : Slice :=
  mkAddrSlice (mkAddrStdAnycastBits 1 anycastPfx1 17 addr256A)

private def invalidStdAnycastDepth30Full : Slice :=
  mkAddrSlice (mkAddrStdAnycastBits 30 anycastPfx30 99 addr256B)

private def invalidVarAnycast0Len73 : Slice :=
  mkAddrSlice (mkAddrVarBits 0x11223344 varPayload73)

private def invalidVarAnycast5Len73 : Slice :=
  mkAddrSlice (mkAddrVarAnycastBits 5 anycastPfx5 0x01020304 varPayload73)

private def invalidSlicePool : Array (String × Slice) :=
  #[
    ("prefix-short-0", invalidPrefixShort0),
    ("prefix-short-1", invalidPrefixShort1),
    ("extern-len-prefix-short", invalidExternLenPrefixShort),
    ("extern-len1-no-payload", invalidExternLen1NoPayload),
    ("extern-len9-payload-short", invalidExternLen9PayloadShort),
    ("std-missing-one-bit", invalidStdMissingOneBit),
    ("std-anycast-depth0", invalidStdAnycastDepth0),
    ("std-anycast-depth31", invalidStdAnycastDepth31),
    ("std-anycast-prefix-short", invalidStdAnycastPrefixShort),
    ("var-tag-only", invalidVarTagOnly),
    ("var-missing-len", invalidVarMissingLen),
    ("var-missing-wc", invalidVarMissingWc),
    ("var-len73-no-payload", invalidVarLen73NoPayload),
    ("var-anycast-depth31", invalidVarAnycastDepth31),
    ("var-anycast-prefix-short", invalidVarAnycastPrefixShort),
    ("std-anycast-depth1-full", invalidStdAnycastDepth1Full),
    ("std-anycast-depth30-full", invalidStdAnycastDepth30Full),
    ("var-anycast0-len73", invalidVarAnycast0Len73),
    ("var-anycast5-len73", invalidVarAnycast5Len73)
  ]

private def validSlicePool : Array (String × Slice) :=
  #[
    ("none", mkAddrSlice mkAddrNoneBits),
    ("none-tail7", mkAddrSlice mkAddrNoneBits tailBits7),
    ("extern-len9", mkAddrSlice (mkAddrExternBits extPayload9)),
    ("extern-len9-tail11", mkAddrSlice (mkAddrExternBits extPayload9) tailBits11),
    ("std-anycast0", mkAddrSlice (mkAddrStdBits 17 addr256A)),
    ("std-tail-refs", mkAddrSlice (mkAddrStdBits 7 addr256A) tailBits11 #[refLeafA, refLeafB])
  ]

private def pickSliceFromPool
    (pool : Array (String × Slice))
    (fallback : String × Slice)
    (rng : StdGen) : (String × Slice) × StdGen :=
  if pool.isEmpty then
    (fallback, rng)
  else
    let (idx, rng') := randNat rng 0 (pool.size - 1)
    match pool[idx]? with
    | some entry => (entry, rng')
    | none => (fallback, rng')

private def pickValidSlice (rng : StdGen) : (String × Slice) × StdGen :=
  pickSliceFromPool validSlicePool ("none", mkAddrSlice mkAddrNoneBits) rng

private def pickInvalidSlice (rng : StdGen) : (String × Slice) × StdGen :=
  pickSliceFromPool invalidSlicePool ("prefix-short-0", invalidPrefixShort0) rng

private def wc8Pool : Array Nat := #[0, 1, 2, 17, 127, 128, 254, 255]

private def wc32Pool : Array Nat :=
  #[0, 1, 2, 0x7fffffff, 0x80000000, 0xffffffff, 0x11223344, 0x01020304]

private def anycastDepthPool : Array Nat := #[1, 2, 3, 5, 8, 30]

private def pickWc8 (rng : StdGen) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (wc8Pool.size - 1)
  (wc8Pool[idx]!, rng')

private def pickWc32 (rng : StdGen) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (wc32Pool.size - 1)
  (wc32Pool[idx]!, rng')

private def pickAnycastDepth (rng : StdGen) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (anycastDepthPool.size - 1)
  (anycastDepthPool[idx]!, rng')

private def pickAddr256 (rng0 : StdGen) : BitString × StdGen :=
  let (offset, rng1) := randNat rng0 0 7
  (patternedBits 256 offset, rng1)

private def pickAnycastPrefix (depth : Nat) (rng0 : StdGen) : BitString × StdGen :=
  let (offset, rng1) := randNat rng0 0 7
  (patternedBits depth offset, rng1)

private def pickExternPayload (rng0 : StdGen) : BitString × StdGen :=
  let lenPool : Array Nat := #[0, 1, 2, 9, 31, 64, 255, 511]
  let (idx, rng1) := randNat rng0 0 (lenPool.size - 1)
  let len := lenPool[idx]!
  let (offset, rng2) := randNat rng1 0 7
  (patternedBits len offset, rng2)

private def pickVarPayload (rng0 : StdGen) : BitString × StdGen :=
  let lenPool : Array Nat := #[0, 1, 2, 17, 73, 255, 511]
  let (idx, rng1) := randNat rng0 0 (lenPool.size - 1)
  let len := lenPool[idx]!
  let (offset, rng2) := randNat rng1 0 7
  (patternedBits len offset, rng2)

private def pickTailBits (rng0 : StdGen) : BitString × StdGen :=
  let (width, rng1) := randNat rng0 1 16
  let maxVal : Nat := (1 <<< width) - 1
  let (v, rng2) := randNat rng1 0 maxVal
  (natToBits v width, rng2)

private def pickNotSliceValue (rng0 : StdGen) : Value × StdGen :=
  let (pick, rng1) := randNat rng0 0 2
  let v : Value :=
    if pick = 0 then .null
    else if pick = 1 then intV 73
    else .cell Cell.empty
  (v, rng1)

private def pickExternTruncatedSlice (rng0 : StdGen) : Slice × StdGen :=
  let (len, rng1) := randNat rng0 1 511
  let (payloadBits, rng2) := randNat rng1 0 (len - 1)
  (mkSliceFromBits (mkAddrExternBitsWithLen len payloadBits), rng2)

private def pickStdTruncatedSlice (rng0 : StdGen) : Slice × StdGen :=
  let (bodyBits, rng1) := randNat rng0 0 263
  (mkSliceFromBits (mkTruncatedStdBits bodyBits), rng1)

private def pickAnycastPrefixShortSlice (rng0 : StdGen) : Slice × StdGen :=
  let (depth, rng1) := randNat rng0 1 30
  let (prefixBits, rng2) := randNat rng1 0 (depth - 1)
  let bits :=
    natToBits 2 2 ++
      natToBits 1 1 ++
      natToBits depth 5 ++
      Array.replicate prefixBits false
  (mkSliceFromBits bits, rng2)

private def pickVarTruncatedSlice (rng0 : StdGen) : Slice × StdGen :=
  let (shape, rng1) := randNat rng0 0 3
  if shape = 0 then
    (invalidVarTagOnly, rng1)
  else if shape = 1 then
    (invalidVarMissingLen, rng1)
  else if shape = 2 then
    let (len, rng2) := randNat rng1 0 511
    let bits := natToBits 3 2 ++ natToBits 0 1 ++ natToBits len 9
    (mkSliceFromBits bits, rng2)
  else
    let (len, rng2) := randNat rng1 1 511
    let (payloadBits, rng3) := randNat rng2 0 (len - 1)
    let bits :=
      natToBits 3 2 ++
        natToBits 0 1 ++
        natToBits len 9 ++
        natToBits 0x11223344 32 ++
        Array.replicate payloadBits false
    (mkSliceFromBits bits, rng3)

private def genLdmsgaddrqFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 22
  if shape = 0 then
    (mkLdmsgaddrqCase "fuzz/ok/none" #[.slice (mkAddrSlice mkAddrNoneBits)], rng1)
  else if shape = 1 then
    let (tail, rng2) := pickTailBits rng1
    (mkLdmsgaddrqCase s!"fuzz/ok/none-tail-{tail.size}"
      #[.slice (mkAddrSlice mkAddrNoneBits tail)], rng2)
  else if shape = 2 then
    let (payload, rng2) := pickExternPayload rng1
    (mkLdmsgaddrqCase s!"fuzz/ok/extern/len-{payload.size}"
      #[.slice (mkAddrSlice (mkAddrExternBits payload))], rng2)
  else if shape = 3 then
    let (payload, rng2) := pickExternPayload rng1
    let (tail, rng3) := pickTailBits rng2
    (mkLdmsgaddrqCase s!"fuzz/ok/extern-tail/len-{payload.size}/tail-{tail.size}"
      #[.slice (mkAddrSlice (mkAddrExternBits payload) tail)], rng3)
  else if shape = 4 then
    let (wc, rng2) := pickWc8 rng1
    let (addr, rng3) := pickAddr256 rng2
    (mkLdmsgaddrqCase s!"fuzz/ok/std-anycast0/wc-{wc}"
      #[.slice (mkAddrSlice (mkAddrStdBits wc addr))], rng3)
  else if shape = 5 then
    let (depth, rng2) := pickAnycastDepth rng1
    let (pfx, rng3) := pickAnycastPrefix depth rng2
    let (wc, rng4) := pickWc8 rng3
    let (addr, rng5) := pickAddr256 rng4
    (mkLdmsgaddrqCase s!"fuzz/quiet-invalid/std-anycast/depth-{depth}/wc-{wc}"
      #[.slice (mkAddrSlice (mkAddrStdAnycastBits depth pfx wc addr))], rng5)
  else if shape = 6 then
    let (wc, rng2) := pickWc32 rng1
    let (addr, rng3) := pickVarPayload rng2
    (mkLdmsgaddrqCase s!"fuzz/quiet-invalid/var-anycast0/wc-{wc}/len-{addr.size}"
      #[.slice (mkAddrSlice (mkAddrVarBits wc addr))], rng3)
  else if shape = 7 then
    let (depth, rng2) := pickAnycastDepth rng1
    let (pfx, rng3) := pickAnycastPrefix depth rng2
    let (wc, rng4) := pickWc32 rng3
    let (addr, rng5) := pickVarPayload rng4
    (mkLdmsgaddrqCase s!"fuzz/quiet-invalid/var-anycast/depth-{depth}/wc-{wc}/len-{addr.size}"
      #[.slice (mkAddrSlice (mkAddrVarAnycastBits depth pfx wc addr))], rng5)
  else if shape = 8 then
    let ((label, cs), rng2) := pickValidSlice rng1
    let (noise, rng3) := pickNotSliceValue rng2
    (mkLdmsgaddrqCase s!"fuzz/ok/deep/{label}" #[noise, .slice cs], rng3)
  else if shape = 9 then
    let (bitCount, rng2) := randNat rng1 0 1
    let cs := if bitCount = 0 then invalidPrefixShort0 else invalidPrefixShort1
    (mkLdmsgaddrqCase s!"fuzz/quiet-invalid/prefix-short-{bitCount}" #[.slice cs], rng2)
  else if shape = 10 then
    let (cs, rng2) := pickExternTruncatedSlice rng1
    (mkLdmsgaddrqCase "fuzz/quiet-invalid/extern-truncated" #[.slice cs], rng2)
  else if shape = 11 then
    let (cs, rng2) := pickStdTruncatedSlice rng1
    (mkLdmsgaddrqCase "fuzz/quiet-invalid/std-truncated" #[.slice cs], rng2)
  else if shape = 12 then
    (mkLdmsgaddrqCase "fuzz/quiet-invalid/anycast-depth0" #[.slice invalidStdAnycastDepth0], rng1)
  else if shape = 13 then
    (mkLdmsgaddrqCase "fuzz/quiet-invalid/anycast-depth31" #[.slice invalidStdAnycastDepth31], rng1)
  else if shape = 14 then
    let (cs, rng2) := pickAnycastPrefixShortSlice rng1
    (mkLdmsgaddrqCase "fuzz/quiet-invalid/anycast-prefix-short" #[.slice cs], rng2)
  else if shape = 15 then
    let (cs, rng2) := pickVarTruncatedSlice rng1
    (mkLdmsgaddrqCase "fuzz/quiet-invalid/var-truncated" #[.slice cs], rng2)
  else if shape = 16 then
    (mkLdmsgaddrqCase "fuzz/quiet-invalid/var-anycast-depth31" #[.slice invalidVarAnycastDepth31], rng1)
  else if shape = 17 then
    let ((label, cs), rng2) := pickInvalidSlice rng1
    let (noise, rng3) := pickNotSliceValue rng2
    (mkLdmsgaddrqCase s!"fuzz/quiet-invalid/deep/{label}" #[noise, .slice cs], rng3)
  else if shape = 18 then
    (mkLdmsgaddrqCase "fuzz/underflow/empty" #[], rng1)
  else if shape = 19 then
    let (v, rng2) := pickNotSliceValue rng1
    (mkLdmsgaddrqCase "fuzz/type/top-not-slice" #[v], rng2)
  else if shape = 20 then
    let ((label, cs), rng2) := pickValidSlice rng1
    let (v, rng3) := pickNotSliceValue rng2
    (mkLdmsgaddrqCase s!"fuzz/type/deep-top-not-slice/{label}" #[.slice cs, v], rng3)
  else if shape = 21 then
    let ((label, cs), rng2) := pickValidSlice rng1
    (mkLdmsgaddrqCase s!"fuzz/gas/exact/{label}" #[.slice cs]
      #[.pushInt (.num ldmsgaddrqSetGasExact), .tonEnvOp .setGasLimit, ldmsgaddrqInstr], rng2)
  else
    let ((label, cs), rng2) := pickValidSlice rng1
    (mkLdmsgaddrqCase s!"fuzz/gas/exact-minus-one/{label}" #[.slice cs]
      #[.pushInt (.num ldmsgaddrqSetGasExactMinusOne), .tonEnvOp .setGasLimit, ldmsgaddrqInstr], rng2)

def suite : InstrSuite where
  id := ldmsgaddrqId
  unit := #[
    { name := "unit/direct/success-status-order-and-remainder"
      run := do
        let checks : Array (String × Slice × Nat) :=
          #[
            ("ok/none-no-tail", mkAddrSlice mkAddrNoneBits, 2),
            ("ok/none-with-tail", mkAddrSlice mkAddrNoneBits tailBits7, 2),
            ("ok/extern-len0", mkAddrSlice (mkAddrExternBits #[]), consumedExternBits 0),
            ("ok/extern-len9-with-tail", mkAddrSlice (mkAddrExternBits extPayload9) tailBits11,
              consumedExternBits extPayload9.size),
            ("ok/extern-len511", mkAddrSlice (mkAddrExternBits extPayload511), consumedExternBits extPayload511.size),
            ("ok/std-anycast0", mkAddrSlice (mkAddrStdBits 0 addr256A), consumedStdBits),
            ("ok/std-anycast0-tail", mkAddrSlice (mkAddrStdBits 255 addr256B) tailBits13, consumedStdBits),
            ("ok/std-tail-with-refs", mkAddrSlice (mkAddrStdBits 7 addr256A) tailBits11 #[refLeafA, refLeafB],
              consumedStdBits)
          ]
        for c in checks do
          let label := c.1
          let input := c.2.1
          let consumed := c.2.2
          expectOkStack label
            (runLdmsgaddrqDirect #[.slice input])
            (expectedSuccessStack #[] input consumed)

        let deepInput := mkAddrSlice (mkAddrExternBits extPayload9) tailBits11
        expectOkStack "ok/deep-stack-preserve-below"
          (runLdmsgaddrqDirect #[.cell Cell.empty, .slice deepInput])
          (expectedSuccessStack #[.cell Cell.empty] deepInput (consumedExternBits extPayload9.size)) }
    ,
    { name := "unit/direct/underflow-and-type-order"
      run := do
        expectErr "underflow/empty" (runLdmsgaddrqDirect #[]) .stkUnd
        expectErr "type/top-not-slice/null" (runLdmsgaddrqDirect #[.null]) .typeChk
        expectErr "type/top-not-slice/int" (runLdmsgaddrqDirect #[intV 1]) .typeChk
        expectErr "type/deep-top-not-slice"
          (runLdmsgaddrqDirect #[.slice (mkAddrSlice mkAddrNoneBits), .cell Cell.empty]) .typeChk }
    ,
    { name := "unit/direct/quiet-invalid-shape-status0"
      run := do
        for entry in invalidSlicePool do
          let label := entry.1
          let cs := entry.2
          expectOkStack s!"quiet-invalid/{label}"
            (runLdmsgaddrqDirect #[.slice cs])
            (expectedQuietFailStack #[] cs)

        expectOkStack "quiet-invalid/deep-stack-preserve-below"
          (runLdmsgaddrqDirect #[intV 11, .slice invalidVarAnycastDepth31])
          (expectedQuietFailStack #[intV 11] invalidVarAnycastDepth31) }
    ,
    { name := "unit/direct/nonquiet-baseline-cellund"
      run := do
        for entry in invalidSlicePool do
          let label := entry.1
          let cs := entry.2
          expectErr s!"nonquiet-invalid/{label}" (runLdmsgaddrDirect #[.slice cs]) .cellUnd }
    ,
    { name := "unit/opcode/decode-and-assembler-boundaries"
      run := do
        let quietCode ←
          match assembleCp0 [ldmsgaddrqInstr] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble quiet failed: {e}")
        if quietCode.bits = natToBits 0xfa41 16 then
          pure ()
        else
          throw (IO.userError s!"ldmsgaddrq encode mismatch: got bits {quietCode.bits}")

        let nonQuietCode ←
          match assembleCp0 [ldmsgaddrInstr] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble non-quiet failed: {e}")
        if nonQuietCode.bits = natToBits 0xfa40 16 then
          pure ()
        else
          throw (IO.userError s!"ldmsgaddr encode mismatch: got bits {nonQuietCode.bits}")

        let program : Array Instr :=
          #[ldmsgaddrqInstr, ldmsgaddrInstr, (.tonEnvOp (.parseMsgAddr true)), .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble sequence failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/ldmsgaddrq" s0 ldmsgaddrqInstr 16
        let s2 ← expectDecodeStep "decode/ldmsgaddr" s1 ldmsgaddrInstr 16
        let s3 ← expectDecodeStep "decode/parsemsgaddrq" s2 (.tonEnvOp (.parseMsgAddr true)) 16
        let s4 ← expectDecodeStep "decode/tail-add" s3 .add 8
        if s4.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/end: expected exhausted slice, got {s4.bitsRemaining} bits remaining") }
    ,
    { name := "unit/dispatch/non-tonenv-falls-through"
      run := do
        expectOkStack "dispatch/fallback"
          (runLdmsgaddrqDispatchFallback #[.null])
          #[.null, intV 441] }
  ]
  oracle := #[
    mkLdmsgaddrqCase "ok/none-no-tail" #[.slice (mkAddrSlice mkAddrNoneBits)],
    mkLdmsgaddrqCase "ok/none-tail7" #[.slice (mkAddrSlice mkAddrNoneBits tailBits7)],
    mkLdmsgaddrqCase "ok/none-tail13" #[.slice (mkAddrSlice mkAddrNoneBits tailBits13)],
    mkLdmsgaddrqCase "ok/extern-len0" #[.slice (mkAddrSlice (mkAddrExternBits #[]))],
    mkLdmsgaddrqCase "ok/extern-len1" #[.slice (mkAddrSlice (mkAddrExternBits (patternedBits 1 2)))],
    mkLdmsgaddrqCase "ok/extern-len9-tail11" #[.slice (mkAddrSlice (mkAddrExternBits extPayload9) tailBits11)],
    mkLdmsgaddrqCase "ok/extern-len255" #[.slice (mkAddrSlice (mkAddrExternBits extPayload255))],
    mkLdmsgaddrqCase "ok/extern-len511" #[.slice (mkAddrSlice (mkAddrExternBits extPayload511))],
    mkLdmsgaddrqCase "ok/std-anycast0-wc0" #[.slice (mkAddrSlice (mkAddrStdBits 0 addr256A))],
    mkLdmsgaddrqCase "ok/std-anycast0-wc255-tail"
      #[.slice (mkAddrSlice (mkAddrStdBits 255 addr256B) tailBits13)],
    mkLdmsgaddrqCase "quiet-invalid/std-anycast-depth1"
      #[.slice (mkAddrSlice (mkAddrStdAnycastBits 1 anycastPfx1 17 addr256A))],
    mkLdmsgaddrqCase "quiet-invalid/std-anycast-depth30-tail"
      #[.slice (mkAddrSlice (mkAddrStdAnycastBits 30 anycastPfx30 99 addr256B) tailBits7)],
    mkLdmsgaddrqCase "quiet-invalid/var-anycast0-len0"
      #[.slice (mkAddrSlice (mkAddrVarBits 0x01020304 #[]))],
    mkLdmsgaddrqCase "quiet-invalid/var-anycast0-len73-tail"
      #[.slice (mkAddrSlice (mkAddrVarBits 0x11223344 varPayload73) tailBits7)],
    mkLdmsgaddrqCase "quiet-invalid/var-anycast5-len73"
      #[.slice (mkAddrSlice (mkAddrVarAnycastBits 5 anycastPfx5 0x01020304 varPayload73))],
    mkLdmsgaddrqCase "quiet-invalid/var-anycast3-len255-tail"
      #[.slice (mkAddrSlice (mkAddrVarAnycastBits 3 anycastPfx3 0x7fffffff varPayload255) tailBits11)],
    mkLdmsgaddrqCase "ok/deep-stack-null"
      #[.null, .slice (mkAddrSlice (mkAddrExternBits extPayload9) tailBits11)],
    mkLdmsgaddrqCase "ok/deep-stack-cell"
      #[.cell Cell.empty, .slice (mkAddrSlice (mkAddrStdBits 77 addr256A))],
    mkLdmsgaddrqCase "ok/std-tail-with-refs"
      #[.slice (mkAddrSlice (mkAddrStdBits 7 addr256A) tailBits11 #[refLeafA, refLeafB])],

    mkLdmsgaddrqCase "quiet-invalid/prefix-short-0" #[.slice invalidPrefixShort0],
    mkLdmsgaddrqCase "quiet-invalid/prefix-short-1" #[.slice invalidPrefixShort1],
    mkLdmsgaddrqCase "quiet-invalid/extern-len-prefix-short" #[.slice invalidExternLenPrefixShort],
    mkLdmsgaddrqCase "quiet-invalid/extern-len1-no-payload" #[.slice invalidExternLen1NoPayload],
    mkLdmsgaddrqCase "quiet-invalid/extern-len9-payload-short" #[.slice invalidExternLen9PayloadShort],
    mkLdmsgaddrqCase "quiet-invalid/std-missing-one-bit" #[.slice invalidStdMissingOneBit],
    mkLdmsgaddrqCase "quiet-invalid/std-anycast-depth0" #[.slice invalidStdAnycastDepth0],
    mkLdmsgaddrqCase "quiet-invalid/std-anycast-depth31" #[.slice invalidStdAnycastDepth31],
    mkLdmsgaddrqCase "quiet-invalid/std-anycast-prefix-short" #[.slice invalidStdAnycastPrefixShort],
    mkLdmsgaddrqCase "quiet-invalid/var-tag-only" #[.slice invalidVarTagOnly],
    mkLdmsgaddrqCase "quiet-invalid/var-missing-len" #[.slice invalidVarMissingLen],
    mkLdmsgaddrqCase "quiet-invalid/var-missing-wc" #[.slice invalidVarMissingWc],
    mkLdmsgaddrqCase "quiet-invalid/var-len73-no-payload" #[.slice invalidVarLen73NoPayload],
    mkLdmsgaddrqCase "quiet-invalid/var-anycast-depth31" #[.slice invalidVarAnycastDepth31],
    mkLdmsgaddrqCase "quiet-invalid/var-anycast-prefix-short" #[.slice invalidVarAnycastPrefixShort],
    mkLdmsgaddrqCase "quiet-invalid/deep-stack" #[intV 7, .slice invalidVarAnycastDepth31],

    mkLdmsgaddrqCase "underflow/empty" #[],
    mkLdmsgaddrqCase "type/top-not-slice" #[.null],
    mkLdmsgaddrqCase "type/deep-top-not-slice" #[.slice (mkAddrSlice mkAddrNoneBits), .cell Cell.empty],

    mkLdmsgaddrqCase "gas/exact-cost-succeeds" #[.slice (mkAddrSlice (mkAddrExternBits extPayload9))]
      #[.pushInt (.num ldmsgaddrqSetGasExact), .tonEnvOp .setGasLimit, ldmsgaddrqInstr],
    mkLdmsgaddrqCase "gas/exact-minus-one-out-of-gas" #[.slice (mkAddrSlice (mkAddrExternBits extPayload9))]
      #[.pushInt (.num ldmsgaddrqSetGasExactMinusOne), .tonEnvOp .setGasLimit, ldmsgaddrqInstr]
  ]
  fuzz := #[
    { seed := 2026021026
      count := 360
      gen := genLdmsgaddrqFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.LDMSGADDRQ
