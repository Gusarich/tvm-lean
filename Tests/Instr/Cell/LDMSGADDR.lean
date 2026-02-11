import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.LDMSGADDR

/-
LDMSGADDR branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/TonEnv/LdMsgAddr.lean`
  - `TvmLean/Model/Cell/Primitives.lean` (`Slice.skipMessageAddr`, `Slice.skipMaybeAnycast`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`LDMSGADDR` encode: `0xfa40`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xfa40` decode to `.tonEnvOp (.ldMsgAddr false)`)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/tonops.cpp`
    (`skip_message_addr`, `util::load_msg_addr_q`, `exec_load_message_addr`)

Branch map used for this suite:
- Lean LDMSGADDR path: 7 branch sites / 14 terminal outcomes
  (opcode guard; pop-slice underflow/type; msg-addr tag split {00,01,10,11};
   maybe-anycast split; len/depth/payload-availability guards; success path pushes
   loaded-address slice then remainder slice).
- C++ LDMSGADDR path: 6 branch sites / 10 aligned outcomes in `runvmx` context.

Key risk areas covered here:
- stack ordering (`addr` pushed before remainder);
- strict underflow/type ordering from `popSlice`;
- modern-TVМ gates (`global_version >= 10`) where anycast and `addr_var` are rejected;
- malformed-shape `cellUnd` paths (short prefixes, short payloads, invalid anycast encodings);
- decode/asm opcode boundary (`0xfa40`) and dispatch fallback.
-/

private def ldmsgaddrId : InstrId := { name := "LDMSGADDR" }

private def ldmsgaddrInstr : Instr :=
  .tonEnvOp (.ldMsgAddr false)

private def mkLdmsgaddrCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[ldmsgaddrInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := ldmsgaddrId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runLdmsgaddrDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrTonEnvLdMsgAddr ldmsgaddrInstr stack

private def runLdmsgaddrDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrTonEnvLdMsgAddr .add (VM.push (intV 440)) stack

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

private def anycastPfx3 : BitString := patternedBits 3 1

private def anycastPfx5 : BitString := patternedBits 5 2

private def ldmsgaddrSetGasExact : Int :=
  computeExactGasBudget ldmsgaddrInstr

private def ldmsgaddrSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne ldmsgaddrInstr

private def mkAddrNoneBits : BitString :=
  natToBits 0 2

private def mkAddrExternBits (payload : BitString) : BitString :=
  natToBits 1 2 ++ natToBits payload.size 9 ++ payload

private def mkAddrExternBitsWithLen (len : Nat) (payloadBits : Nat) : BitString :=
  natToBits 1 2 ++ natToBits len 9 ++ Array.replicate payloadBits false

private def mkAddrStdBits (wc8 : Nat) (addr : BitString := addr256A) : BitString :=
  natToBits 2 2 ++ natToBits 0 1 ++ natToBits wc8 8 ++ addr

private def mkAddrStdAnycastBits
    (depth : Nat)
    (pfx : BitString)
    (wc8 : Nat)
    (addr : BitString := addr256A) : BitString :=
  natToBits 2 2 ++ natToBits 1 1 ++ natToBits depth 5 ++ pfx ++ natToBits wc8 8 ++ addr

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

private def mkAddrSlice (addrBits : BitString) (tailBits : BitString := #[]) : Slice :=
  mkSliceFromBits (addrBits ++ tailBits)

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
  below ++ #[.slice (Slice.ofCell addrCell), .slice rest]

private def pickExternPayload (rng0 : StdGen) : BitString × StdGen :=
  let lenPool : Array Nat := #[0, 1, 2, 9, 31, 64, 255, 511]
  let (idx, rng1) := randNat rng0 0 (lenPool.size - 1)
  let len := lenPool[idx]!
  let (offset, rng2) := randNat rng1 0 7
  (patternedBits len offset, rng2)

private def pickTailBits (rng0 : StdGen) : BitString × StdGen :=
  let (width, rng1) := randNat rng0 1 14
  let maxVal : Nat := (1 <<< width) - 1
  let (v, rng2) := randNat rng1 0 maxVal
  (natToBits v width, rng2)

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
  let (shape, rng1) := randNat rng0 0 2
  if shape = 0 then
    (mkSliceFromBits (natToBits 3 2), rng1)
  else if shape = 1 then
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

private def genLdmsgaddrFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 16
  if shape = 0 then
    (mkLdmsgaddrCase "fuzz/ok/none" #[.slice (mkAddrSlice mkAddrNoneBits)], rng1)
  else if shape = 1 then
    let (tail, rng2) := pickTailBits rng1
    (mkLdmsgaddrCase s!"fuzz/ok/none-tail-{tail.size}" #[.slice (mkAddrSlice mkAddrNoneBits tail)], rng2)
  else if shape = 2 then
    let (payload, rng2) := pickExternPayload rng1
    (mkLdmsgaddrCase s!"fuzz/ok/extern/len-{payload.size}" #[.slice (mkAddrSlice (mkAddrExternBits payload))], rng2)
  else if shape = 3 then
    let (payload, rng2) := pickExternPayload rng1
    let (tail, rng3) := pickTailBits rng2
    (mkLdmsgaddrCase s!"fuzz/ok/extern-tail/len-{payload.size}/tail-{tail.size}"
      #[.slice (mkAddrSlice (mkAddrExternBits payload) tail)], rng3)
  else if shape = 4 then
    let (wc, rng2) := randNat rng1 0 255
    (mkLdmsgaddrCase s!"fuzz/ok/std/wc-{wc}" #[.slice (mkAddrSlice (mkAddrStdBits wc addr256A))], rng2)
  else if shape = 5 then
    let (wc, rng2) := randNat rng1 0 255
    let (tail, rng3) := pickTailBits rng2
    (mkLdmsgaddrCase s!"fuzz/ok/std-tail/wc-{wc}/tail-{tail.size}"
      #[.slice (mkAddrSlice (mkAddrStdBits wc addr256B) tail)], rng3)
  else if shape = 6 then
    let (wc, rng2) := randNat rng1 0 255
    (mkLdmsgaddrCase s!"fuzz/ok/deep-std/wc-{wc}" #[.null, .slice (mkAddrSlice (mkAddrStdBits wc addr256A))], rng2)
  else if shape = 7 then
    let (prefixBits, rng2) := randNat rng1 0 1
    (mkLdmsgaddrCase s!"fuzz/cellund/prefix-short-{prefixBits}"
      #[.slice (mkSliceFromBits (Array.replicate prefixBits false))], rng2)
  else if shape = 8 then
    let (s, rng2) := pickExternTruncatedSlice rng1
    (mkLdmsgaddrCase "fuzz/cellund/extern-truncated" #[.slice s], rng2)
  else if shape = 9 then
    let (s, rng2) := pickStdTruncatedSlice rng1
    (mkLdmsgaddrCase "fuzz/cellund/std-truncated" #[.slice s], rng2)
  else if shape = 10 then
    (mkLdmsgaddrCase "fuzz/cellund/anycast-depth-zero"
      #[.slice (mkSliceFromBits (natToBits 2 2 ++ natToBits 1 1 ++ natToBits 0 5))], rng1)
  else if shape = 11 then
    (mkLdmsgaddrCase "fuzz/cellund/anycast-depth31"
      #[.slice (mkSliceFromBits (natToBits 2 2 ++ natToBits 1 1 ++ natToBits 31 5))], rng1)
  else if shape = 12 then
    let (s, rng2) := pickAnycastPrefixShortSlice rng1
    (mkLdmsgaddrCase "fuzz/cellund/anycast-prefix-short" #[.slice s], rng2)
  else if shape = 13 then
    let (s, rng2) := pickVarTruncatedSlice rng1
    (mkLdmsgaddrCase "fuzz/cellund/var-truncated" #[.slice s], rng2)
  else if shape = 14 then
    (mkLdmsgaddrCase "fuzz/underflow/empty" #[], rng1)
  else if shape = 15 then
    (mkLdmsgaddrCase "fuzz/type/top-not-slice" #[.null], rng1)
  else
    (mkLdmsgaddrCase "fuzz/type/deep-top-not-slice" #[.slice (mkAddrSlice mkAddrNoneBits), .null], rng1)

def suite : InstrSuite where
  id := ldmsgaddrId
  unit := #[
    { name := "unit/direct/success-order-and-remainder"
      run := do
        let checks : Array (String × BitString × BitString × Nat) :=
          #[
            ("ok/none-no-tail", mkAddrNoneBits, #[], 2),
            ("ok/none-with-tail", mkAddrNoneBits, tailBits7, 2),
            ("ok/extern-len0", mkAddrExternBits #[], #[], consumedExternBits 0),
            ("ok/extern-len9-with-tail", mkAddrExternBits extPayload9, tailBits11, consumedExternBits extPayload9.size),
            ("ok/std-no-anycast", mkAddrStdBits 0 addr256A, #[], consumedStdBits),
            ("ok/std-no-anycast-tail", mkAddrStdBits 255 addr256B, tailBits13, consumedStdBits)
          ]
        for c in checks do
          let label := c.1
          let addrBits := c.2.1
          let tail := c.2.2.1
          let consumed := c.2.2.2
          let input := mkAddrSlice addrBits tail
          expectOkStack label
            (runLdmsgaddrDirect #[.slice input])
            (expectedSuccessStack #[] input consumed)

        let deepInput := mkAddrSlice (mkAddrExternBits extPayload9) tailBits11
        expectOkStack "ok/deep-stack-preserve-below"
          (runLdmsgaddrDirect #[.null, .slice deepInput])
          (expectedSuccessStack #[.null] deepInput (consumedExternBits extPayload9.size)) }
    ,
    { name := "unit/direct/underflow-and-type-order"
      run := do
        expectErr "underflow/empty" (runLdmsgaddrDirect #[]) .stkUnd
        expectErr "type/top-not-slice" (runLdmsgaddrDirect #[.null]) .typeChk
        expectErr "type/deep-top-not-slice"
          (runLdmsgaddrDirect #[.slice (mkAddrSlice mkAddrNoneBits), .null]) .typeChk }
    ,
    { name := "unit/direct/invalid-shape-cellund"
      run := do
        expectErr "cellund/prefix-too-short-0"
          (runLdmsgaddrDirect #[.slice (mkSliceFromBits #[])]) .cellUnd
        expectErr "cellund/prefix-too-short-1"
          (runLdmsgaddrDirect #[.slice (mkSliceFromBits #[false])]) .cellUnd

        expectErr "cellund/extern-len-prefix-short"
          (runLdmsgaddrDirect #[.slice (mkSliceFromBits (natToBits 1 2 ++ Array.replicate 8 false))]) .cellUnd
        expectErr "cellund/extern-len1-no-payload"
          (runLdmsgaddrDirect #[.slice (mkSliceFromBits (mkAddrExternBitsWithLen 1 0))]) .cellUnd
        expectErr "cellund/extern-len9-payload-short"
          (runLdmsgaddrDirect #[.slice (mkSliceFromBits (mkAddrExternBitsWithLen 9 8))]) .cellUnd
        expectErr "cellund/std-missing-one-bit"
          (runLdmsgaddrDirect #[.slice (mkSliceFromBits (mkTruncatedStdBits 263))]) .cellUnd

        expectErr "cellund/anycast-depth-zero"
          (runLdmsgaddrDirect #[.slice (mkSliceFromBits (natToBits 2 2 ++ natToBits 1 1 ++ natToBits 0 5))]) .cellUnd
        expectErr "cellund/anycast-depth31"
          (runLdmsgaddrDirect #[.slice (mkSliceFromBits (natToBits 2 2 ++ natToBits 1 1 ++ natToBits 31 5))]) .cellUnd
        expectErr "cellund/anycast-depth5-prefix-short"
          (runLdmsgaddrDirect #[.slice (mkSliceFromBits
            (natToBits 2 2 ++ natToBits 1 1 ++ natToBits 5 5 ++ Array.replicate 4 false))]) .cellUnd
        expectErr "cellund/std-anycast-depth3-disallowed"
          (runLdmsgaddrDirect #[.slice (mkAddrSlice (mkAddrStdAnycastBits 3 anycastPfx3 17 addr256A))]) .cellUnd

        expectErr "cellund/var-tag-only"
          (runLdmsgaddrDirect #[.slice (mkSliceFromBits (natToBits 3 2))]) .cellUnd
        expectErr "cellund/var-missing-wc"
          (runLdmsgaddrDirect #[.slice (mkSliceFromBits (natToBits 3 2 ++ natToBits 0 1 ++ natToBits 73 9))]) .cellUnd
        expectErr "cellund/var-len73-no-payload"
          (runLdmsgaddrDirect #[.slice (mkSliceFromBits
            (natToBits 3 2 ++ natToBits 0 1 ++ natToBits 73 9 ++ natToBits 0x11223344 32))]) .cellUnd
        expectErr "cellund/var-anycast0-len73-disallowed"
          (runLdmsgaddrDirect #[.slice (mkAddrSlice (mkAddrVarBits 0x11223344 varPayload73))]) .cellUnd
        expectErr "cellund/var-anycast5-len73-disallowed"
          (runLdmsgaddrDirect #[.slice (mkAddrSlice (mkAddrVarAnycastBits 5 anycastPfx5 0x01020304 varPayload73))]) .cellUnd }
    ,
    { name := "unit/opcode/decode-and-assembler-boundaries"
      run := do
        let program : Array Instr := #[ldmsgaddrInstr, .tonEnvOp (.ldMsgAddr true), .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/ldmsgaddr" s0 ldmsgaddrInstr 16
        let s2 ← expectDecodeStep "decode/ldmsgaddrq" s1 (.tonEnvOp (.ldMsgAddr true)) 16
        let s3 ← expectDecodeStep "decode/tail-add" s2 .add 8
        if s3.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/end: expected exhausted slice, got {s3.bitsRemaining} bits remaining") }
    ,
    { name := "unit/dispatch/non-tonenv-falls-through"
      run := do
        expectOkStack "dispatch/fallback"
          (runLdmsgaddrDispatchFallback #[.null])
          #[.null, intV 440] }
  ]
  oracle := #[
    mkLdmsgaddrCase "ok/none-no-tail" #[.slice (mkAddrSlice mkAddrNoneBits)],
    mkLdmsgaddrCase "ok/none-with-tail" #[.slice (mkAddrSlice mkAddrNoneBits tailBits7)],
    mkLdmsgaddrCase "ok/extern-len0" #[.slice (mkAddrSlice (mkAddrExternBits #[]))],
    mkLdmsgaddrCase "ok/extern-len9" #[.slice (mkAddrSlice (mkAddrExternBits extPayload9))],
    mkLdmsgaddrCase "ok/extern-len255" #[.slice (mkAddrSlice (mkAddrExternBits extPayload255))],
    mkLdmsgaddrCase "ok/extern-len511" #[.slice (mkAddrSlice (mkAddrExternBits extPayload511))],
    mkLdmsgaddrCase "ok/extern-len9-with-tail" #[.slice (mkAddrSlice (mkAddrExternBits extPayload9) tailBits11)],
    mkLdmsgaddrCase "ok/std-anycast0-wc0" #[.slice (mkAddrSlice (mkAddrStdBits 0 addr256A))],
    mkLdmsgaddrCase "ok/std-anycast0-wc255" #[.slice (mkAddrSlice (mkAddrStdBits 255 addr256B))],
    mkLdmsgaddrCase "ok/std-anycast0-with-tail"
      #[.slice (mkAddrSlice (mkAddrStdBits 17 addr256A) tailBits13)],
    mkLdmsgaddrCase "ok/deep-stack-below-preserved"
      #[.null, .slice (mkAddrSlice (mkAddrExternBits extPayload9) tailBits11)],

    mkLdmsgaddrCase "cellund/prefix-too-short-0" #[.slice (mkSliceFromBits #[])],
    mkLdmsgaddrCase "cellund/prefix-too-short-1" #[.slice (mkSliceFromBits #[false])],
    mkLdmsgaddrCase "cellund/extern-len-prefix-short"
      #[.slice (mkSliceFromBits (natToBits 1 2 ++ Array.replicate 8 false))],
    mkLdmsgaddrCase "cellund/extern-len1-no-payload"
      #[.slice (mkSliceFromBits (mkAddrExternBitsWithLen 1 0))],
    mkLdmsgaddrCase "cellund/extern-len9-payload-short"
      #[.slice (mkSliceFromBits (mkAddrExternBitsWithLen 9 8))],
    mkLdmsgaddrCase "cellund/std-missing-one-bit"
      #[.slice (mkSliceFromBits (mkTruncatedStdBits 263))],
    mkLdmsgaddrCase "cellund/anycast-depth-zero"
      #[.slice (mkSliceFromBits (natToBits 2 2 ++ natToBits 1 1 ++ natToBits 0 5))],
    mkLdmsgaddrCase "cellund/anycast-depth31"
      #[.slice (mkSliceFromBits (natToBits 2 2 ++ natToBits 1 1 ++ natToBits 31 5))],
    mkLdmsgaddrCase "cellund/anycast-depth5-prefix-short"
      #[.slice (mkSliceFromBits (natToBits 2 2 ++ natToBits 1 1 ++ natToBits 5 5 ++ Array.replicate 4 false))],
    mkLdmsgaddrCase "cellund/var-tag-only"
      #[.slice (mkSliceFromBits (natToBits 3 2))],
    mkLdmsgaddrCase "cellund/var-missing-wc"
      #[.slice (mkSliceFromBits (natToBits 3 2 ++ natToBits 0 1 ++ natToBits 255 9))],
    mkLdmsgaddrCase "cellund/var-len255-no-payload"
      #[.slice (mkSliceFromBits (natToBits 3 2 ++ natToBits 0 1 ++ natToBits 255 9 ++ natToBits 0x11223344 32))],

    mkLdmsgaddrCase "underflow/empty" #[],
    mkLdmsgaddrCase "type/top-not-slice" #[.null],
    mkLdmsgaddrCase "type/deep-top-not-slice" #[.slice (mkAddrSlice mkAddrNoneBits), .null],

    mkLdmsgaddrCase "gas/exact-cost-succeeds" #[.slice (mkAddrSlice (mkAddrExternBits extPayload9))]
      #[.pushInt (.num ldmsgaddrSetGasExact), .tonEnvOp .setGasLimit, ldmsgaddrInstr],
    mkLdmsgaddrCase "gas/exact-minus-one-out-of-gas" #[.slice (mkAddrSlice (mkAddrExternBits extPayload9))]
      #[.pushInt (.num ldmsgaddrSetGasExactMinusOne), .tonEnvOp .setGasLimit, ldmsgaddrInstr]
  ]
  fuzz := #[
    { seed := 2026021001
      count := 500
      gen := genLdmsgaddrFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.LDMSGADDR
