import Tests.Tuple.Util

open TvmLean Tests
open Tests.Tuple

namespace Tests.Tuple

def decodeInstrBits (bs : BitString) : Except String Instr := do
  let cell : Cell := Cell.mkOrdinary bs #[]
  let s := Slice.ofCell cell
  match decodeCp0 s with
  | .error e => throw s!"decodeCp0 failed: {reprStr e}"
  | .ok (i, rest) =>
      if rest.bitsRemaining != 0 then
        throw s!"decodeCp0 did not consume all bits: remaining={rest.bitsRemaining}"
      return i

def testAllTupleOps : IO Unit := do
  -- Helpers
  let runOk (label : String) (i : Instr) (stack : Stack) (expect : Stack) : IO Unit := do
    let (code, st) ← runInstrWithStack i stack
    assertExitOk label code
    assert (st.stack == expect) s!"{label}: stack mismatch got={st.stack} expect={expect}"

  let runExc (label : String) (i : Instr) (stack : Stack) (e : Excno) : IO Unit := do
    let (code, _st) ← runInstrWithStack i stack
    assertExitExc label code e

  -- Construct a tuple [1,2,3].
  let t123 : Value := mkTuple [vInt 1, vInt 2, vInt 3]

  -- TUPLE <n> (mktuple)
  runOk "tuple/mktuple" (.tupleOp (.mktuple 3)) #[vInt 1, vInt 2, vInt 3] #[t123]
  runExc "tuple/mktuple(stkUnd)" (.tupleOp (.mktuple 3)) #[vInt 1, vInt 2] .stkUnd

  -- TUPLEVAR (mktupleVar): stack has items then n on top.
  runOk "tuple/mktupleVar" (.tupleOp .mktupleVar) #[vInt 1, vInt 2, vInt 3, vInt 3] #[t123]
  runExc "tuple/mktupleVar(stkUnd)" (.tupleOp .mktupleVar) #[vInt 1, vInt 2, vInt 3, vInt 4] .stkUnd

  -- INDEX <idx>
  runOk "tuple/index" (.tupleOp (.index 1)) #[t123] #[vInt 2]
  runExc "tuple/index(rangeChk)" (.tupleOp (.index 5)) #[t123] .rangeChk
  runExc "tuple/index(typeChk)" (.tupleOp (.index 0)) #[vInt 1] .typeChk

  -- INDEXVAR / INDEXVARQ (pop idx, then tuple-or-null)
  runOk "tuple/indexVar" (.tupleOp .indexVar) #[t123, vInt 2] #[vInt 3]
  runExc "tuple/indexVar(rangeChk)" (.tupleOp .indexVar) #[t123, vInt 9] .rangeChk
  runOk "tuple/indexVarQ(null)" (.tupleOp .indexVarQ) #[Value.null, vInt 0] #[Value.null]
  runOk "tuple/indexVarQ(oob->null)" (.tupleOp .indexVarQ) #[t123, vInt 9] #[Value.null]
  runExc "tuple/indexVarQ(idx=255 rangeChk)" (.tupleOp .indexVarQ) #[t123, vInt 255] .rangeChk

  -- INDEXQ <idx>
  runOk "tuple/indexQ(inrange)" (.tupleOp (.indexQ 2)) #[t123] #[vInt 3]
  runOk "tuple/indexQ(oob->null)" (.tupleOp (.indexQ 9)) #[t123] #[Value.null]
  runOk "tuple/indexQ(null)" (.tupleOp (.indexQ 0)) #[Value.null] #[Value.null]

  -- INDEX2 / INDEX3 perform nested tuple indexing.
  let inner4 : Value := mkTuple [vInt 10, vInt 11, vInt 12, vInt 13]
  let nested2 : Value := mkTuple [inner4, mkTuple [vInt 20]]
  runOk "tuple/index2" (.tupleOp (.index2 0 3)) #[nested2] #[vInt 13]

  let nested3 : Value := mkTuple [mkTuple [mkTuple [vInt 1, vInt 2], mkTuple [vInt 3]], mkTuple []]
  runOk "tuple/index3" (.tupleOp (.index3 0 0 1)) #[nested3] #[vInt 2]

  -- UNTUPLE <n>
  runOk "tuple/untuple" (.tupleOp (.untuple 3)) #[t123] #[vInt 1, vInt 2, vInt 3]
  runExc "tuple/untuple(typeChk size)" (.tupleOp (.untuple 2)) #[t123] .typeChk
  runExc "tuple/untuple(typeChk non-tuple)" (.tupleOp (.untuple 1)) #[vInt 1] .typeChk

  -- UNTUPLEVAR: expects n then tuple.
  runOk "tuple/untupleVar" (.tupleOp .untupleVar) #[t123, vInt 3] #[vInt 1, vInt 2, vInt 3]
  runExc "tuple/untupleVar(typeChk)" (.tupleOp .untupleVar) #[t123, vInt 2] .typeChk

  -- UNPACKFIRST <n> / UNPACKFIRSTVAR
  runOk "tuple/unpackFirst" (.tupleOp (.unpackFirst 2)) #[t123] #[vInt 1, vInt 2]
  runExc "tuple/unpackFirst(typeChk short)" (.tupleOp (.unpackFirst 4)) #[t123] .typeChk
  runOk "tuple/unpackFirstVar" (.tupleOp .unpackFirstVar) #[t123, vInt 2] #[vInt 1, vInt 2]

  -- EXPLODE <maxLen> / EXPLODEVAR: pushes items then length.
  runOk "tuple/explode" (.tupleOp (.explode 3)) #[t123] #[vInt 1, vInt 2, vInt 3, vInt 3]
  runExc "tuple/explode(typeChk maxLen)" (.tupleOp (.explode 2)) #[t123] .typeChk
  runOk "tuple/explodeVar" (.tupleOp .explodeVar) #[t123, vInt 3] #[vInt 1, vInt 2, vInt 3, vInt 3]

  -- SETINDEX <idx> / SETINDEXVAR
  runOk "tuple/setIndex" (.tupleOp (.setIndex 1)) #[t123, vInt 999] #[mkTuple [vInt 1, vInt 999, vInt 3]]
  runExc "tuple/setIndex(rangeChk)" (.tupleOp (.setIndex 9)) #[t123, vInt 0] .rangeChk
  runOk "tuple/setIndexVar" (.tupleOp .setIndexVar) #[t123, vInt 999, vInt 1] #[mkTuple [vInt 1, vInt 999, vInt 3]]

  -- SETINDEXQ / SETINDEXVARQ
  runOk "tuple/setIndexQ(null,null)->null" (.tupleOp (.setIndexQ 5)) #[Value.null, Value.null] #[Value.null]
  runOk "tuple/setIndexQ(null,x)->new tuple" (.tupleOp (.setIndexQ 2)) #[Value.null, vInt 7] #[mkTuple [Value.null, Value.null, vInt 7]]
  runOk "tuple/setIndexQ(extend)" (.tupleOp (.setIndexQ 5)) #[mkTuple [vInt 1], vInt 9] #[mkTuple [vInt 1, Value.null, Value.null, Value.null, Value.null, vInt 9]]
  runOk "tuple/setIndexQ(oob with null keeps)" (.tupleOp (.setIndexQ 5)) #[mkTuple [vInt 1], Value.null] #[mkTuple [vInt 1]]

  runOk "tuple/setIndexVarQ(null,x)->new tuple" (.tupleOp .setIndexVarQ) #[Value.null, vInt 7, vInt 2] #[mkTuple [Value.null, Value.null, vInt 7]]
  runOk "tuple/setIndexVarQ(set existing)" (.tupleOp .setIndexVarQ) #[t123, vInt 99, vInt 0] #[mkTuple [vInt 99, vInt 2, vInt 3]]
  runExc "tuple/setIndexVarQ(idx=255 rangeChk)" (.tupleOp .setIndexVarQ) #[Value.null, vInt 1, vInt 255] .rangeChk

  -- TLEN / QTLEN / ISTUPLE / LAST
  runOk "tuple/tlen" (.tupleOp .tlen) #[t123] #[vInt 3]
  runExc "tuple/tlen(typeChk)" (.tupleOp .tlen) #[vInt 1] .typeChk
  runOk "tuple/qtlen(tuple)" (.tupleOp .qtlen) #[t123] #[vInt 3]
  runOk "tuple/qtlen(non-tuple)" (.tupleOp .qtlen) #[vInt 1] #[vInt (-1)]
  runOk "tuple/isTuple(tuple)" (.tupleOp .isTuple) #[t123] #[vInt (-1)]
  runOk "tuple/isTuple(non-tuple)" (.tupleOp .isTuple) #[vInt 1] #[vInt 0]
  runOk "tuple/last" (.tupleOp .last) #[t123] #[vInt 3]
  runExc "tuple/last(typeChk empty)" (.tupleOp .last) #[mkTuple []] .typeChk

  -- TPUSH / TPOP
  runOk "tuple/tpush" (.tupleOp .tpush) #[t123, vInt 4] #[mkTuple [vInt 1, vInt 2, vInt 3, vInt 4]]
  runOk "tuple/tpop" (.tupleOp .tpop) #[mkTuple [vInt 7, vInt 8]] #[mkTuple [vInt 7], vInt 8]

  -- PUSHNULL / ISNULL and NULL* ops are in the spec's tuple category but are separate `Instr` constructors.
  runOk "tuple/pushnull" .pushNull #[] #[Value.null]
  runOk "tuple/isnull(null)" .isNull #[Value.null] #[vInt (-1)]
  runOk "tuple/isnull(non-null)" .isNull #[vInt 1] #[vInt 0]

  -- NULLSWAPIF / NULLSWAPIFNOT: spot-check trigger/no-trigger behavior.
  -- For stack [a, x], the implementation pushes null(s) above `a` when triggered, then pushes x back.
  runOk "tuple/nullswapif(trigger)" .nullSwapIf #[vInt 10, vInt 1] #[vInt 10, Value.null, vInt 1]
  runOk "tuple/nullswapif(no trigger)" .nullSwapIf #[vInt 10, vInt 0] #[vInt 10, vInt 0]
  runOk "tuple/nullswapifnot(trigger)" .nullSwapIfNot #[vInt 10, vInt 0] #[vInt 10, Value.null, vInt 0]

  -- NULLROTRIF / NULLROTRIFNOT: ensure they run and preserve the condition int on top.
  let (codeR, stR) ← runInstrWithStack .nullRotrIf #[vInt 11, vInt 22, vInt 1]
  assertExitOk "tuple/nullrotrif" codeR
  assert (stR.stack.back! == vInt 1) s!"tuple/nullrotrif: expected condition preserved"

  let (codeR2, stR2) ← runInstrWithStack .nullRotrIfNot #[vInt 11, vInt 22, vInt 0]
  assertExitOk "tuple/nullrotrifnot" codeR2
  assert (stR2.stack.back! == vInt 0) s!"tuple/nullrotrifnot: expected condition preserved"

  -- Decode sanity checks for a few tuple opcodes.
  let decodeOrThrow (label : String) (bs : BitString) : IO Instr := do
    match decodeInstrBits bs with
    | .ok i => pure i
    | .error e => throw (IO.userError s!"{label}: {e}")
  let iTlen ← decodeOrThrow "decode TLEN" (natToBits 0x6f88 16)
  assert (iTlen == .tupleOp .tlen) s!"decode TLEN mismatch: {iTlen.pretty}"
  let iIndex2 ← decodeOrThrow "decode INDEX2" (natToBits 0x6fbf 16)
  assert (iIndex2 == .tupleOp (.index2 3 3)) s!"decode INDEX2 mismatch: {iIndex2.pretty}"

initialize
  Tests.registerTest "tuple/all" testAllTupleOps

  -- Roundtrips for tuple ops (covers encode/decode for this family).
  Tests.registerRoundtrip (.tupleOp (.mktuple 0))
  Tests.registerRoundtrip (.tupleOp (.mktuple 15))
  Tests.registerRoundtrip (.tupleOp .mktupleVar)
  Tests.registerRoundtrip (.tupleOp (.index 0))
  Tests.registerRoundtrip (.tupleOp (.index 15))
  Tests.registerRoundtrip (.tupleOp .indexVar)
  Tests.registerRoundtrip (.tupleOp (.indexQ 0))
  Tests.registerRoundtrip (.tupleOp (.indexQ 15))
  Tests.registerRoundtrip (.tupleOp .indexVarQ)
  Tests.registerRoundtrip (.tupleOp (.untuple 0))
  Tests.registerRoundtrip (.tupleOp (.untuple 15))
  Tests.registerRoundtrip (.tupleOp .untupleVar)
  Tests.registerRoundtrip (.tupleOp (.unpackFirst 0))
  Tests.registerRoundtrip (.tupleOp (.unpackFirst 15))
  Tests.registerRoundtrip (.tupleOp .unpackFirstVar)
  Tests.registerRoundtrip (.tupleOp (.explode 0))
  Tests.registerRoundtrip (.tupleOp (.explode 15))
  Tests.registerRoundtrip (.tupleOp .explodeVar)
  Tests.registerRoundtrip (.tupleOp (.setIndex 0))
  Tests.registerRoundtrip (.tupleOp (.setIndex 15))
  Tests.registerRoundtrip (.tupleOp .setIndexVar)
  Tests.registerRoundtrip (.tupleOp (.setIndexQ 0))
  Tests.registerRoundtrip (.tupleOp (.setIndexQ 15))
  Tests.registerRoundtrip (.tupleOp .setIndexVarQ)
  Tests.registerRoundtrip (.tupleOp .tlen)
  Tests.registerRoundtrip (.tupleOp .qtlen)
  Tests.registerRoundtrip (.tupleOp .isTuple)
  Tests.registerRoundtrip (.tupleOp .last)
  Tests.registerRoundtrip (.tupleOp .tpush)
  Tests.registerRoundtrip (.tupleOp .tpop)
  Tests.registerRoundtrip (.tupleOp (.index2 0 0))
  Tests.registerRoundtrip (.tupleOp (.index2 3 3))
  Tests.registerRoundtrip (.tupleOp (.index3 0 0 0))
  Tests.registerRoundtrip (.tupleOp (.index3 3 3 3))

  -- And the tuple-category non-tupleOp instructions.
  Tests.registerRoundtrip .pushNull
  Tests.registerRoundtrip .isNull
  Tests.registerRoundtrip .nullSwapIf
  Tests.registerRoundtrip .nullSwapIfNot
  Tests.registerRoundtrip .nullRotrIf
  Tests.registerRoundtrip .nullRotrIfNot
  Tests.registerRoundtrip .nullSwapIf2
  Tests.registerRoundtrip .nullSwapIfNot2
  Tests.registerRoundtrip .nullRotrIf2
  Tests.registerRoundtrip .nullRotrIfNot2

end Tests.Tuple
