import Tests.Dictionary.Util

open TvmLean Tests

namespace Tests.Dictionary

set_option maxRecDepth 2048

def testDictAll : IO Unit := do
  -- STDICT: store maybe-dict into builder.
  let dict0 : Cell := mkCellBits (natToBits 0xab 8)
  let (codeS0, stS0) ← runInstrWithStack .stdict #[.null, .builder Builder.empty]
  assertExitOk "dict/stdict(null)" codeS0
  assert (stS0.stack.size == 1) s!"dict/stdict(null): unexpected stack size={stS0.stack.size}"
  match stS0.stack[0]! with
  | .builder b =>
      assert (b.bits == #[false]) s!"dict/stdict(null): expected hasRef=false bit, got bits={b.bits}"
      assert (b.refs.isEmpty) s!"dict/stdict(null): expected no refs, got refs={b.refs.size}"
  | v => throw (IO.userError s!"dict/stdict(null): expected builder, got {v.pretty}")

  let (codeS1, stS1) ← runInstrWithStack .stdict #[.cell dict0, .builder Builder.empty]
  assertExitOk "dict/stdict(cell)" codeS1
  match stS1.stack[0]! with
  | .builder b =>
      assert (b.bits == #[true]) s!"dict/stdict(cell): expected hasRef=true bit, got bits={b.bits}"
      assert (b.refs == #[dict0]) s!"dict/stdict(cell): unexpected refs={b.refs.size}"
  | v => throw (IO.userError s!"dict/stdict(cell): expected builder, got {v.pretty}")

  -- SKIPDICT: skip the serialized dict header in a slice.
  let hdrCell : Cell := mkCellBits #[true] #[dict0]
  let hdrSlice : Slice := Slice.ofCell hdrCell
  let (codeK, stK) ← runInstrWithStack .skipdict #[.slice hdrSlice]
  assertExitOk "dict/skipdict" codeK
  let expectSkip : Slice := { hdrSlice with bitPos := hdrSlice.bitPos + 1, refPos := hdrSlice.refPos + 1 }
  assertStackEq "dict/skipdict" stK.stack #[.slice expectSkip]

  -- LDDICT: load maybe-dict from slice (success + quiet/failure).
  let (codeL0, stL0) ← runInstrWithStack (.lddict false false) #[.slice hdrSlice]
  assertExitOk "dict/lddict" codeL0
  let expectAfter : Slice := { hdrSlice with bitPos := hdrSlice.bitPos + 1, refPos := hdrSlice.refPos + 1 }
  assertStackEq "dict/lddict" stL0.stack #[.cell dict0, .slice expectAfter]

  let (codeL1, stL1) ← runInstrWithStack (.lddict true true) #[.slice hdrSlice]
  assertExitOk "dict/lddict(preload+quiet)" codeL1
  assertStackEq "dict/lddict(preload+quiet)" stL1.stack #[.cell dict0, vInt (-1)]

  let badSlice : Slice := Slice.ofCell (mkCellBits #[])
  let (codeL2, stL2) ← runInstrWithStack (.lddict false true) #[.slice badSlice]
  assertExitOk "dict/lddictq(fail)" codeL2
  assertStackEq "dict/lddictq(fail)" stL2.stack #[.slice badSlice, vInt 0]

  let (codeL3, _stL3) ← runInstrWithStack (.lddict false false) #[.slice badSlice]
  assertExitExc "dict/lddict(fail)" codeL3 .cellUnd

  -- DICTSET/DICTGET (slice key, slice value).
  let n8 : Nat := 8
  let keyA : BitString := natToBits 0x10 n8
  let keyB : BitString := natToBits 0x20 n8
  let valAcell : Cell := mkCellBits (natToBits 0xaaaa 16)
  let valBcell : Cell := mkCellBits (natToBits 0xbbbb 16)
  let dictAB? ← mkDictRootSlice [(keyA, Slice.ofCell valAcell), (keyB, Slice.ofCell valBcell)]
  let dictAB ←
    match dictAB? with
    | some c => pure c
    | none => throw (IO.userError "mkDictRootSlice produced none")

  let (codeG0, stG0) ←
    runInstrWithStack (.dictGet false false false) #[.slice (mkKeySlice keyA), .cell dictAB, vInt (Int.ofNat n8)]
  assertExitOk "dict/dictget(found)" codeG0
  assert (stG0.stack.size == 2) s!"dict/dictget(found): unexpected stack size={stG0.stack.size}"
  match stG0.stack[0]! with
  | .slice s =>
      assert (sliceToCell s == valAcell) s!"dict/dictget(found): bad value cell"
  | v => throw (IO.userError s!"dict/dictget(found): expected slice, got {v.pretty}")
  assert (stG0.stack[1]! == vInt (-1)) s!"dict/dictget(found): expected ok=-1"

  let (codeG1, stG1) ←
    runInstrWithStack (.dictGet false false false) #[.slice (mkKeySlice (natToBits 0x99 n8)), .cell dictAB, vInt (Int.ofNat n8)]
  assertExitOk "dict/dictget(miss)" codeG1
  assertStackEq "dict/dictget(miss)" stG1.stack #[vInt 0]

  -- DICTSET (mode=set) on empty dict: returns new root only.
  let newVal : Cell := mkCellBits (natToBits 0x1234 16)
  let (codeSet0, stSet0) ←
    runInstrWithStack (.dictSet false false false .set)
      #[.slice (Slice.ofCell newVal), .slice (mkKeySlice keyA), .null, vInt (Int.ofNat n8)]
  assertExitOk "dict/dictset(set)" codeSet0
  assert (stSet0.stack.size == 1) s!"dict/dictset(set): unexpected stack size={stSet0.stack.size}"
  let root1? ←
    match stSet0.stack[0]! with
    | .cell c => pure (some c)
    | .null => pure none
    | v => throw (IO.userError s!"dict/dictset(set): expected cell|null, got {v.pretty}")
  match dictLookupWithCells root1? keyA with
  | .error e => throw (IO.userError s!"dict/dictset(set): lookup error {reprStr e}")
  | .ok (none, _) => throw (IO.userError "dict/dictset(set): key not found")
  | .ok (some s, _) =>
      assert (sliceToCell s == newVal) s!"dict/dictset(set): stored value mismatch"

  -- DICTREPLACE / DICTADD: ok flag behavior.
  let dictOne? ← mkDictRootSlice [(keyA, Slice.ofCell valAcell)]
  let dictOne ←
    match dictOne? with
    | some c => pure c
    | none => throw (IO.userError "mkDictRootSlice(one) produced none")

  let repVal : Cell := mkCellBits (natToBits 0x7777 16)
  let (codeRep0, stRep0) ←
    runInstrWithStack (.dictSet false false false .replace)
      #[.slice (Slice.ofCell repVal), .slice (mkKeySlice keyA), .cell dictOne, vInt (Int.ofNat n8)]
  assertExitOk "dict/dictreplace(found)" codeRep0
  assert (stRep0.stack.size == 2) s!"dict/dictreplace(found): unexpected stack size={stRep0.stack.size}"
  assert (stRep0.stack[1]! == vInt (-1)) s!"dict/dictreplace(found): expected ok=-1"

  let rootRep ←
    match stRep0.stack[0]! with
    | .cell c => pure (some c)
    | .null => pure none
    | v => throw (IO.userError s!"dict/dictreplace(found): expected cell|null, got {v.pretty}")
  match dictLookupWithCells rootRep keyA with
  | .ok (some s, _) => assert (sliceToCell s == repVal) s!"dict/dictreplace(found): value mismatch"
  | .ok (none, _) => throw (IO.userError "dict/dictreplace(found): missing key")
  | .error e => throw (IO.userError s!"dict/dictreplace(found): lookup error {reprStr e}")

  let (codeRep1, stRep1) ←
    runInstrWithStack (.dictSet false false false .replace)
      #[.slice (Slice.ofCell repVal), .slice (mkKeySlice keyB), .cell dictOne, vInt (Int.ofNat n8)]
  assertExitOk "dict/dictreplace(miss)" codeRep1
  assertStackEq "dict/dictreplace(miss)"
    stRep1.stack #[.cell dictOne, vInt 0]

  let (codeAdd0, stAdd0) ←
    runInstrWithStack (.dictSet false false false .add)
      #[.slice (Slice.ofCell valBcell), .slice (mkKeySlice keyB), .cell dictOne, vInt (Int.ofNat n8)]
  assertExitOk "dict/dictadd(absent)" codeAdd0
  assert (stAdd0.stack.size == 2) s!"dict/dictadd(absent): unexpected stack size={stAdd0.stack.size}"
  assert (stAdd0.stack[1]! == vInt (-1)) s!"dict/dictadd(absent): expected ok=-1"

  let (codeAdd1, stAdd1) ←
    runInstrWithStack (.dictSet false false false .add)
      #[.slice (Slice.ofCell valAcell), .slice (mkKeySlice keyA), .cell dictOne, vInt (Int.ofNat n8)]
  assertExitOk "dict/dictadd(present)" codeAdd1
  assertStackEq "dict/dictadd(present)" stAdd1.stack #[.cell dictOne, vInt 0]

  -- DICTGETREF (slice key, ref value).
  let refVal : Cell := mkCellBits (natToBits 0xde 8)
  let dictRef? ← mkDictRootRef [(keyA, refVal)]
  let dictRef ←
    match dictRef? with
    | some c => pure c
    | none => throw (IO.userError "mkDictRootRef produced none")
  let (codeGR, stGR) ←
    runInstrWithStack (.dictGet false false true) #[.slice (mkKeySlice keyA), .cell dictRef, vInt (Int.ofNat n8)]
  assertExitOk "dict/dictgetref" codeGR
  assertStackEq "dict/dictgetref" stGR.stack #[.cell refVal, vInt (-1)]

  -- DICTI/DICTU GET (int key).
  let keyI : Int := -1
  let bitsI ← dictKeyBitsOrFail keyI n8 false
  let dictI? ← mkDictRootSlice [(bitsI, Slice.ofCell valAcell)]
  let dictI ←
    match dictI? with
    | some c => pure c
    | none => throw (IO.userError "mkDictRootSlice(int) produced none")
  let (codeIG, stIG) ←
    runInstrWithStack (.dictGet true false false) #[vInt keyI, .cell dictI, vInt (Int.ofNat n8)]
  assertExitOk "dict/dictiget" codeIG
  assert (stIG.stack.size == 2) s!"dict/dictiget: unexpected stack size={stIG.stack.size}"
  assert (stIG.stack[1]! == vInt (-1)) s!"dict/dictiget: expected ok=-1"

  let keyU : Int := 255
  let bitsU ← dictKeyBitsOrFail keyU n8 true
  let dictU? ← mkDictRootSlice [(bitsU, Slice.ofCell valBcell)]
  let dictU ←
    match dictU? with
    | some c => pure c
    | none => throw (IO.userError "mkDictRootSlice(uint) produced none")
  let (codeUG, stUG) ←
    runInstrWithStack (.dictGet true true false) #[vInt keyU, .cell dictU, vInt (Int.ofNat n8)]
  assertExitOk "dict/dictuget" codeUG
  assert (stUG.stack[1]! == vInt (-1)) s!"dict/dictuget: expected ok=-1"

  -- Out-of-range integer key behaves like "not found" for GET (but rangeChk for SET).
  let (codeUG2, stUG2) ←
    runInstrWithStack (.dictGet true true false) #[vInt 300, .cell dictU, vInt (Int.ofNat n8)]
  assertExitOk "dict/dictuget(oob)" codeUG2
  assertStackEq "dict/dictuget(oob)" stUG2.stack #[vInt 0]

  let (codeIS0, _stIS0) ←
    runInstrWithStack (.dictSet true false false .set) #[.slice (Slice.ofCell valAcell), vInt 128, .null, vInt (Int.ofNat n8)]
  assertExitExc "dict/dictiset(range)" codeIS0 .rangeChk

  -- DICTSETB / DICTREPLACEB (builder value).
  let b0 : Builder := { Builder.empty with bits := natToBits 0xfeed 16 }
  let (codeSB, stSB) ←
    runInstrWithStack (.dictSetB false false .set)
      #[.builder b0, .slice (mkKeySlice keyA), .null, vInt (Int.ofNat n8)]
  assertExitOk "dict/dictsetb" codeSB
  let rootSB ←
    match stSB.stack[0]! with
    | .cell c => pure (some c)
    | .null => pure none
    | v => throw (IO.userError s!"dict/dictsetb: expected cell|null, got {v.pretty}")
  match dictLookupWithCells rootSB keyA with
  | .ok (some s, _) =>
      assert (sliceToCell s == b0.finalize) s!"dict/dictsetb: stored builder mismatch"
  | .ok (none, _) => throw (IO.userError "dict/dictsetb: missing key")
  | .error e => throw (IO.userError s!"dict/dictsetb: lookup error {reprStr e}")

  let rootB? ← mkDictRootBuilder [(keyA, b0)]
  let rootB ←
    match rootB? with
    | some c => pure c
    | none => throw (IO.userError "mkDictRootBuilder produced none")
  let b1 : Builder := { Builder.empty with bits := natToBits 0xbeef 16 }
  let (codeRB0, stRB0) ←
    runInstrWithStack (.dictReplaceB false false) #[.builder b1, .slice (mkKeySlice keyA), .cell rootB, vInt (Int.ofNat n8)]
  assertExitOk "dict/dictreplaceb(found)" codeRB0
  assert (stRB0.stack[1]! == vInt (-1)) s!"dict/dictreplaceb(found): expected ok=-1"

  -- DICTGETNEAR (get next/prev).
  let k1 : Int := 1
  let k3 : Int := 3
  let k5 : Int := 5
  let kb1 ← dictKeyBitsOrFail k1 n8 false
  let kb3 ← dictKeyBitsOrFail k3 n8 false
  let kb5 ← dictKeyBitsOrFail k5 n8 false
  let v1 : Cell := mkCellBits (natToBits 0x0101 16)
  let v3 : Cell := mkCellBits (natToBits 0x0303 16)
  let v5 : Cell := mkCellBits (natToBits 0x0505 16)
  let dict135? ← mkDictRootSlice [(kb1, Slice.ofCell v1), (kb3, Slice.ofCell v3), (kb5, Slice.ofCell v5)]
  let dict135 ←
    match dict135? with
    | some c => pure c
    | none => throw (IO.userError "mkDictRootSlice(135) produced none")

  -- DICTIGETNEXT: args4=8.
  let (codeN0, stN0) ← runInstrWithStack (.dictGetNear 8) #[vInt 3, .cell dict135, vInt (Int.ofNat n8)]
  assertExitOk "dict/dictigetnext" codeN0
  assert (stN0.stack.size == 3) s!"dict/dictigetnext: unexpected stack size={stN0.stack.size}"
  match stN0.stack[0]! with
  | .slice s => assert (sliceToCell s == v5) s!"dict/dictigetnext: value mismatch"
  | v => throw (IO.userError s!"dict/dictigetnext: expected value slice, got {v.pretty}")
  assert (stN0.stack[1]! == vInt 5) s!"dict/dictigetnext: expected key=5"
  assert (stN0.stack[2]! == vInt (-1)) s!"dict/dictigetnext: expected ok=-1"

  -- DICTIGETNEXTEQ: args4=9.
  let (codeN1, stN1) ← runInstrWithStack (.dictGetNear 9) #[vInt 3, .cell dict135, vInt (Int.ofNat n8)]
  assertExitOk "dict/dictigetnexteq" codeN1
  assert (stN1.stack.size == 3) s!"dict/dictigetnexteq: unexpected stack size={stN1.stack.size}"
  match stN1.stack[0]! with
  | .slice s => assert (sliceToCell s == v3) s!"dict/dictigetnexteq: value mismatch"
  | v => throw (IO.userError s!"dict/dictigetnexteq: expected value slice, got {v.pretty}")
  assert (stN1.stack[1]! == vInt 3) s!"dict/dictigetnexteq: expected key=3"
  assert (stN1.stack[2]! == vInt (-1)) s!"dict/dictigetnexteq: expected ok=-1"

  -- DICTUGETNEXT with key=-1 returns MIN key: args4=12.
  let bitsU0 ← dictKeyBitsOrFail 0 n8 true
  let v0 : Cell := mkCellBits (natToBits 0x0000 16)
  let dictU0? ← mkDictRootSlice [(bitsU0, Slice.ofCell v0), (bitsU, Slice.ofCell v5)]
  let dictU01 ←
    match dictU0? with
    | some c => pure c
    | none => throw (IO.userError "mkDictRootSlice(u01) produced none")
  let (codeN2, stN2) ← runInstrWithStack (.dictGetNear 12) #[vInt (-1), .cell dictU01, vInt (Int.ofNat n8)]
  assertExitOk "dict/dictugetnext(-1)" codeN2
  assert (stN2.stack.size == 3) s!"dict/dictugetnext(-1): unexpected stack size={stN2.stack.size}"
  match stN2.stack[0]! with
  | .slice s => assert (sliceToCell s == v0) s!"dict/dictugetnext(-1): value mismatch"
  | v => throw (IO.userError s!"dict/dictugetnext(-1): expected value slice, got {v.pretty}")
  assert (stN2.stack[1]! == vInt 0) s!"dict/dictugetnext(-1): expected key=0"
  assert (stN2.stack[2]! == vInt (-1)) s!"dict/dictugetnext(-1): expected ok=-1"

  -- DICTGETNEXT for slice keys: args4=4.
  let hint : Slice := mkKeySlice (natToBits 0x15 n8)
  let (codeN3, stN3) ← runInstrWithStack (.dictGetNear 4) #[.slice hint, .cell dictAB, vInt (Int.ofNat n8)]
  assertExitOk "dict/dictgetnext" codeN3
  assert (stN3.stack.size == 3) s!"dict/dictgetnext: unexpected stack size={stN3.stack.size}"
  match stN3.stack[1]! with
  | .slice k =>
      assert (bitsToNat (k.readBits n8) == 0x20) s!"dict/dictgetnext: expected key=0x20"
  | v => throw (IO.userError s!"dict/dictgetnext: expected key slice, got {v.pretty}")
  assert (stN3.stack[2]! == vInt (-1)) s!"dict/dictgetnext: expected ok=-1"

  -- DICTMIN/MAX and DICTREMMIN remove behavior (signed int keys).
  -- MIN: args5=4 (intKey signed, bySlice).
  let (codeM0, stM0) ← runInstrWithStack (.dictGetMinMax 4) #[.cell dict135, vInt (Int.ofNat n8)]
  assertExitOk "dict/dictimmin" codeM0
  assert (stM0.stack.size == 3) s!"dict/dictimmin: unexpected stack size={stM0.stack.size}"
  assert (stM0.stack[1]! == vInt 1) s!"dict/dictimmin: expected key=1"
  assert (stM0.stack[2]! == vInt (-1)) s!"dict/dictimmin: expected ok=-1"

  -- REMMIN: args5=20 (16+4).
  let (codeM1, stM1) ← runInstrWithStack (.dictGetMinMax 20) #[.cell dict135, vInt (Int.ofNat n8)]
  assertExitOk "dict/dictiremmin" codeM1
  assert (stM1.stack.size == 4) s!"dict/dictiremmin: unexpected stack size={stM1.stack.size}"
  let outRoot ←
    match stM1.stack[0]! with
    | .cell c => pure (some c)
    | .null => pure none
    | v => throw (IO.userError s!"dict/dictiremmin: expected cell|null, got {v.pretty}")
  assert (stM1.stack[2]! == vInt 1) s!"dict/dictiremmin: expected key=1"
  assert (stM1.stack[3]! == vInt (-1)) s!"dict/dictiremmin: expected ok=-1"
  match dictLookupWithCells outRoot kb1 with
  | .ok (none, _) => pure ()
  | .ok (some _, _) => throw (IO.userError "dict/dictiremmin: key was not removed")
  | .error e => throw (IO.userError s!"dict/dictiremmin: lookup error {reprStr e}")

  -- DICT{I,U}GET{JMP,EXEC}{Z}: not-found pushZ behavior + found execution.
  let (codeE0, stE0) ← runInstrWithStack (.dictGetExec false false true) #[vInt 123, .null, vInt (Int.ofNat n8)]
  assertExitOk "dict/dictigetjmpz(miss)" codeE0
  assertStackEq "dict/dictigetjmpz(miss)" stE0.stack #[vInt 123]

  let codeCell99 ←
    match assembleCp0 [.pushInt (.num 99)] with
    | .ok c => pure c
    | .error e => throw (IO.userError s!"assembleCp0(code99) failed: {reprStr e}")
  let codeSlice99 : Slice := Slice.ofCell codeCell99
  let kbExec ← dictKeyBitsOrFail 7 n8 false
  let dictExec? ← mkDictRootSlice [(kbExec, codeSlice99)]
  let dictExec ←
    match dictExec? with
    | some c => pure c
    | none => throw (IO.userError "mkDictRootSlice(exec) produced none")

  let (codeE1, stE1) ← runInstrWithStack (.dictGetExec false false false) #[vInt 7, .cell dictExec, vInt (Int.ofNat n8)]
  assertExitOk "dict/dictigetjmp(found)" codeE1
  assertStackEq "dict/dictigetjmp(found)" stE1.stack #[vInt 99]

  let (codeE2, stE2) ← runInstrWithStack (.dictGetExec false true false) #[vInt 7, .cell dictExec, vInt (Int.ofNat n8)]
  assertExitOk "dict/dictigetexec(found)" codeE2
  assertStackEq "dict/dictigetexec(found)" stE2.stack #[vInt 99]

  -- DICTPUSHCONST: requires a code cell reference; test via a handcrafted code cell.
  let dictConst : Cell := mkCellBits (natToBits 0x01 8)
  let keyBitsConst : Nat := 17
  let word24 : Nat := 0xf4a400 + keyBitsConst
  let codePushConst : Cell := mkCellBits (natToBits word24 24) #[dictConst]
  let (codePC, stPC) ← runCodeCellWith codePushConst
  assertExitOk "dict/dictpushconst" codePC
  assertStackEq "dict/dictpushconst" stPC.stack #[.cell dictConst, vInt (Int.ofNat keyBitsConst)]

initialize
  Tests.registerTest "dictionary/all" testDictAll
  Tests.registerRoundtrip .stdict
  Tests.registerRoundtrip .skipdict
  Tests.registerRoundtrip (.lddict false false)
  Tests.registerRoundtrip (.lddict true true)
  Tests.registerRoundtrip (.dictGet false false false)
  Tests.registerRoundtrip (.dictGet false false true)
  Tests.registerRoundtrip (.dictGet true false false)
  Tests.registerRoundtrip (.dictGet true true false)
  Tests.registerRoundtrip (.dictSet false false false .set)
  Tests.registerRoundtrip (.dictSet false false false .replace)
  Tests.registerRoundtrip (.dictSet false false false .add)
  Tests.registerRoundtrip (.dictSet true false false .set)
  Tests.registerRoundtrip (.dictSet true true false .set)
  Tests.registerRoundtrip (.dictSetB false false .set)
  Tests.registerRoundtrip (.dictSetB true false .set)
  Tests.registerRoundtrip (.dictSetB true true .set)
  Tests.registerRoundtrip (.dictReplaceB false false)
  Tests.registerRoundtrip (.dictReplaceB true false)
  Tests.registerRoundtrip (.dictReplaceB true true)
  Tests.registerRoundtrip (.dictGetNear 4)
  Tests.registerRoundtrip (.dictGetNear 8)
  Tests.registerRoundtrip (.dictGetNear 12)
  Tests.registerRoundtrip (.dictGetMinMax 2)
  Tests.registerRoundtrip (.dictGetMinMax 4)
  Tests.registerRoundtrip (.dictGetMinMax 6)
  Tests.registerRoundtrip (.dictGetMinMax 20)
  Tests.registerRoundtrip (.dictGetExec false false false)
  Tests.registerRoundtrip (.dictGetExec true true true)

end Tests.Dictionary
