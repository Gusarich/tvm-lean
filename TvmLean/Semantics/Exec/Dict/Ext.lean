import TvmLean.Semantics.Exec.Common

namespace TvmLean

/-! DICTEXT family: newer dict ops (LDDICTS, *SETGET/*DELGET, SUBDICT*, PFXDICT*). -/

namespace DictExt

private def pushBool (b : Bool) : VM Unit :=
  VM.pushSmallInt (if b then -1 else 0)

private def pushDictRoot (c? : Option Cell) : VM Unit := do
  match c? with
  | none => VM.push .null
  | some c => VM.push (.cell c)

private def consumeCreatedGas (created : Nat) : VM Unit := do
  if created > 0 then
    modify fun st => st.consumeGas (cellCreateGasPrice * Int.ofNat created)

private def registerLoaded (loaded : Array Cell) : VM Unit := do
  for c in loaded do
    VM.registerCellLoad c

private def prechargeRootLoad (dictCell? : Option Cell) : VM Unit := do
  match dictCell? with
  | some c => VM.registerCellLoad c
  | none => pure ()

private def loadedWithoutRoot (dictCell? : Option Cell) (loaded : Array Cell) : Array Cell :=
  match dictCell? with
  | none => loaded
  | some root => loaded.filter (fun c => c != root)

private def extractRefOrThrow (valueSlice : Slice) : VM Cell := do
  if valueSlice.bitsRemaining == 0 && valueSlice.refsRemaining == 1 then
    return valueSlice.cell.refs[valueSlice.refPos]!
  else
    throw .dictErr

private def slicePrefix (s : Slice) (bits : Nat) (refs : Nat := 0) : Except Excno (Slice × Slice) := do
  if !s.haveBits bits || !s.haveRefs refs then
    throw .cellUnd
  let mid : Slice := { s with bitPos := s.bitPos + bits, refPos := s.refPos + refs }
  let prefixCell : Cell := Slice.prefixCell s mid
  return (Slice.ofCell prefixCell, mid)

/-! Prefix dictionary helpers (TON `PrefixDictionary`, `pfx_dict_set`, `pfx_dict_lookup_delete`). -/

private def pfxLabelCommonPrefixLen (labelBits keyBits : BitString) (m : Nat) : Nat :=
  let cmpLen : Nat := Nat.min m labelBits.size
  let keyPart : BitString := keyBits.take cmpLen
  bitsCommonPrefixLen labelBits keyPart

private partial def pfxLookupPrefixWithCells (root : Option Cell) (keyBits : BitString) (keyLen : Nat) (n : Nat) :
    Except Excno (Option Slice × Nat × Array Cell) := do
  match root with
  | none => return (none, 0, #[])
  | some rootCell =>
      let rec go (cell : Cell) (nRem m pos : Nat) (loaded : Array Cell) :
          Except Excno (Option Slice × Nat × Array Cell) := do
        let loaded := loaded.push cell
        let lbl ← parseDictLabel cell nRem
        let labelBits : BitString := dictLabelBits lbl
        let l : Nat :=
          let keyPart := keyBits.extract pos (pos + Nat.min m lbl.len)
          bitsCommonPrefixLen labelBits keyPart
        if l < lbl.len then
          return (none, pos + l, loaded)
        let nRem := nRem - lbl.len
        let m := m - lbl.len
        let pos := pos + lbl.len
        let payload0 : Slice := lbl.remainder.advanceBits lbl.storedBits
        if !payload0.haveBits 1 then
          throw .dictErr
        let ctor : Bool := (payload0.readBits 1)[0]!
        let payload : Slice := { payload0 with bitPos := payload0.bitPos + 1 }
        if !ctor then
          return (some payload, pos, loaded)
        -- Fork node
        if nRem = 0 then
          throw .dictErr
        if payload.bitsRemaining != 0 || payload.refsRemaining != 2 then
          throw .dictErr
        if m = 0 then
          return (none, keyLen, loaded)
        let swBit : Bool := keyBits[pos]!
        let child := payload.cell.refs[if swBit then 1 else 0]!
        go child (nRem - 1) (m - 1) (pos + 1) loaded

      go rootCell n keyLen 0 #[]

private partial def pfxSetGenAuxWithCells (root : Option Cell) (key : BitString) (n : Nat)
    (storeVal : Builder → Except Excno Builder) (mode : DictSetMode) :
    Except Excno (Option Cell × Bool × Nat × Array Cell) := do
  let m : Nat := key.size
  if m > n then
    return (root, false, 0, #[])
  match root with
  | none =>
      if mode == .replace then
        return (none, false, 0, #[])
      let enc : BitString := dictLabelEncode key m n
      let b0 ← builderStoreBitsChecked Builder.empty enc
      let b1 ← builderStoreBitsChecked b0 #[false] -- leaf ctor = 0
      let b2 ← storeVal b1
      return (some b2.finalize, true, 1, #[])
  | some cell =>
      let lbl ← parseDictLabel cell n
      let labelBits : BitString := dictLabelBits lbl
      let l : Nat :=
        let keyPart := key.take (Nat.min m lbl.len)
        bitsCommonPrefixLen labelBits keyPart
      if l < lbl.len then
        if l = m || mode == .replace then
          return (some cell, false, 0, #[cell])

        -- Insert a new fork inside the current edge.
        let q : Nat := l + 1
        let newKey : BitString := key.extract q m
        let enc1 : BitString := dictLabelEncode newKey (m - q) (n - q)
        let b1 ← builderStoreBitsChecked Builder.empty enc1
        let b1 ← builderStoreBitsChecked b1 #[false]
        let b1 ← storeVal b1
        let cNew := b1.finalize

        let t : Nat := lbl.len - q
        let oldSuffix : BitString := labelBits.extract q lbl.len
        let payloadSlice : Slice := lbl.remainder.advanceBits lbl.storedBits
        let payloadCell : Cell := payloadSlice.toCellRemaining
        let enc2 : BitString := dictLabelEncode oldSuffix t (n - q)
        let b2 ← builderStoreBitsChecked Builder.empty enc2
        let b2 ← builderAppendCellChecked b2 payloadCell
        let cOld := b2.finalize

        let prefBits : BitString := key.take l
        let encF : BitString := dictLabelEncode prefBits l n
        let bF ← builderStoreBitsChecked Builder.empty encF
        let bF ← builderStoreBitsChecked bF #[true] -- fork ctor = 1
        let swBit : Bool := key[l]!
        let (left, right) := if swBit then (cOld, cNew) else (cNew, cOld)
        let bF ← builderStoreRefChecked bF left
        let bF ← builderStoreRefChecked bF right
        return (some bF.finalize, true, 3, #[cell])

      -- Label matches fully.
      let payload0 : Slice := lbl.remainder.advanceBits lbl.storedBits
      if !payload0.haveBits 1 then
        throw .dictErr
      let ctor : Bool := (payload0.readBits 1)[0]!
      let payload : Slice := { payload0 with bitPos := payload0.bitPos + 1 }
      let nRem : Nat := n - lbl.len
      let mRem : Nat := m - lbl.len
      if !ctor then
        -- Leaf
        if mRem != 0 || mode == .add then
          return (some cell, false, 0, #[cell])
        let enc : BitString := dictLabelEncode key m n
        let b0 ← builderStoreBitsChecked Builder.empty enc
        let b0 ← builderStoreBitsChecked b0 #[false]
        let b0 ← storeVal b0
        return (some b0.finalize, true, 1, #[cell])

      -- Fork
      if nRem = 0 then
        throw .dictErr
      if payload.bitsRemaining != 0 || payload.refsRemaining != 2 then
        throw .dictErr
      if mRem = 0 then
        return (some cell, false, 0, #[cell])
      let swBit : Bool := key[lbl.len]!
      let childKey : BitString := key.extract (lbl.len + 1) m
      let left0 := payload.cell.refs[0]!
      let right0 := payload.cell.refs[1]!
      if swBit then
        let (rightNew?, ok, createdChild, loadedChild) ←
          pfxSetGenAuxWithCells (some right0) childKey (nRem - 1) storeVal mode
        if !ok then
          return (some cell, false, 0, #[cell] ++ loadedChild)
        match rightNew? with
        | none => throw .dictErr
        | some rightNew =>
            let enc : BitString := dictLabelEncode (key.take lbl.len) lbl.len n
            let b ← builderStoreBitsChecked Builder.empty enc
            let b ← builderStoreBitsChecked b #[true]
            let b ← builderStoreRefChecked b left0
            let b ← builderStoreRefChecked b rightNew
            return (some b.finalize, true, createdChild + 1, #[cell] ++ loadedChild)
      else
        let (leftNew?, ok, createdChild, loadedChild) ←
          pfxSetGenAuxWithCells (some left0) childKey (nRem - 1) storeVal mode
        if !ok then
          return (some cell, false, 0, #[cell] ++ loadedChild)
        match leftNew? with
        | none => throw .dictErr
        | some leftNew =>
            let enc : BitString := dictLabelEncode (key.take lbl.len) lbl.len n
            let b ← builderStoreBitsChecked Builder.empty enc
            let b ← builderStoreBitsChecked b #[true]
            let b ← builderStoreRefChecked b leftNew
            let b ← builderStoreRefChecked b right0
            return (some b.finalize, true, createdChild + 1, #[cell] ++ loadedChild)

private partial def pfxLookupDeleteWithCells (root : Option Cell) (key : BitString) (n : Nat) :
    Except Excno (Option Slice × Option Cell × Nat × Array Cell) := do
  let m : Nat := key.size
  match root with
  | none => return (none, none, 0, #[])
  | some cell =>
      let lbl ← parseDictLabel cell n
      let labelBits : BitString := dictLabelBits lbl
      let l : Nat :=
        let keyPart := key.take (Nat.min m lbl.len)
        bitsCommonPrefixLen labelBits keyPart
      if l < lbl.len then
        return (none, some cell, 0, #[cell])
      let payload0 : Slice := lbl.remainder.advanceBits lbl.storedBits
      if !payload0.haveBits 1 then
        throw .dictErr
      let ctor : Bool := (payload0.readBits 1)[0]!
      let payload : Slice := { payload0 with bitPos := payload0.bitPos + 1 }
      if !ctor then
        if lbl.len < m then
          return (none, some cell, 0, #[cell])
        return (some payload, none, 0, #[cell])
      -- Fork
      if payload.bitsRemaining != 0 || payload.refsRemaining != 2 then
        throw .dictErr
      if lbl.len = m then
        return (none, some cell, 0, #[cell])
      let swBit : Bool := key[lbl.len]!
      let childKey : BitString := key.extract (lbl.len + 1) m
      let left0 := payload.cell.refs[0]!
      let right0 := payload.cell.refs[1]!
      let child0 := if swBit then right0 else left0
      let (oldVal?, childNew?, createdChild, loadedChild) ←
        pfxLookupDeleteWithCells (some child0) childKey (n - lbl.len - 1)
      match oldVal? with
      | none =>
          return (none, some cell, 0, #[cell] ++ loadedChild)
      | some oldVal =>
          match childNew? with
          | some childNew =>
              -- Both children present: rebuild fork with updated child.
              let newRefs : Array Cell := if swBit then #[left0, childNew] else #[childNew, right0]
              let newCell : Cell := Cell.mkOrdinary cell.bits newRefs
              return (some oldVal, some newCell, createdChild + 1, #[cell] ++ loadedChild)
          | none =>
              -- One child removed: merge current edge with the surviving child.
              let survivorBit : Bool := !swBit
              let survivor : Cell := if swBit then left0 else right0
              let childN : Nat := n - lbl.len - 1
              let lbl2 ← parseDictLabel survivor childN
              let childLabelBits : BitString := dictLabelBits lbl2
              let combinedLabelBits : BitString := dictLabelBits lbl ++ #[survivorBit] ++ childLabelBits
              let combinedLen : Nat := lbl.len + 1 + lbl2.len
              let enc : BitString := dictLabelEncode combinedLabelBits combinedLen n
              let payload2 : Slice := lbl2.remainder.advanceBits lbl2.storedBits
              let payloadCell2 : Cell := payload2.toCellRemaining
              let b0 ← builderStoreBitsChecked Builder.empty enc
              let b1 ← builderAppendCellChecked b0 payloadCell2
              return (some oldVal, some b1.finalize, createdChild + 1, #[cell] ++ loadedChild ++ #[survivor])

end DictExt

set_option maxHeartbeats 1000000 in
def execInstrDictExt (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .dictExt op =>
      match op with
      | .lddicts preload =>
          let s ← VM.popSlice
          if !s.haveBits 1 then
            throw .cellUnd
          let present : Bool := (s.readBits 1)[0]!
          let refs : Nat := if present then 1 else 0
          if !s.haveRefs refs then
            throw .cellUnd
          let stop : Slice := { s with bitPos := s.bitPos + 1, refPos := s.refPos + refs }
          let dictCell : Cell := Slice.prefixCell s stop
          VM.push (.slice (Slice.ofCell dictCell))
          if !preload then
            VM.push (.slice stop)

      | .mutGet intKey unsigned byRef mode =>
          VM.checkUnderflow (if mode == .del then 3 else 4)
          let n ← VM.popNatUpTo 1023
          let dictCell? ← VM.popMaybeCell
          let keyBits? : Option BitString ←
            if mode == .del then
              if intKey then
                let idxVal ← VM.popInt
                match idxVal with
                | .nan => throw .rangeChk
                | .num idx =>
                    match dictKeyBits? idx n unsigned with
                    | some bs => pure (some bs)
                    | none => throw .rangeChk
              else
                let keySlice ← VM.popSlice
                if keySlice.haveBits n then
                  pure (some (keySlice.readBits n))
                else
                  throw .cellUnd
            else
              if intKey then
                let idxVal ← VM.popInt
                match idxVal with
                | .nan => throw .rangeChk
                | .num idx =>
                    match dictKeyBits? idx n unsigned with
                    | some bs => pure (some bs)
                    | none => throw .rangeChk
              else
                let keySlice ← VM.popSlice
                if keySlice.haveBits n then
                  pure (some (keySlice.readBits n))
                else
                  pure none

          let okFlagFor (setMode : DictSetMode) : Bool := setMode != .add

          match mode with
          | .del =>
              let keyBits ←
                match keyBits? with
                | some bs => pure bs
                | none => throw .cellUnd
              if byRef then
                DictExt.prechargeRootLoad dictCell?
                match dictDeleteWithCells dictCell? keyBits with
                | .error e =>
                    let loaded := DictExt.loadedWithoutRoot dictCell? (dictDeleteVisitedCells dictCell? keyBits)
                    DictExt.registerLoaded loaded
                    throw e
                | .ok (oldVal?, newRoot?, created, loaded) =>
                    let loaded := DictExt.loadedWithoutRoot dictCell? loaded
                    DictExt.registerLoaded loaded
                    DictExt.consumeCreatedGas created
                    DictExt.pushDictRoot newRoot?
                    match oldVal? with
                    | none =>
                        DictExt.pushBool false
                    | some oldVal =>
                        let c ← DictExt.extractRefOrThrow oldVal
                        VM.push (.cell c)
                        DictExt.pushBool true
              else
                DictExt.prechargeRootLoad dictCell?
                match dictDeleteWithCells dictCell? keyBits with
                | .error e =>
                    let loaded := DictExt.loadedWithoutRoot dictCell? (dictDeleteVisitedCells dictCell? keyBits)
                    DictExt.registerLoaded loaded
                    throw e
                | .ok (oldVal?, newRoot?, created, loaded) =>
                    let loaded := DictExt.loadedWithoutRoot dictCell? loaded
                    DictExt.registerLoaded loaded
                    DictExt.consumeCreatedGas created
                    DictExt.pushDictRoot newRoot?
                    match oldVal? with
                    | none =>
                        DictExt.pushBool false
                    | some oldVal =>
                        VM.push (.slice oldVal)
                        DictExt.pushBool true

          | .set | .replace | .add =>
              let setMode : DictSetMode :=
                match mode with
                | .set => .set
                | .replace => .replace
                | .add => .add
                | .del => .set
              let ok_f : Bool := okFlagFor setMode
              if byRef then
                let newValueRef ← VM.popCell
                let keyBits ←
                  match keyBits? with
                  | some bs => pure bs
                  | none => throw .cellUnd
                DictExt.prechargeRootLoad dictCell?
                match dictLookupSetRefWithCells dictCell? keyBits newValueRef setMode with
                | .error e =>
                    let loaded := DictExt.loadedWithoutRoot dictCell? (dictLookupVisitedCells dictCell? keyBits)
                    DictExt.registerLoaded loaded
                    throw e
                | .ok (oldVal?, newRoot?, _ok, created, loaded) =>
                    let loaded := DictExt.loadedWithoutRoot dictCell? loaded
                    DictExt.registerLoaded loaded
                    DictExt.consumeCreatedGas created
                    DictExt.pushDictRoot newRoot?
                    match oldVal? with
                    | some oldVal =>
                        let c ← DictExt.extractRefOrThrow oldVal
                        VM.push (.cell c)
                        DictExt.pushBool ok_f
                    | none =>
                        DictExt.pushBool (!ok_f)
              else
                let newValue ← VM.popSlice
                let keyBits ←
                  match keyBits? with
                  | some bs => pure bs
                  | none => throw .cellUnd
                DictExt.prechargeRootLoad dictCell?
                match dictLookupSetSliceWithCells dictCell? keyBits newValue setMode with
                | .error e =>
                    let loaded := DictExt.loadedWithoutRoot dictCell? (dictLookupVisitedCells dictCell? keyBits)
                    DictExt.registerLoaded loaded
                    throw e
                | .ok (oldVal?, newRoot?, _ok, created, loaded) =>
                    let loaded := DictExt.loadedWithoutRoot dictCell? loaded
                    DictExt.registerLoaded loaded
                    DictExt.consumeCreatedGas created
                    DictExt.pushDictRoot newRoot?
                    match oldVal? with
                    | some oldVal =>
                        VM.push (.slice oldVal)
                        DictExt.pushBool ok_f
                    | none =>
                        DictExt.pushBool (!ok_f)

      | .mutGetB intKey unsigned mode =>
          VM.checkUnderflow 4
          let n ← VM.popNatUpTo 1023
          let dictCell? ← VM.popMaybeCell
          let keyBits? : Option BitString ←
            if intKey then
              let idxVal ← VM.popInt
              match idxVal with
              | .nan => throw .rangeChk
              | .num idx =>
                  match dictKeyBits? idx n unsigned with
                  | some bs => pure (some bs)
                  | none => throw .rangeChk
            else
              let keySlice ← VM.popSlice
              if keySlice.haveBits n then
                pure (some (keySlice.readBits n))
              else
                pure none
          let newValue ← VM.popBuilder
          let keyBits ←
            match keyBits? with
            | some bs => pure bs
            | none => throw .cellUnd
          let ok_f : Bool := mode != .add
          DictExt.prechargeRootLoad dictCell?
          match dictLookupSetBuilderWithCells dictCell? keyBits newValue mode with
          | .error e =>
              let loaded := DictExt.loadedWithoutRoot dictCell? (dictLookupVisitedCells dictCell? keyBits)
              DictExt.registerLoaded loaded
              throw e
          | .ok (oldVal?, newRoot?, _ok, created, loaded) =>
              let loaded := DictExt.loadedWithoutRoot dictCell? loaded
              DictExt.registerLoaded loaded
              DictExt.consumeCreatedGas created
              DictExt.pushDictRoot newRoot?
              match oldVal? with
              | some oldVal =>
                  VM.push (.slice oldVal)
                  DictExt.pushBool ok_f
              | none =>
                  DictExt.pushBool (!ok_f)

      | .del intKey unsigned =>
          VM.checkUnderflow 3
          let n ← VM.popNatUpTo 1023
          let dictCell? ← VM.popMaybeCell
          let keyBits? : Option BitString ←
            if intKey then
              let idx ← VM.popIntFinite
              pure (dictKeyBits? idx n unsigned)
            else
              let keySlice ← VM.popSlice
              if keySlice.haveBits n then
                pure (some (keySlice.readBits n))
              else
                throw .cellUnd
          match keyBits? with
          | none =>
              -- Matches TON `exec_dict_delete`: out-of-range integer key throws range_chk (no quiet mode).
              throw .rangeChk
          | some keyBits =>
              DictExt.prechargeRootLoad dictCell?
              match dictDeleteWithCells dictCell? keyBits with
              | .error e =>
                  let loaded := DictExt.loadedWithoutRoot dictCell? (dictDeleteVisitedCells dictCell? keyBits)
                  DictExt.registerLoaded loaded
                  throw e
              | .ok (oldVal?, newRoot?, created, loaded) =>
                  let loaded := DictExt.loadedWithoutRoot dictCell? loaded
                  DictExt.registerLoaded loaded
                  DictExt.consumeCreatedGas created
                  DictExt.pushDictRoot newRoot?
                  DictExt.pushBool (oldVal?.isSome)

      | .getOptRef intKey unsigned =>
          VM.checkUnderflow 3
          let n ← VM.popNatUpTo 1023
          let dictCell? ← VM.popMaybeCell
          let keyBits? : Option BitString ←
            if intKey then
              let idx ← VM.popIntFinite
              pure (dictKeyBits? idx n unsigned)
            else
              let keySlice ← VM.popSlice
              if keySlice.haveBits n then
                pure (some (keySlice.readBits n))
              else
                throw .cellUnd
          match keyBits? with
          | none =>
              VM.push .null
          | some keyBits =>
              DictExt.prechargeRootLoad dictCell?
              match dictLookupWithCells dictCell? keyBits with
              | .error e =>
                  let loaded := DictExt.loadedWithoutRoot dictCell? (dictLookupVisitedCells dictCell? keyBits)
                  DictExt.registerLoaded loaded
                  throw e
              | .ok (none, loaded) =>
                  let loaded := DictExt.loadedWithoutRoot dictCell? loaded
                  DictExt.registerLoaded loaded
                  VM.push .null
              | .ok (some valueSlice, loaded) =>
                  let loaded := DictExt.loadedWithoutRoot dictCell? loaded
                  DictExt.registerLoaded loaded
                  let c ← DictExt.extractRefOrThrow valueSlice
                  VM.push (.cell c)

      | .setGetOptRef intKey unsigned =>
          VM.checkUnderflow 4
          let n ← VM.popNatUpTo 1023
          let dictCell? ← VM.popMaybeCell
          let keyBits? : Option BitString ←
            if intKey then
              let idxVal ← VM.popInt
              match idxVal with
              | .nan => throw .rangeChk
              | .num idx =>
                  match dictKeyBits? idx n unsigned with
                  | some bs => pure (some bs)
                  | none => throw .rangeChk
            else
              let keySlice ← VM.popSlice
              if keySlice.haveBits n then
                pure (some (keySlice.readBits n))
              else
                pure none
          let newValue? ← VM.popMaybeCell
          let keyBits : BitString ←
            match keyBits? with
            | some bs => pure bs
            | none => throw .cellUnd
          match newValue? with
          | some newValue =>
              DictExt.prechargeRootLoad dictCell?
              match dictLookupSetRefWithCells dictCell? keyBits newValue .set with
              | .error e =>
                  let loaded := DictExt.loadedWithoutRoot dictCell? (dictLookupVisitedCells dictCell? keyBits)
                  DictExt.registerLoaded loaded
                  throw e
              | .ok (oldVal?, newRoot?, _ok, created, loaded) =>
                  let loaded := DictExt.loadedWithoutRoot dictCell? loaded
                  DictExt.registerLoaded loaded
                  DictExt.consumeCreatedGas created
                  DictExt.pushDictRoot newRoot?
                  match oldVal? with
                  | none => VM.push .null
                  | some oldVal =>
                      let c ← DictExt.extractRefOrThrow oldVal
                      VM.push (.cell c)
          | none =>
              DictExt.prechargeRootLoad dictCell?
              match dictDeleteWithCells dictCell? keyBits with
              | .error e =>
                  let loaded := DictExt.loadedWithoutRoot dictCell? (dictLookupVisitedCells dictCell? keyBits)
                  DictExt.registerLoaded loaded
                  throw e
              | .ok (oldVal?, newRoot?, created, loaded) =>
                  let loaded := DictExt.loadedWithoutRoot dictCell? loaded
                  DictExt.registerLoaded loaded
                  DictExt.consumeCreatedGas created
                  DictExt.pushDictRoot newRoot?
                  match oldVal? with
                  | none => VM.push .null
                  | some oldVal =>
                      let c ← DictExt.extractRefOrThrow oldVal
                      VM.push (.cell c)

      | .subdictGet intKey unsigned rp =>
          VM.checkUnderflow 4
          let n ← VM.popNatUpTo 1023
          let dictCell? ← VM.popMaybeCell
          let mk : Nat := if intKey then (if unsigned then 256 else 257) else 1023
          let k ← VM.popNatUpTo (Nat.min mk n)
          let prefixBits : BitString ←
            if intKey then
              let idx ← VM.popIntFinite
              match dictKeyBits? idx k unsigned with
              | some bs => pure bs
              | none => throw .cellUnd
          else
            let keySlice ← VM.popSlice
            if keySlice.haveBits k then
              pure (keySlice.readBits k)
            else
              throw .cellUnd
          if k > 0 then
            DictExt.prechargeRootLoad dictCell?
          match dictExtractPrefixSubdictWithCells dictCell? n prefixBits k rp with
          -- Most SUBDICT* cases propagate `cell_und`, but signed-int RP extraction
          -- can surface `dict_err` from C++ `cut_prefix_subdict()` for malformed tries.
          | .error .cellUnd =>
              if intKey && !unsigned && rp then
                throw .dictErr
              else
                throw .cellUnd
          | .error e => throw e
          | .ok (newRoot?, _changed, created, loaded) =>
              let loaded :=
                if k > 0 then
                  DictExt.loadedWithoutRoot dictCell? loaded
                else
                  loaded
              DictExt.registerLoaded loaded
              DictExt.consumeCreatedGas created
              DictExt.pushDictRoot newRoot?

      | .pfxSet mode =>
          VM.checkUnderflow 4
          let n ← VM.popNatUpTo 1023
          let dictCell? ← VM.popMaybeCell
          let keySlice ← VM.popSlice
          let newValue ← VM.popSlice
          let keyBits : BitString := keySlice.readBits keySlice.bitsRemaining
          if keyBits.size > n then
            DictExt.pushDictRoot dictCell?
            DictExt.pushBool false
          else
            DictExt.prechargeRootLoad dictCell?
            let storeVal : Builder → Except Excno Builder :=
              fun b => builderAppendCellChecked b newValue.toCellRemaining
            match DictExt.pfxSetGenAuxWithCells dictCell? keyBits n storeVal mode with
            | .error e => throw e
            | .ok (newRoot?, ok, created, loaded0) =>
                let loaded := DictExt.loadedWithoutRoot dictCell? loaded0
                DictExt.registerLoaded loaded
                DictExt.consumeCreatedGas created
                DictExt.pushDictRoot newRoot?
                DictExt.pushBool ok

      | .pfxDel =>
          VM.checkUnderflow 3
          let n ← VM.popNatUpTo 1023
          let dictCell? ← VM.popMaybeCell
          let keySlice ← VM.popSlice
          let keyBits : BitString := keySlice.readBits keySlice.bitsRemaining
          if keyBits.size > n then
            DictExt.pushDictRoot dictCell?
            DictExt.pushBool false
          else
            DictExt.prechargeRootLoad dictCell?
            match DictExt.pfxLookupDeleteWithCells dictCell? keyBits n with
            | .error e => throw e
            | .ok (oldVal?, newRoot?, created, loaded0) =>
                let loaded := DictExt.loadedWithoutRoot dictCell? loaded0
                DictExt.registerLoaded loaded
                DictExt.consumeCreatedGas created
                let ok := oldVal?.isSome
                -- Update root only if deletion succeeded.
                let outRoot? := if ok then newRoot? else dictCell?
                DictExt.pushDictRoot outRoot?
                DictExt.pushBool ok

      | .pfxGet kind =>
          VM.checkUnderflow 3
          let n ← VM.popNatUpTo 1023
          let dictCell? ← VM.popMaybeCell
          let cs0 ← VM.popSlice
          DictExt.prechargeRootLoad dictCell?
          let keyBits : BitString := cs0.readBits cs0.bitsRemaining
          match DictExt.pfxLookupPrefixWithCells dictCell? keyBits keyBits.size n with
          | .error e => throw e
          | .ok (none, _pos, loaded) =>
              -- Not found / cannot parse.
              let loaded :=
                match dictCell? with
                | none => loaded
                | some root => loaded.filter (fun c => c != root)
              DictExt.registerLoaded loaded
              match kind with
              | .get | .getExec =>
                  throw .cellUnd
              | .getQ =>
                  VM.push (.slice cs0)
                  DictExt.pushBool false
              | .getJmp =>
                  VM.push (.slice cs0)
          | .ok (some valueSlice, pfxLen, loaded0) =>
              let loaded :=
                match dictCell? with
                | none => loaded0
                | some root => loaded0.filter (fun c => c != root)
              DictExt.registerLoaded loaded
              let (pfxSlice, cs1) ←
                match DictExt.slicePrefix cs0 pfxLen 0 with
                | .ok x => pure x
                | .error e => throw e
              VM.push (.slice pfxSlice)
              match kind with
              | .getQ | .get =>
                  VM.push (.slice valueSlice)
              | .getJmp | .getExec =>
                  pure ()
              VM.push (.slice cs1)
              match kind with
              | .getQ =>
                  DictExt.pushBool true
              | .get =>
                  pure ()
              | .getJmp | .getExec =>
                  let cont : Continuation := .ordinary valueSlice (.quit 0) OrdCregs.empty OrdCdata.empty
                  modify fun st =>
                    match kind with
                    | .getExec => st.callTo cont
                    | _ => st.jumpTo cont

      | .pfxSwitch dictCell keyLen =>
          let cs0 ← VM.popSlice
          VM.registerCellLoad dictCell
          let keyBits : BitString := cs0.readBits cs0.bitsRemaining
          match DictExt.pfxLookupPrefixWithCells (some dictCell) keyBits keyBits.size keyLen with
          | .error e => throw e
          | .ok (none, _pos, loaded) =>
              DictExt.registerLoaded loaded
              VM.push (.slice cs0)
          | .ok (some valueSlice, pfxLen, loaded0) =>
              let loaded := loaded0
              DictExt.registerLoaded loaded
              let (pfxSlice, cs1) ←
                match DictExt.slicePrefix cs0 pfxLen 0 with
                | .ok x => pure x
                | .error e => throw e
              VM.push (.slice pfxSlice)
              VM.push (.slice cs1)
              let cont : Continuation := .ordinary valueSlice (.quit 0) OrdCregs.empty OrdCdata.empty
              modify fun st => st.jumpTo cont
  | _ => next

end TvmLean
