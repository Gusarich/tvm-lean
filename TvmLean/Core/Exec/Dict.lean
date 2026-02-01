import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrDict (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .stdict =>
      -- Builder is on top, dict root cell (or null) below.
      let b ← VM.popBuilder
      let d? ← VM.popMaybeCell
      let hasRef : Bool := d?.isSome
      let needRefs : Nat := if hasRef then 1 else 0
      if !b.canExtendBy 1 needRefs then
        throw .cellOv
      let b1 := b.storeBits #[hasRef]
      let b2 :=
        match d? with
        | some c => { b1 with refs := b1.refs.push c }
        | none => b1
      VM.push (.builder b2)
  | .skipdict =>
      let s ← VM.popSlice
      if !s.haveBits 1 then
        throw .cellUnd
      let present : Bool := (s.readBits 1)[0]!
      let needRefs : Nat := if present then 1 else 0
      if !s.haveRefs needRefs then
        throw .cellUnd
      VM.push (.slice { s with bitPos := s.bitPos + 1, refPos := s.refPos + needRefs })
  | .dictPushConst dict keyBits =>
      VM.push (.cell dict)
      VM.pushSmallInt (Int.ofNat keyBits)
  | .dictGet intKey unsigned byRef =>
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
          -- Dictionary index out of bounds: behave like "not found".
          VM.pushSmallInt 0
      | some keyBits =>
          match dictLookupWithCells dictCell? keyBits with
          | .error e =>
              throw e
          | .ok (none, loaded) =>
              for c in loaded do
                modify fun st => st.registerCellLoad c
              VM.pushSmallInt 0
          | .ok (some valueSlice, loaded) =>
              for c in loaded do
                modify fun st => st.registerCellLoad c
              if byRef then
                if valueSlice.bitsRemaining == 0 && valueSlice.refsRemaining == 1 then
                  let c := valueSlice.cell.refs[valueSlice.refPos]!
                  VM.push (.cell c)
                  VM.pushSmallInt (-1)
                else
                  throw .dictErr
              else
                VM.push (.slice valueSlice)
                VM.pushSmallInt (-1)
  | .dictGetNear args4 =>
      -- Matches C++ `exec_dict_getnear` (dictops.cpp).
      let allowEq : Bool := (args4 &&& 1) = 1
      let goUp : Bool := (args4 &&& 2) = 0
      let intKey : Bool := (args4 &&& 8) = 8
      let unsigned : Bool := intKey && ((args4 &&& 4) = 4)
      let sgnd : Bool := intKey && !unsigned
      let maxN : Nat := if intKey then (if unsigned then 256 else 257) else 1023
      let n ← VM.popNatUpTo maxN
      let dictCell? ← VM.popMaybeCell
      if intKey then
        let key ← VM.popIntFinite
        let mut res : Except Excno (Option (Slice × BitString) × Array Cell) := do
          match dictKeyBits? key n unsigned with
          | some hintBits =>
              dictNearestWithCells dictCell? hintBits goUp allowEq sgnd
          | none =>
              let cond : Bool := (decide (0 ≤ key)) != goUp
              if cond then
                dictMinMaxWithCells dictCell? n (!goUp) sgnd
              else
                return (none, #[])
        match res with
        | .error e => throw e
        | .ok (none, loaded) =>
            for c in loaded do
              modify fun st => st.registerCellLoad c
            VM.pushSmallInt 0
        | .ok (some (val, keyBits), loaded) =>
            for c in loaded do
              modify fun st => st.registerCellLoad c
            VM.push (.slice val)
            let keyOut : Int :=
              if sgnd then
                bitsToIntSignedTwos keyBits
              else
                Int.ofNat (bitsToNat keyBits)
            VM.pushIntQuiet (.num keyOut) false
            VM.pushSmallInt (-1)
      else
        let keyHint ← VM.popSlice
        if !keyHint.haveBits n then
          throw .cellUnd
        let hintBits : BitString := keyHint.readBits n
        match dictNearestWithCells dictCell? hintBits goUp allowEq false with
        | .error e => throw e
        | .ok (none, loaded) =>
            for c in loaded do
              modify fun st => st.registerCellLoad c
            VM.pushSmallInt 0
        | .ok (some (val, keyBits), loaded) =>
            for c in loaded do
              modify fun st => st.registerCellLoad c
            VM.push (.slice val)
            modify fun st => st.consumeGas cellCreateGasPrice
            let keyCell : Cell := Cell.mkOrdinary keyBits #[]
            VM.push (.slice (Slice.ofCell keyCell))
            VM.pushSmallInt (-1)
  | .dictGetMinMax args5 =>
      -- Matches C++ `exec_dict_getmin` (dictops.cpp).
      let byRef : Bool := (args5 &&& 1) = 1
      let unsigned : Bool := (args5 &&& 2) = 2
      let intKey : Bool := (args5 &&& 4) = 4
      let fetchMax : Bool := (args5 &&& 8) = 8
      let remove : Bool := (args5 &&& 16) = 16
      let invertFirst : Bool := !unsigned
      let maxN : Nat := if intKey then (if unsigned then 256 else 257) else 1023
      let n ← VM.popNatUpTo maxN
      let dictCell? ← VM.popMaybeCell
      match dictMinMaxWithCells dictCell? n fetchMax invertFirst with
      | .error e => throw e
      | .ok (none, loaded) =>
          for c in loaded do
            modify fun st => st.registerCellLoad c
          if remove then
            match dictCell? with
            | none => VM.push .null
            | some c => VM.push (.cell c)
          VM.pushSmallInt 0
      | .ok (some (val0, keyBits), loaded0) =>
          for c in loaded0 do
            modify fun st => st.registerCellLoad c
          let mut val := val0
          let mut dictOut? : Option Cell := dictCell?
          let mut created : Nat := 0
          let mut loaded1 : Array Cell := #[]
          if remove then
            match dictDeleteWithCells dictCell? keyBits with
            | .error e => throw e
            | .ok (oldVal?, newRoot?, created1, loadedDel) =>
                match oldVal? with
                | none => throw .dictErr
                | some oldVal =>
                    val := oldVal
                    dictOut? := newRoot?
                    created := created1
                    loaded1 := loadedDel
          for c in loaded1 do
            modify fun st => st.registerCellLoad c
          if created > 0 then
            modify fun st => st.consumeGas (cellCreateGasPrice * Int.ofNat created)

          if remove then
            match dictOut? with
            | none => VM.push .null
            | some c => VM.push (.cell c)

          if byRef then
            if val.bitsRemaining == 0 && val.refsRemaining == 1 then
              let c := val.cell.refs[val.refPos]!
              VM.push (.cell c)
            else
              throw .dictErr
          else
            VM.push (.slice val)

          if intKey then
            let keyOut : Int :=
              if invertFirst then
                bitsToIntSignedTwos keyBits
              else
                Int.ofNat (bitsToNat keyBits)
            VM.pushIntQuiet (.num keyOut) false
          else
            modify fun st => st.consumeGas cellCreateGasPrice
            let keyCell : Cell := Cell.mkOrdinary keyBits #[]
            VM.push (.slice (Slice.ofCell keyCell))

          VM.pushSmallInt (-1)
  | .dictSet intKey unsigned byRef mode =>
      let n ← VM.popNatUpTo 1023
      let dictCell? ← VM.popMaybeCell
      let keyBits : BitString ←
        if intKey then
          let idxVal ← VM.popInt
          match idxVal with
          | .nan => throw .rangeChk
          | .num idx =>
              match dictKeyBits? idx n unsigned with
              | some bs => pure bs
              | none => throw .rangeChk
        else
          let keySlice ← VM.popSlice
          if keySlice.haveBits n then
            pure (keySlice.readBits n)
          else
            throw .cellUnd

      if byRef then
        let valRef ← VM.popCell
        match dictSetRefWithCells dictCell? keyBits valRef mode with
        | .error e =>
            throw e
        | .ok (newRoot?, ok, created, loaded) =>
            for c in loaded do
              modify fun st => st.registerCellLoad c
            if created > 0 then
              modify fun st => st.consumeGas (cellCreateGasPrice * Int.ofNat created)
            match newRoot? with
            | none => VM.push .null
            | some c => VM.push (.cell c)
            if mode == .set then
              if !ok then
                throw .fatal
            else
              VM.pushSmallInt (if ok then -1 else 0)
      else
        let valSlice ← VM.popSlice
        match dictSetSliceWithCells dictCell? keyBits valSlice mode with
        | .error e =>
            throw e
        | .ok (newRoot?, ok, created, loaded) =>
            for c in loaded do
              modify fun st => st.registerCellLoad c
            if created > 0 then
              modify fun st => st.consumeGas (cellCreateGasPrice * Int.ofNat created)
            match newRoot? with
            | none => VM.push .null
            | some c => VM.push (.cell c)
            if mode == .set then
              if !ok then
                throw .fatal
            else
              VM.pushSmallInt (if ok then -1 else 0)
  | .dictSetB intKey unsigned mode =>
      let n ← VM.popNatUpTo 1023
      let dictCell? ← VM.popMaybeCell
      let keyBits : BitString ←
        if intKey then
          let idxVal ← VM.popInt
          match idxVal with
          | .nan => throw .rangeChk
          | .num idx =>
              match dictKeyBits? idx n unsigned with
              | some bs => pure bs
              | none => throw .rangeChk
        else
          let keySlice ← VM.popSlice
          if keySlice.haveBits n then
            pure (keySlice.readBits n)
          else
            throw .cellUnd
      let newVal ← VM.popBuilder
      match dictSetBuilderWithCells dictCell? keyBits newVal mode with
      | .error e =>
          throw e
      | .ok (newRoot?, ok, created, loaded) =>
          for c in loaded do
            modify fun st => st.registerCellLoad c
          if created > 0 then
            modify fun st => st.consumeGas (cellCreateGasPrice * Int.ofNat created)
          match newRoot? with
          | none => VM.push .null
          | some c => VM.push (.cell c)
          if mode == .set then
            if !ok then
              throw .fatal
          else
            VM.pushSmallInt (if ok then -1 else 0)
  | .dictReplaceB intKey unsigned =>
      let n ← VM.popNatUpTo 1023
      let dictCell? ← VM.popMaybeCell
      let keyBits : BitString ←
        if intKey then
          let idxVal ← VM.popInt
          match idxVal with
          | .nan => throw .rangeChk
          | .num idx =>
              match dictKeyBits? idx n unsigned with
              | some bs => pure bs
              | none => throw .rangeChk
        else
          let keySlice ← VM.popSlice
          if keySlice.haveBits n then
            pure (keySlice.readBits n)
          else
            throw .cellUnd
      let newVal ← VM.popBuilder
      match dictReplaceBuilderWithCells dictCell? keyBits newVal with
      | .error e =>
          throw e
      | .ok (newRoot?, ok, created, loaded) =>
          for c in loaded do
            modify fun st => st.registerCellLoad c
          if created > 0 then
            modify fun st => st.consumeGas (cellCreateGasPrice * Int.ofNat created)
          match newRoot? with
          | none => VM.push .null
          | some c => VM.push (.cell c)
          VM.pushSmallInt (if ok then -1 else 0)
  | .dictGetExec unsigned doCall pushZ =>
      let n ← VM.popNatUpTo 1023
      let dictCell? ← VM.popMaybeCell
      let idx ← VM.popIntFinite
      match dictKeyBits? idx n unsigned with
      | none =>
          if pushZ then
            VM.push (.int (.num idx))
          else
            pure ()
      | some keyBits =>
          match dictLookupWithCells dictCell? keyBits with
          | .error e =>
              throw e
          | .ok (res?, loaded) =>
              for c in loaded do
                modify fun st => st.registerCellLoad c
              match res? with
              | none =>
                  if pushZ then
                    VM.push (.int (.num idx))
                  else
                    pure ()
              | some valueSlice =>
                  let cont : Continuation := .ordinary valueSlice (.quit 0) OrdCregs.empty OrdCdata.empty
                  modify fun st =>
                    if doCall then
                      st.callTo cont
                    else
                      st.jumpTo cont
  | .lddict preload quiet =>
      let s ← VM.popSlice
      let ok : Bool :=
        if s.haveBits 1 then
          let present : Bool := (s.readBits 1)[0]!
          let needRefs : Nat := if present then 1 else 0
          s.haveRefs needRefs
        else
          false
      if !ok then
        if quiet then
          if !preload then
            VM.push (.slice s)
          VM.pushSmallInt 0
        else
          throw .cellUnd
      else
        let present : Bool := (s.readBits 1)[0]!
        let needRefs : Nat := if present then 1 else 0
        if present then
          let c := s.cell.refs[s.refPos]!
          VM.push (.cell c)
        else
          VM.push .null
        if !preload then
          let s' : Slice := { s with bitPos := s.bitPos + 1, refPos := s.refPos + needRefs }
          VM.push (.slice s')
        if quiet then
          VM.pushSmallInt (-1)
  | _ => next

end TvmLean
