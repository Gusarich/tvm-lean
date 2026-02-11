import TvmLean.Semantics.Exec.Common
import TvmLean.Semantics.Exec.TonEnv.GetParamAliases

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrTonEnvGetExtraBalance (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .tonEnvOp .getExtraBalance =>
      -- Mirrors C++ `exec_get_extra_currency_balance` (tonops.cpp).
      let id : Nat ← VM.popNatUpTo ((1 <<< 32) - 1)

      -- Read balance tuple from c7 params[7].
      VM.pushC7Param 7
      let balanceVal ← VM.pop
      let balanceTuple : Array Value ←
        match balanceVal with
        | .tuple t => pure t
        | _ => throw .typeChk

      -- dict_root := balance[1]; allow missing -> null (like C++ tuple_index default).
      let dictRootVal : Value := if 1 < balanceTuple.size then balanceTuple[1]! else .null
      let dictRoot? : Option Cell ←
        match dictRootVal with
        | .cell c => pure (some c)
        | .null => pure none
        | _ => throw .typeChk

      let keyBits : BitString := natToBits id 32
      match dictLookupWithCells dictRoot? keyBits with
      | .error e =>
          throw e
      | .ok (none, loaded) =>
          for c in loaded do
            VM.registerCellLoad c
          VM.pushSmallInt 0
      | .ok (some cs, loaded) =>
          for c in loaded do
            VM.registerCellLoad c
          -- Parse `VarUInteger 32`-like: len_bits=5, unsigned, quiet=false.
          let (lenBytes, s1) ← cs.takeBitsAsNatCellUnd 5
          let dataBits : Nat := lenBytes * 8
          let (n, _s2) ← s1.takeBitsAsNatCellUnd dataBits
          VM.pushIntQuiet (.num (Int.ofNat n)) false
  | _ => next

end TvmLean
