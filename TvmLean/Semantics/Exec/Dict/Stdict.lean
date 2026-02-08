import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrDictStdict (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .stdict =>
      VM.checkUnderflow 2
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
  | _ => next

end TvmLean
