import TvmLean.Model
import TvmLean.Semantics

namespace TvmLean

def refPathToString (pathRev : List Nat) : String :=
  let path := pathRev.reverse
  if path.isEmpty then
    "<root>"
  else
    String.intercalate "/" (path.map fun i => s!"refs[{i}]")

partial def firstBitDiff (a b : BitString) (i : Nat := 0) : Option Nat :=
  if i < a.size then
    if a[i]! != b[i]! then
      some i
    else
      firstBitDiff a b (i + 1)
  else
    none

partial def Cell.diff (a b : Cell) (pathRev : List Nat := []) : Option String :=
  if a.special != b.special then
    some s!"{refPathToString pathRev}: special differs (a={a.special} b={b.special})"
  else if a.levelMask != b.levelMask then
    some s!"{refPathToString pathRev}: levelMask differs (a={a.levelMask} b={b.levelMask})"
  else if a.bits.size != b.bits.size then
    some s!"{refPathToString pathRev}: bits.size differs (a={a.bits.size} b={b.bits.size})"
  else
    match firstBitDiff a.bits b.bits with
    | some i =>
        some s!"{refPathToString pathRev}: bits differ at {i} (a={a.bits[i]!} b={b.bits[i]!})"
    | none =>
        if a.refs.size != b.refs.size then
          some s!"{refPathToString pathRev}: refs.size differs (a={a.refs.size} b={b.refs.size})"
        else
          Id.run do
            let mut out : Option String := none
            for i in [0:a.refs.size] do
              if out.isNone then
                out := Cell.diff a.refs[i]! b.refs[i]! (i :: pathRev)
            out

