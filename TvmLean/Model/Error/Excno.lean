import Std

namespace TvmLean

inductive Excno : Type
  | none
  | alt
  | stkUnd
  | stkOv
  | intOv
  | rangeChk
  | invOpcode
  | typeChk
  | cellOv
  | cellUnd
  | dictErr
  | unknown
  | unimplemented
  | fatal
  | outOfGas
  | virtErr
  deriving DecidableEq, Repr, Inhabited

def Excno.toInt : Excno → Int
  | .none => 0
  | .alt => 1
  | .stkUnd => 2
  | .stkOv => 3
  | .intOv => 4
  | .rangeChk => 5
  | .invOpcode => 6
  | .typeChk => 7
  | .cellOv => 8
  | .cellUnd => 9
  | .dictErr => 10
  | .unknown => 11
  | .fatal => 12
  | .outOfGas => 13
  | .virtErr => 14
  | .unimplemented => 15

instance : ToString Excno := ⟨fun
  | .none => "none"
  | .alt => "alt"
  | .stkUnd => "stkUnd"
  | .stkOv => "stkOv"
  | .intOv => "intOv"
  | .rangeChk => "rangeChk"
  | .invOpcode => "invOpcode"
  | .typeChk => "typeChk"
  | .cellOv => "cellOv"
  | .cellUnd => "cellUnd"
  | .dictErr => "dictErr"
  | .unknown => "unknown"
  | .unimplemented => "unimplemented"
  | .fatal => "fatal"
  | .outOfGas => "outOfGas"
  | .virtErr => "virtErr"⟩

end TvmLean
