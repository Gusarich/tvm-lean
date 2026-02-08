import TvmLean.Model

namespace TvmLean

def bytesHex (bs : Array UInt8) : String :=
  let hexDigit (n : Nat) : Char :=
    if n < 10 then
      Char.ofNat ('0'.toNat + n)
    else
      Char.ofNat ('a'.toNat + (n - 10))
  let byteHex (b : UInt8) : String :=
    let n := b.toNat
    String.singleton (hexDigit (n / 16)) ++ String.singleton (hexDigit (n % 16))
  String.intercalate "" (bs.toList.map byteHex)

def canonContTy : Continuation → String
  | .ordinary .. => "vmc_std"
  | .envelope .. => "vmc_envelope"
  | .quit _ => "vmc_quit"
  | .excQuit => "vmc_quit_exc"
  | .whileCond .. => "vmc_while_cond"
  | .whileBody .. => "vmc_while_body"
  | .untilBody .. => "vmc_until"
  | .repeatBody .. => "vmc_repeat"
  | .againBody .. => "vmc_again"

partial def canonValue (v : Value) : String :=
  match v with
  | .null => "null"
  | .int .nan => "nan"
  | .int (.num n) => s!"int:{n}"
  | .cell c => s!"cell:{bytesHex (Cell.hashBytes c)}"
  | .slice s => s!"slice:{bytesHex (Cell.hashBytes s.toCellRemaining)}"
  | .builder b => s!"builder:{bytesHex (Cell.hashBytes b.finalize)}"
  | .tuple t =>
      let inner := String.intercalate "," (t.toList.map canonValue)
      "tuple[" ++ toString t.size ++ "]{" ++ inner ++ "}"
  | .cont k => "cont:Cont{" ++ canonContTy k ++ "}"

partial def valueEqNormalized : Value → Value → Bool
  | .null, .null => true
  | .int x, .int y => x == y
  | .cell x, .cell y => x == y
  | .builder x, .builder y => x == y
  | .cont x, .cont y => x == y
  | .slice x, .slice y => x.toCellRemaining == y.toCellRemaining
  | .tuple x, .tuple y =>
      if x.size != y.size then
        false
      else
        Id.run do
          let mut ok := true
          for i in [0:x.size] do
            if ok then
              ok := valueEqNormalized x[i]! y[i]!
          return ok
  | _, _ => false

partial def firstValueMismatch (expected actual : Value) : Option (List Nat × Value × Value) :=
  if valueEqNormalized expected actual then
    none
  else
    match expected, actual with
    | .tuple e, .tuple a =>
        if e.size != a.size then
          some ([], expected, actual)
        else
          Id.run do
            for i in [0:e.size] do
              let ev := e[i]!
              let av := a[i]!
              if !valueEqNormalized ev av then
                match firstValueMismatch ev av with
                | some (path, leafE, leafA) => return some (i :: path, leafE, leafA)
                | none => return some ([i], ev, av)
            return some ([], expected, actual)
    | _, _ =>
        some ([], expected, actual)


end TvmLean
