import TvmLean.Model.Cont.Continuation

namespace TvmLean

instance : Inhabited Value := ⟨.null⟩

def Value.pretty : Value → String
  | .int .nan => "NaN"
  | .int (.num n) => toString n
  | .null => "null"
  | .cell _ => "<cell>"
  | .slice _ => "<slice>"
  | .builder _ => "<builder>"
  | .tuple t => s!"<tuple:{t.size}>"
  | .cont k =>
      match k with
      | .ordinary _ _ _ _ => "<cont:ord>"
      | .envelope _ _ _ => "<cont:env>"
      | .quit n => s!"<cont:quit {n}>"
      | .excQuit => "<cont:excquit>"
      | .whileCond _ _ _ => "<cont:while-cond>"
      | .whileBody _ _ _ => "<cont:while-body>"
      | .untilBody _ _ => "<cont:until-body>"
      | .repeatBody _ _ _ => "<cont:repeat-body>"
      | .againBody _ => "<cont:again-body>"

instance : ToString Value := ⟨Value.pretty⟩

def arrayBeqBy {α : Type} (a b : Array α) (beq : α → α → Bool) : Bool :=
  if a.size != b.size then
    false
  else
    Id.run do
      let mut ok := true
      for i in [0:a.size] do
        match a.get? i, b.get? i with
        | some x, some y =>
            if !(beq x y) then
              ok := false
        | _, _ =>
            ok := false
      return ok

def arrayBeq {α : Type} [BEq α] (a b : Array α) : Bool :=
  arrayBeqBy a b (fun x y => x == y)

partial def Value.beq : Value → Value → Bool
  | .null, .null => true
  | .int x, .int y => x == y
  | .cell x, .cell y => x == y
  | .slice x, .slice y => x == y
  | .builder x, .builder y => x == y
  | .tuple x, .tuple y => arrayBeqBy x y Value.beq
  | .cont x, .cont y => x == y
  | _, _ => false

instance : BEq Value := ⟨Value.beq⟩

end TvmLean
