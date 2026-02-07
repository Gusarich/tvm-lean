import TvmLean.Model.Cont.Cdata

namespace TvmLean

partial def Continuation.beq : Continuation → Continuation → Bool
  | .quit x, .quit y => x == y
  | .excQuit, .excQuit => true
  | .ordinary x sx _ _, .ordinary y sy _ _ => x == y && Continuation.beq sx sy
  | .envelope x _ _, .envelope y _ _ => Continuation.beq x y
  | .whileCond c1 b1 a1, .whileCond c2 b2 a2 =>
      Continuation.beq c1 c2 && Continuation.beq b1 b2 && Continuation.beq a1 a2
  | .whileBody c1 b1 a1, .whileBody c2 b2 a2 =>
      Continuation.beq c1 c2 && Continuation.beq b1 b2 && Continuation.beq a1 a2
  | .untilBody b1 a1, .untilBody b2 a2 =>
      Continuation.beq b1 b2 && Continuation.beq a1 a2
  | .repeatBody b1 a1 n1, .repeatBody b2 a2 n2 =>
      n1 == n2 && Continuation.beq b1 b2 && Continuation.beq a1 a2
  | .againBody b1, .againBody b2 =>
      Continuation.beq b1 b2
  | _, _ => false

instance : BEq Continuation := ⟨Continuation.beq⟩

def Continuation.hasC0 : Continuation → Bool
  | .ordinary _ _ cregs _ => cregs.c0.isSome
  | .envelope _ cregs _ => cregs.c0.isSome
  | _ => false

def Continuation.forceCdata : Continuation → Continuation
  | .ordinary code saved cregs cdata => .ordinary code saved cregs cdata
  | .envelope ext cregs cdata => .envelope ext cregs cdata
  | k => .envelope k OrdCregs.empty OrdCdata.empty

def Continuation.defineCtr (k : Continuation) (idx : Nat) (v : Value) : Except Excno Continuation := do
  let k := k.forceCdata
  match k with
  | .ordinary code saved cregs cdata =>
      let cregs ← cregs.defineFromValue idx v
      return .ordinary code saved cregs cdata
  | .envelope ext cregs cdata =>
      let cregs ← cregs.defineFromValue idx v
      return .envelope ext cregs cdata
  | _ =>
      -- unreachable (forceCdata makes it either .ordinary or .envelope)
      return k

def Continuation.defineC0 (k : Continuation) (c0 : Continuation) : Continuation :=
  let k := k.forceCdata
  match k with
  | .ordinary code saved cregs cdata =>
      let cregs := match cregs.c0 with | some _ => cregs | none => { cregs with c0 := some c0 }
      .ordinary code saved cregs cdata
  | .envelope ext cregs cdata =>
      let cregs := match cregs.c0 with | some _ => cregs | none => { cregs with c0 := some c0 }
      .envelope ext cregs cdata
  | _ =>
      k

def Continuation.defineC1 (k : Continuation) (c1 : Continuation) : Continuation :=
  let k := k.forceCdata
  match k with
  | .ordinary code saved cregs cdata =>
      let cregs := match cregs.c1 with | some _ => cregs | none => { cregs with c1 := some c1 }
      .ordinary code saved cregs cdata
  | .envelope ext cregs cdata =>
      let cregs := match cregs.c1 with | some _ => cregs | none => { cregs with c1 := some c1 }
      .envelope ext cregs cdata
  | _ =>
      k

def Continuation.defineC2 (k : Continuation) (c2 : Continuation) : Continuation :=
  let k := k.forceCdata
  match k with
  | .ordinary code saved cregs cdata =>
      let cregs := match cregs.c2 with | some _ => cregs | none => { cregs with c2 := some c2 }
      .ordinary code saved cregs cdata
  | .envelope ext cregs cdata =>
      let cregs := match cregs.c2 with | some _ => cregs | none => { cregs with c2 := some c2 }
      .envelope ext cregs cdata
  | _ =>
      k

end TvmLean
