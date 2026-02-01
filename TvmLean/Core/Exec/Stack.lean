import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrStack (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .nop =>
      pure ()
  | .pushInt n =>
      VM.pushIntQuiet n false
  | .pushPow2 exp =>
      VM.pushIntQuiet (.num (intPow2 exp)) false
  | .pushPow2Dec exp =>
      VM.pushIntQuiet (.num (intPow2 exp - 1)) false
  | .pushNegPow2 exp =>
      VM.pushIntQuiet (.num (-intPow2 exp)) false
  | .push idx =>
      let v ← VM.fetch idx
      VM.push v
  | .pop idx =>
      -- Mirror the C++ behavior: swap top with s[idx], then pop the top.
      VM.swap 0 idx
      let _ ← VM.pop
      pure ()
  | .xchg0 idx =>
      VM.swap 0 idx
  | .xchg1 idx =>
      VM.swap 1 idx
  | .xchg x y =>
      if decide (x = 0 ∨ y ≤ x) then
        throw .invOpcode
      let st ← get
      if y < st.stack.size then
        VM.swap x y
      else
        throw .stkUnd
  | .xchg2 x y =>
      let st ← get
      let need : Nat := Nat.max (Nat.max x y) 1
      if need < st.stack.size then
        VM.swap 1 x
        VM.swap 0 y
      else
        throw .stkUnd
  | .xchg3 x y z =>
      let st ← get
      let need : Nat := Nat.max (Nat.max (Nat.max x y) z) 2
      if need < st.stack.size then
        VM.swap 2 x
        VM.swap 1 y
        VM.swap 0 z
      else
        throw .stkUnd
  | .xcpu x y =>
      let st ← get
      let need : Nat := Nat.max x y
      if need < st.stack.size then
        VM.swap 0 x
        let v ← VM.fetch y
        VM.push v
      else
        throw .stkUnd
  | .xc2pu x y z =>
      let st ← get
      let need : Nat := Nat.max (Nat.max (Nat.max x y) z) 1
      if need < st.stack.size then
        VM.swap 1 x
        VM.swap 0 y
        let v ← VM.fetch z
        VM.push v
      else
        throw .stkUnd
  | .xcpuxc x y z =>
      let st ← get
      if decide (st.stack.size > Nat.max (Nat.max x y) 1 ∧ z ≤ st.stack.size) then
        VM.swap 1 x
        let v ← VM.fetch y
        VM.push v
        VM.swap 0 1
        VM.swap 0 z
      else
        throw .stkUnd
  | .xcpu2 x y z =>
      let st ← get
      let need : Nat := Nat.max (Nat.max x y) z
      if need < st.stack.size then
        VM.swap 0 x
        let v1 ← VM.fetch y
        VM.push v1
        let v2 ← VM.fetch (z + 1)
        VM.push v2
      else
        throw .stkUnd
  | .puxc2 x y z =>
      let st ← get
      if x < st.stack.size && 1 < st.stack.size && y ≤ st.stack.size && z ≤ st.stack.size then
        let v ← VM.fetch x
        VM.push v
        VM.swap 0 2
        VM.swap 1 y
        VM.swap 0 z
      else
        throw .stkUnd
  | .puxc x y =>
      let st ← get
      if x < st.stack.size && y ≤ st.stack.size then
        let v ← VM.fetch x
        VM.push v
        VM.swap 0 1
        VM.swap 0 y
      else
        throw .stkUnd
  | .puxcpu x y z =>
      let st ← get
      if x < st.stack.size && y ≤ st.stack.size && z ≤ st.stack.size then
        let v ← VM.fetch x
        VM.push v
        VM.swap 0 1
        VM.swap 0 y
        let v2 ← VM.fetch z
        VM.push v2
      else
        throw .stkUnd
  | .pu2xc x y z =>
      let st ← get
      if x < st.stack.size && y ≤ st.stack.size && z ≤ st.stack.size + 1 then
        let v ← VM.fetch x
        VM.push v
        VM.swap 0 1
        let v2 ← VM.fetch y
        VM.push v2
        VM.swap 0 1
        VM.swap 0 z
      else
        throw .stkUnd
  | .push2 x y =>
      let st ← get
      let need : Nat := Nat.max x y
      if need < st.stack.size then
        let v1 ← VM.fetch x
        VM.push v1
        let v2 ← VM.fetch (y + 1)
        VM.push v2
      else
        throw .stkUnd
  | .push3 x y z =>
      let st ← get
      let need : Nat := Nat.max (Nat.max x y) z
      if need < st.stack.size then
        let v1 ← VM.fetch x
        VM.push v1
        let v2 ← VM.fetch (y + 1)
        VM.push v2
        let v3 ← VM.fetch (z + 2)
        VM.push v3
      else
        throw .stkUnd
  | .blkSwap x y =>
      let st ← get
      let total : Nat := x + y
      if total ≤ st.stack.size then
        let n := st.stack.size
        let front := st.stack.take (n - total)
        let below := st.stack.extract (n - total) (n - y)
        let top := st.stack.extract (n - y) n
        modify fun st => { st with stack := front ++ top ++ below }
      else
        throw .stkUnd
  | .blkPush x y =>
      let st ← get
      if y < st.stack.size then
        for _ in [0:x] do
          let v ← VM.fetch y
          VM.push v
      else
        throw .stkUnd
  | .rot =>
      let st ← get
      if 2 < st.stack.size then
        VM.swap 1 2
        VM.swap 0 1
      else
        throw .stkUnd
  | .rotRev =>
      let st ← get
      if 2 < st.stack.size then
        VM.swap 0 1
        VM.swap 1 2
      else
        throw .stkUnd
  | .twoSwap =>
      let st ← get
      if 3 < st.stack.size then
        VM.swap 1 3
        VM.swap 0 2
      else
        throw .stkUnd
  | .twoDup =>
      let st ← get
      if 1 < st.stack.size then
        let v1 ← VM.fetch 1
        VM.push v1
        let v2 ← VM.fetch 1
        VM.push v2
      else
        throw .stkUnd
  | .twoOver =>
      let v1 ← VM.fetch 3
      VM.push v1
      let v2 ← VM.fetch 3
      VM.push v2
  | .reverse x y =>
      let st ← get
      let total : Nat := x + y
      if total ≤ st.stack.size then
        let n := st.stack.size
        let start : Nat := n - total
        let stop : Nat := n - y
        let arr := Id.run do
          let mut a := st.stack
          for i in [0:(x / 2)] do
            let i1 : Nat := start + i
            let i2 : Nat := stop - 1 - i
            let v1 := a[i1]!
            let v2 := a[i2]!
            a := a.set! i1 v2
            a := a.set! i2 v1
          return a
        set { st with stack := arr }
      else
        throw .stkUnd
  | .pick =>
      let x ← VM.popNatUpTo ((1 <<< 30) - 1)
      let st ← get
      if x < st.stack.size then
        let v ← VM.fetch x
        VM.push v
      else
        throw .stkUnd
  | .roll =>
      let x ← VM.popNatUpTo ((1 <<< 30) - 1)
      let st ← get
      if x < st.stack.size then
        if x > 255 then
          modify fun st => st.consumeGas (Int.ofNat (x - 255))
        for i in [0:x] do
          let k : Nat := x - 1 - i
          VM.swap k (k + 1)
      else
        throw .stkUnd
  | .rollRev =>
      let x ← VM.popNatUpTo ((1 <<< 30) - 1)
      let st ← get
      if x < st.stack.size then
        if x > 255 then
          modify fun st => st.consumeGas (Int.ofNat (x - 255))
        for i in [0:x] do
          VM.swap i (i + 1)
      else
        throw .stkUnd
  | .blkSwapX =>
      let y ← VM.popNatUpTo ((1 <<< 30) - 1)
      let x ← VM.popNatUpTo ((1 <<< 30) - 1)
      let st ← get
      let total : Nat := x + y
      if total ≤ st.stack.size then
        if x > 0 && y > 0 then
          if total > 255 then
            modify fun st => st.consumeGas (Int.ofNat (total - 255))
          let st ← get
          let n := st.stack.size
          let front := st.stack.take (n - total)
          let below := st.stack.extract (n - total) (n - y)
          let top := st.stack.extract (n - y) n
          set { st with stack := front ++ top ++ below }
        else
          pure ()
      else
        throw .stkUnd
  | .reverseX =>
      let y ← VM.popNatUpTo ((1 <<< 30) - 1)
      let x ← VM.popNatUpTo ((1 <<< 30) - 1)
      let st ← get
      let total : Nat := x + y
      if total ≤ st.stack.size then
        if x > 255 then
          modify fun st => st.consumeGas (Int.ofNat (x - 255))
        let st ← get
        let n := st.stack.size
        let front := st.stack.take (n - total)
        let revPart := st.stack.extract (n - total) (n - y)
        let top := st.stack.extract (n - y) n
        set { st with stack := front ++ revPart.reverse ++ top }
      else
        throw .stkUnd
  | .dropX =>
      let x ← VM.popNatUpTo ((1 <<< 30) - 1)
      let st ← get
      if x ≤ st.stack.size then
        let keep : Nat := st.stack.size - x
        set { st with stack := st.stack.take keep }
      else
        throw .stkUnd
  | .tuck =>
      VM.swap 0 1
      let v ← VM.fetch 1
      VM.push v
  | .xchgX =>
      let x ← VM.popNatUpTo ((1 <<< 30) - 1)
      let st ← get
      if x < st.stack.size then
        VM.swap 0 x
      else
        throw .stkUnd
  | .depth =>
      let st ← get
      VM.pushSmallInt (Int.ofNat st.stack.size)
  | .chkDepth =>
      let x ← VM.popNatUpTo ((1 <<< 30) - 1)
      let st ← get
      if x ≤ st.stack.size then
        pure ()
      else
        throw .stkUnd
  | .onlyTopX =>
      let x ← VM.popNatUpTo ((1 <<< 30) - 1)
      let st ← get
      if x ≤ st.stack.size then
        let n := st.stack.size
        let d : Nat := n - x
        if d > 0 then
          if x > 255 then
            modify fun st => st.consumeGas (Int.ofNat (x - 255))
          let st ← get
          set { st with stack := st.stack.extract d n }
        else
          pure ()
      else
        throw .stkUnd
  | .onlyX =>
      let x ← VM.popNatUpTo ((1 <<< 30) - 1)
      let st ← get
      if x ≤ st.stack.size then
        set { st with stack := st.stack.take x }
      else
        throw .stkUnd
  | _ => next

end TvmLean
