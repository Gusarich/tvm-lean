-- Auto-generated stub for TVM instruction GETORIGINALFWDFEE (category: config).
import Tests.Registry

open TvmLean Tests

def msgForwardPricesCell (firstFrac : Nat) : Cell :=
  -- msg_forward_prices#ea lump_price:uint64 bit_price:uint64 cell_price:uint64 ihr_price_factor:uint32
  --                  first_frac:uint16 next_frac:uint16 = MsgForwardPrices;
  let bits :=
    natToBits 0xea 8 ++
    natToBits 0 64 ++
    natToBits 0 64 ++
    natToBits 0 64 ++
    natToBits 0 32 ++
    natToBits firstFrac 16 ++
    natToBits 0 16
  Cell.mkOrdinary bits #[]

def testGetOriginalFwdFee : IO Unit := do
  let prog : List Instr := [ .tonEnvOp .getOriginalFwdFee ]
  let codeCell ←
    match assembleCp0 prog with
    | .ok c => pure c
    | .error e => throw (IO.userError s!"assembleCp0 failed: {reprStr e}")

  let mcPrices := msgForwardPricesCell 1000
  let basePrices := msgForwardPricesCell 2000
  let unpackedCfg : Array Value :=
    (Array.replicate 7 Value.null)
      |>.set! 4 (.slice (Slice.ofCell mcPrices))
      |>.set! 5 (.slice (Slice.ofCell basePrices))
  let params : Array Value :=
    (Array.replicate 15 Value.null)
      |>.set! 14 (.tuple unpackedCfg)
  let c7 : Array Value := #[.tuple params]

  let base := VmState.initial codeCell

  -- is_masterchain = true
  let stMc : VmState :=
    { base with stack := #[.int (.num 1000), .int (.num (-1))], regs := { base.regs with c7 := c7 } }
  match VmState.run 20 stMc with
  | .continue _ => throw (IO.userError "getoriginalfwdfee(mc): did not halt")
  | .halt exitCode st =>
      assert (exitCode == -1) s!"getoriginalfwdfee(mc): unexpected exitCode={exitCode}"
      assert (st.stack.size == 1) s!"getoriginalfwdfee(mc): unexpected stack size={st.stack.size}"
      match st.stack[0]! with
      | .int (.num n) => assert (n == 1015) s!"getoriginalfwdfee(mc): expected 1015, got {n}"
      | v => throw (IO.userError s!"getoriginalfwdfee(mc): unexpected stack value {v.pretty}")

  -- is_masterchain = false
  let stBase : VmState :=
    { base with stack := #[.int (.num 1000), .int (.num 0)], regs := { base.regs with c7 := c7 } }
  match VmState.run 20 stBase with
  | .continue _ => throw (IO.userError "getoriginalfwdfee(base): did not halt")
  | .halt exitCode st =>
      assert (exitCode == -1) s!"getoriginalfwdfee(base): unexpected exitCode={exitCode}"
      assert (st.stack.size == 1) s!"getoriginalfwdfee(base): unexpected stack size={st.stack.size}"
      match st.stack[0]! with
      | .int (.num n) => assert (n == 1031) s!"getoriginalfwdfee(base): expected 1031, got {n}"
      | v => throw (IO.userError s!"getoriginalfwdfee(base): unexpected stack value {v.pretty}")

initialize
  Tests.registerTest "config/getoriginalfwdfee" testGetOriginalFwdFee
  Tests.registerRoundtrip (.tonEnvOp .getOriginalFwdFee)
