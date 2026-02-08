import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.RSHIFT

/-!
Branch mapping analysis (`RSHIFT`)

Lean:
- `Tvm/Semantics/Instr/Arith.lean` (`evalRSHIFT`)

C++:
- `crypto/vm/arithops.cpp` (`exec_rshift`)

Mapped branches (10):
- stack underflow (0 args)
- stack underflow (1 arg)
- rhs type error
- lhs type error
- rhs `NaN`
- lhs `NaN`
- rhs invalid / out-of-range shift amount
- ok (positive lhs)
- ok (negative lhs, arithmetic sign-extension)
- gas precharge failure

Terminal outcomes (8):
- ok
- `VmError.stackUnderflow`
- `VmError.typeCheck`
- `VmError.rangeCheck`
- `VmError.nan`
- `VmError.outOfGas`
- pop-order-sensitive rhs-first failure
- pop-order-sensitive lhs-second failure

Risk areas:
- rhs/lhs pop-order and error-order
- sign extension for negative operands
- very large shift widths
- exact gas boundary (`computeExactGasBudget*`)
- NaN and non-serializable integers must be injected via program prelude
-/

private def rshiftId : InstrId := { name := "RSHIFT" }
private def rshiftInstr : Instr := .rshift

private def mkCase (name : String) (inputs : Array IntVal) : OracleCase :=
  let (initStack, program) := oracleIntInputsToStackOrProgram inputs
  { name := name
    instr := rshiftId
    program := program.push rshiftInstr
    initStack := initStack
    gasLimits := default
    fuel := 100000
  }

private def mkCaseWithProgram (name : String) (inputs : Array IntVal) (programTail : Array Instr) : OracleCase :=
  let (initStack, prelude) := oracleIntInputsToStackOrProgram inputs
  { name := name
    instr := rshiftId
    program := prelude ++ programTail
    initStack := initStack
    gasLimits := default
    fuel := 100000
  }

private def mkGasCase (name : String) (inputs : Array IntVal) (budget : Int) : OracleCase :=
  mkCaseWithProgram
    name
    inputs
    #[.pushInt (.num budget), .tonEnvOp .setGasLimit, rshiftInstr]

private def unit :=
  #[ ("/ok/identity/shift-by-zero", do
        let label := "/ok/identity/shift-by-zero"
        let (initStack, _) := oracleIntInputsToStackOrProgram #[.num 123456789, .num 0]
        let (expected, _) := oracleIntInputsToStackOrProgram #[.num 123456789]
        let result := runHandlerDirect execInstrArithRshift rshiftInstr initStack
        expectOkStack label result expected),
     ("/ok/basic/positive", do
        let label := "/ok/basic/positive"
        let (initStack, _) := oracleIntInputsToStackOrProgram #[.num 1024, .num 5]
        let (expected, _) := oracleIntInputsToStackOrProgram #[.num 32]
        let result := runHandlerDirect execInstrArithRshift rshiftInstr initStack
        expectOkStack label result expected),
     ("/ok/basic/negative-sign-extension", do
        let label := "/ok/basic/negative-sign-extension"
        let (initStack, _) := oracleIntInputsToStackOrProgram #[.num (-5), .num 1]
        let (expected, _) := oracleIntInputsToStackOrProgram #[.num (-3)]
        let result := runHandlerDirect execInstrArithRshift rshiftInstr initStack
        expectOkStack label result expected),
     ("/underflow/empty", do
        let label := "/underflow/empty"
        let result := runHandlerDirect execInstrArithRshift rshiftInstr #[]
        expectErr label result VmError.stackUnderflow),
     ("/underflow/single-arg", do
        let label := "/underflow/single-arg"
        let (initStack, _) := oracleIntInputsToStackOrProgram #[.num 9]
        let result := runHandlerDirect execInstrArithRshift rshiftInstr initStack
        expectErr label result VmError.stackUnderflow),
     ("/range/negative-shift", do
        let label := "/range/negative-shift"
        let (initStack, _) := oracleIntInputsToStackOrProgram #[.num 8, .num (-1)]
        let result := runHandlerDirect execInstrArithRshift rshiftInstr initStack
        expectErr label result VmError.rangeCheck)
  ]

private def oracle : Array OracleCase :=
  #[ mkCase "/ok/oracle/basic" #[.num 123456789, .num 7],
     mkCase "/ok/oracle/negative" #[.num (-17), .num 3],
     mkCase "/type/nan/rhs" #[.num 42, .nan],
     mkCase "/type/nan/lhs" #[.nan, .num 1],
     mkCase "/range/out-of-range/rhs" #[.num 1, .num 257],
     mkGasCase
       "/gas/exact/ok"
       #[.num 1, .num 1]
       (computeExactGasBudget rshiftInstr),
     mkGasCase
       "/gas/exact-minus-one/out-of-gas"
       #[.num 1, .num 1]
       (computeExactGasBudgetMinusOne rshiftInstr)
  ]

private def genRshiftFuzzCase : StdGen → OracleCase × StdGen
  | g =>
      let (lhsRaw, g1) := g.next
      let (rhsRaw, g2) := g1.next
      let lhs : Int := Int.ofNat (lhsRaw % 2000000001) - 1000000000
      let rhs : Int :=
        if rhsRaw % 16 == 0 then 0
        else if rhsRaw % 16 == 1 then 1
        else if rhsRaw % 16 == 2 then 255
        else Int.ofNat (rhsRaw % 1024)
      let caseName := s!"/fuzz/generated/{lhsRaw}/{rhsRaw}"
      (mkCase caseName #[.num lhs, .num rhs], g2)

private def fuzz :=
  #[{ seed := 0x52534846, count := 700, gen := genRshiftFuzzCase }]

def suite : InstrSuite where
  id := rshiftId
  unit := unit
  oracle := oracle
  fuzz := fuzz

initialize registerSuite suite

end Tests.Instr.Arith.RSHIFT
