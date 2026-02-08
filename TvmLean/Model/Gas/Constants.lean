import TvmLean.Model.Gas.Types
import TvmLean.Model.Instr.Ast

namespace TvmLean

def gasPerInstr : Int := 10
def exceptionGasPrice : Int := 50
def implicitJmpRefGasPrice : Int := 10
def implicitRetGasPrice : Int := 5
def cellLoadGasPrice : Int := 100
def cellReloadGasPrice : Int := 25
def cellCreateGasPrice : Int := 500
def tupleEntryGasPrice : Int := 1
def freeStackDepth : Nat := 32
def stackEntryGasPrice : Int := 1
def hashExtEntryGasPrice : Int := 1
def runvmGasPrice : Int := 40
def chksgnFreeCount : Nat := 10
def chksgnGasPrice : Int := 4000
def p256ChksgnGasPrice : Int := 3500
def ecrecoverGasPrice : Int := 1500
def secp256k1XonlyPubkeyTweakAddGasPrice : Int := 1250

def rist255MulGasPrice : Int := 2000
def rist255MulBaseGasPrice : Int := 750
def rist255AddGasPrice : Int := 600
def rist255FromHashGasPrice : Int := 600
def rist255ValidateGasPrice : Int := 200

def blsVerifyGasPrice : Int := 61000
def blsAggregateBaseGasPrice : Int := -2650
def blsAggregateElementGasPrice : Int := 4350
def blsFastAggregateVerifyBaseGasPrice : Int := 58000
def blsFastAggregateVerifyElementGasPrice : Int := 3000
def blsAggregateVerifyBaseGasPrice : Int := 38500
def blsAggregateVerifyElementGasPrice : Int := 22500

def blsG1AddSubGasPrice : Int := 3900
def blsG1NegGasPrice : Int := 750
def blsG1MulGasPrice : Int := 5200
def blsMapToG1GasPrice : Int := 2350
def blsG1InGroupGasPrice : Int := 2950

def blsG2AddSubGasPrice : Int := 6100
def blsG2NegGasPrice : Int := 1550
def blsG2MulGasPrice : Int := 10550
def blsMapToG2GasPrice : Int := 7950
def blsG2InGroupGasPrice : Int := 4250

def blsG1MultiExpBaseGasPrice : Int := 11375
def blsG1MultiExpCoef1GasPrice : Int := 630
def blsG1MultiExpCoef2GasPrice : Int := 8820
def blsG2MultiExpBaseGasPrice : Int := 30388
def blsG2MultiExpCoef1GasPrice : Int := 1280
def blsG2MultiExpCoef2GasPrice : Int := 22840

def blsPairingBaseGasPrice : Int := 20000
def blsPairingElementGasPrice : Int := 11800

def instrGas (i : Instr) (totBits : Nat) : Int :=
  -- TON charges invalid opcodes (dummy dispatch) as `gas_per_instr` without per-bit cost.
  -- In `runvmx`, EXTCALL falls into this bucket.
  match i with
  | .debugOp (.extCall _) =>
      gasPerInstr
  | _ => gasPerInstr + Int.ofNat totBits

/-! ### Minimal cp0 decoding (Milestone 2) -/

end TvmLean
