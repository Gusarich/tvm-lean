import TvmLean.Semantics.Exec.Common
import TvmLean.Semantics.Exec.Stack.Nop
import TvmLean.Semantics.Exec.Stack.PushInt
import TvmLean.Semantics.Exec.Stack.PushPow2
import TvmLean.Semantics.Exec.Stack.PushPow2Dec
import TvmLean.Semantics.Exec.Stack.PushNegPow2
import TvmLean.Semantics.Exec.Stack.Push
import TvmLean.Semantics.Exec.Stack.Pop
import TvmLean.Semantics.Exec.Stack.Xchg0
import TvmLean.Semantics.Exec.Stack.Xchg1
import TvmLean.Semantics.Exec.Stack.Xchg
import TvmLean.Semantics.Exec.Stack.Xchg2
import TvmLean.Semantics.Exec.Stack.Xchg3
import TvmLean.Semantics.Exec.Stack.Xcpu
import TvmLean.Semantics.Exec.Stack.Xc2pu
import TvmLean.Semantics.Exec.Stack.Xcpuxc
import TvmLean.Semantics.Exec.Stack.Xcpu2
import TvmLean.Semantics.Exec.Stack.Puxc2
import TvmLean.Semantics.Exec.Stack.Puxc
import TvmLean.Semantics.Exec.Stack.Puxcpu
import TvmLean.Semantics.Exec.Stack.Pu2xc
import TvmLean.Semantics.Exec.Stack.Push2
import TvmLean.Semantics.Exec.Stack.Push3
import TvmLean.Semantics.Exec.Stack.BlkSwap
import TvmLean.Semantics.Exec.Stack.BlkPush
import TvmLean.Semantics.Exec.Stack.Rot
import TvmLean.Semantics.Exec.Stack.RotRev
import TvmLean.Semantics.Exec.Stack.TwoSwap
import TvmLean.Semantics.Exec.Stack.TwoDup
import TvmLean.Semantics.Exec.Stack.TwoOver
import TvmLean.Semantics.Exec.Stack.Reverse
import TvmLean.Semantics.Exec.Stack.Pick
import TvmLean.Semantics.Exec.Stack.Roll
import TvmLean.Semantics.Exec.Stack.RollRev
import TvmLean.Semantics.Exec.Stack.BlkSwapX
import TvmLean.Semantics.Exec.Stack.ReverseX
import TvmLean.Semantics.Exec.Stack.DropX
import TvmLean.Semantics.Exec.Stack.Tuck
import TvmLean.Semantics.Exec.Stack.XchgX
import TvmLean.Semantics.Exec.Stack.Depth
import TvmLean.Semantics.Exec.Stack.ChkDepth
import TvmLean.Semantics.Exec.Stack.OnlyTopX
import TvmLean.Semantics.Exec.Stack.OnlyX

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrStack (_host : Host) (i : Instr) (next : VM Unit) : VM Unit :=
  execInstrStackNop i <|
  execInstrStackPushInt i <|
  execInstrStackPushPow2 i <|
  execInstrStackPushPow2Dec i <|
  execInstrStackPushNegPow2 i <|
  execInstrStackPush i <|
  execInstrStackPop i <|
  execInstrStackXchg0 i <|
  execInstrStackXchg1 i <|
  execInstrStackXchg i <|
  execInstrStackXchg2 i <|
  execInstrStackXchg3 i <|
  execInstrStackXcpu i <|
  execInstrStackXc2pu i <|
  execInstrStackXcpuxc i <|
  execInstrStackXcpu2 i <|
  execInstrStackPuxc2 i <|
  execInstrStackPuxc i <|
  execInstrStackPuxcpu i <|
  execInstrStackPu2xc i <|
  execInstrStackPush2 i <|
  execInstrStackPush3 i <|
  execInstrStackBlkSwap i <|
  execInstrStackBlkPush i <|
  execInstrStackRot i <|
  execInstrStackRotRev i <|
  execInstrStackTwoSwap i <|
  execInstrStackTwoDup i <|
  execInstrStackTwoOver i <|
  execInstrStackReverse i <|
  execInstrStackPick i <|
  execInstrStackRoll i <|
  execInstrStackRollRev i <|
  execInstrStackBlkSwapX i <|
  execInstrStackReverseX i <|
  execInstrStackDropX i <|
  execInstrStackTuck i <|
  execInstrStackXchgX i <|
  execInstrStackDepth i <|
  execInstrStackChkDepth i <|
  execInstrStackOnlyTopX i <|
  execInstrStackOnlyX i <|
    next

end TvmLean
