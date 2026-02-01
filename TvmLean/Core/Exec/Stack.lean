import TvmLean.Core.Exec.Common
import TvmLean.Core.Exec.Stack.Nop
import TvmLean.Core.Exec.Stack.PushInt
import TvmLean.Core.Exec.Stack.PushPow2
import TvmLean.Core.Exec.Stack.PushPow2Dec
import TvmLean.Core.Exec.Stack.PushNegPow2
import TvmLean.Core.Exec.Stack.Push
import TvmLean.Core.Exec.Stack.Pop
import TvmLean.Core.Exec.Stack.Xchg0
import TvmLean.Core.Exec.Stack.Xchg1
import TvmLean.Core.Exec.Stack.Xchg
import TvmLean.Core.Exec.Stack.Xchg2
import TvmLean.Core.Exec.Stack.Xchg3
import TvmLean.Core.Exec.Stack.Xcpu
import TvmLean.Core.Exec.Stack.Xc2pu
import TvmLean.Core.Exec.Stack.Xcpuxc
import TvmLean.Core.Exec.Stack.Xcpu2
import TvmLean.Core.Exec.Stack.Puxc2
import TvmLean.Core.Exec.Stack.Puxc
import TvmLean.Core.Exec.Stack.Puxcpu
import TvmLean.Core.Exec.Stack.Pu2xc
import TvmLean.Core.Exec.Stack.Push2
import TvmLean.Core.Exec.Stack.Push3
import TvmLean.Core.Exec.Stack.BlkSwap
import TvmLean.Core.Exec.Stack.BlkPush
import TvmLean.Core.Exec.Stack.Rot
import TvmLean.Core.Exec.Stack.RotRev
import TvmLean.Core.Exec.Stack.TwoSwap
import TvmLean.Core.Exec.Stack.TwoDup
import TvmLean.Core.Exec.Stack.TwoOver
import TvmLean.Core.Exec.Stack.Reverse
import TvmLean.Core.Exec.Stack.Pick
import TvmLean.Core.Exec.Stack.Roll
import TvmLean.Core.Exec.Stack.RollRev
import TvmLean.Core.Exec.Stack.BlkSwapX
import TvmLean.Core.Exec.Stack.ReverseX
import TvmLean.Core.Exec.Stack.DropX
import TvmLean.Core.Exec.Stack.Tuck
import TvmLean.Core.Exec.Stack.XchgX
import TvmLean.Core.Exec.Stack.Depth
import TvmLean.Core.Exec.Stack.ChkDepth
import TvmLean.Core.Exec.Stack.OnlyTopX
import TvmLean.Core.Exec.Stack.OnlyX

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrStack (i : Instr) (next : VM Unit) : VM Unit :=
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
