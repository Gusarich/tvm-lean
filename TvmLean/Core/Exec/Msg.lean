import TvmLean.Core.Exec.Common
import TvmLean.Core.Exec.Msg.SendMsg
import TvmLean.Core.Exec.Msg.SendRawMsg
import TvmLean.Core.Exec.Msg.RawReserve
import TvmLean.Core.Exec.Msg.RawReserveX
import TvmLean.Core.Exec.Msg.SetCode

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrMsg (i : Instr) (next : VM Unit) : VM Unit :=
  execInstrMsgSendMsg i <|
  execInstrMsgSendRawMsg i <|
  execInstrMsgRawReserve i <|
  execInstrMsgRawReserveX i <|
  execInstrMsgSetCode i <|
    next

end TvmLean
