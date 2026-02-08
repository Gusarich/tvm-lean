import TvmLean.Semantics.Exec.Common
import TvmLean.Semantics.Exec.Msg.SendMsg
import TvmLean.Semantics.Exec.Msg.SendRawMsg
import TvmLean.Semantics.Exec.Msg.RawReserve
import TvmLean.Semantics.Exec.Msg.RawReserveX
import TvmLean.Semantics.Exec.Msg.SetCode
import TvmLean.Semantics.Exec.Msg.SetLibCode
import TvmLean.Semantics.Exec.Msg.ChangeLib

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrMsg (_host : Host) (i : Instr) (next : VM Unit) : VM Unit :=
  execInstrMsgSendMsg i <|
  execInstrMsgSendRawMsg i <|
  execInstrMsgRawReserve i <|
  execInstrMsgRawReserveX i <|
  execInstrMsgSetCode i <|
  execInstrMsgSetLibCode i <|
  execInstrMsgChangeLib i <|
    next

end TvmLean
