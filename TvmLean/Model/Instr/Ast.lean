import TvmLean.Model.Error.Excno
import TvmLean.Model.Value.IntVal
import TvmLean.Model.Cell.Slice
import TvmLean.Model.Cell.Builder

namespace TvmLean

inductive DictSetMode : Type
  | set
  | replace
  | add
  deriving DecidableEq, Repr

/-! Additional dictionary opcodes (mostly newer TVM versions). -/

inductive DictMutMode : Type
  | set
  | replace
  | add
  | del
  deriving DecidableEq, Repr

inductive PfxDictGetKind : Type
  | getQ
  | get
  | getJmp
  | getExec
  deriving DecidableEq, Repr

inductive DictExtInstr : Type
  | lddicts (preload : Bool) -- LDDICTS / PLDDICTS
  | mutGet (intKey : Bool) (unsigned : Bool) (byRef : Bool) (mode : DictMutMode) -- DICT*{SET,REPLACE,ADD,DEL}GET{REF?}
  | mutGetB (intKey : Bool) (unsigned : Bool) (mode : DictSetMode) -- DICT*{SET,REPLACE,ADD}GETB
  | del (intKey : Bool) (unsigned : Bool) -- DICT{I,U}?DEL
  | getOptRef (intKey : Bool) (unsigned : Bool) -- DICT{I,U}?GETOPTREF
  | setGetOptRef (intKey : Bool) (unsigned : Bool) -- DICT{I,U}?SETGETOPTREF
  | subdictGet (intKey : Bool) (unsigned : Bool) (rp : Bool) -- SUBDICT*GET / SUBDICT*RPGET
  | pfxSet (mode : DictSetMode) -- PFXDICT{SET,REPLACE,ADD}
  | pfxDel -- PFXDICTDEL
  | pfxGet (kind : PfxDictGetKind) -- PFXDICTGET{Q,JMP,EXEC}
  | pfxSwitch (dict : Cell) (keyLen : Nat) -- PFXDICTSWITCH (const dict ref + key_len)
  deriving Repr

inductive TupleInstr : Type
  | mktuple (n : Nat) -- TUPLE <n>
  | index (idx : Nat) -- INDEX <idx>
  | index2 (i : Nat) (j : Nat) -- INDEX2 <i>,<j> (0..3 each)
  | index3 (i : Nat) (j : Nat) (k : Nat) -- INDEX3 <i>,<j>,<k> (0..3 each)
  | untuple (n : Nat) -- UNTUPLE <n>
  | unpackFirst (n : Nat) -- UNPACKFIRST <n>
  | explode (maxLen : Nat) -- EXPLODE <maxLen>
  | setIndex (idx : Nat) -- SETINDEX <idx>
  | indexQ (idx : Nat) -- INDEXQ <idx>
  | setIndexQ (idx : Nat) -- SETINDEXQ <idx>
  | mktupleVar          -- TUPLEVAR
  | indexVar            -- INDEXVAR
  | untupleVar          -- UNTUPLEVAR
  | unpackFirstVar      -- UNPACKFIRSTVAR
  | explodeVar          -- EXPLODEVAR
  | setIndexVar         -- SETINDEXVAR
  | indexVarQ           -- INDEXVARQ
  | setIndexVarQ        -- SETINDEXVARQ
  | tlen                -- TLEN
  | qtlen               -- QTLEN
  | isTuple             -- ISTUPLE
  | last                -- LAST
  | tpush             -- TPUSH
  | tpop              -- TPOP
  deriving Repr

inductive CellInstr : Type
  | sdFirst -- SDFIRST
  | sdSfx -- SDSFX
  | sdSfxRev -- SDSFXREV
  | sdPsfx -- SDPSFX
  | sdPsfxRev -- SDPSFXREV
  | sdCntLead1 -- SDCNTLEAD1
  | sdCntTrail1 -- SDCNTTRAIL1
  | strefR (quiet : Bool) -- STREFR / STREFRQ
  | endxc -- ENDXC
  | sdSubstr -- SDSUBSTR
  | scutfirst -- SCUTFIRST
  | sskipfirst -- SSKIPFIRST
  | scutlast -- SCUTLAST
  | sskiplast -- SSKIPLAST
  | subslice -- SUBSLICE
  | split (quiet : Bool) -- SPLIT / SPLITQ
  | pldRefVar -- PLDREFVAR
  | loadLeInt (unsigned : Bool) (bytes : Nat) (prefetch : Bool) (quiet : Bool) -- {P}LD{I,U}LE{4,8}{Q}
  | ldZeroes -- LDZEROES
  | ldOnes   -- LDONES
  | ldSame   -- LDSAME
  | sdepth   -- SDEPTH
  | clevel   -- CLEVEL
  | clevelMask -- CLEVELMASK
  | chashI (i : Nat) -- CHASHI <i>
  | cdepthI (i : Nat) -- CDEPTHI <i>
  | chashIX  -- CHASHIX (index from stack)
  | cdepthIX -- CDEPTHIX (index from stack)
  | schkBits (quiet : Bool) -- SCHKBITS / SCHKBITSQ
  | schkRefs (quiet : Bool) -- SCHKREFS / SCHKREFSQ
  | schkBitRefs (quiet : Bool) -- SCHKBITREFS / SCHKBITREFSQ
  | bdepth     -- BDEPTH
  | brefs      -- BREFS
  | bbitrefs   -- BBITREFS
  | brembits   -- BREMBITS
  | bremrefs   -- BREMREFS
  | brembitrefs -- BREMBITREFS
  | bchkBitsImm (bits : Nat) (quiet : Bool) -- BCHKBITS{Q} <bits>
  | bchk (needBits : Bool) (needRefs : Bool) (quiet : Bool) -- BCHK{BITS,REFS,BITREFS}{Q}
  deriving Repr

/-! Extra crypto opcodes (mostly newer TVM versions). -/

inductive CryptoExtInstr : Type
  | ecrecover
  | secp256k1XonlyPubkeyTweakAdd
  | p256ChkSignU
  | p256ChkSignS
  | rist255FromHash
  | rist255Validate
  | rist255Add
  | rist255Sub
  | rist255Mul
  | rist255MulBase
  | rist255PushL
  | rist255Qvalidate
  | rist255Qadd
  | rist255Qsub
  | rist255Qmul
  | rist255QmulBase
  | blsVerify
  | blsAggregate
  | blsFastAggregateVerify
  | blsAggregateVerify
  | blsG1Add
  | blsG1Sub
  | blsG1Neg
  | blsG1Mul
  | blsG1MultiExp
  | blsG1Zero
  | blsMapToG1
  | blsG1InGroup
  | blsG1IsZero
  | blsG2Add
  | blsG2Sub
  | blsG2Neg
  | blsG2Mul
  | blsG2MultiExp
  | blsG2Zero
  | blsMapToG2
  | blsG2InGroup
  | blsG2IsZero
  | blsPairing
  | blsPushR
  deriving Repr

inductive CryptoInstr : Type
  | hashExt (hashId : Nat) (append : Bool) (rev : Bool) -- HASHEXT{A}{R} <hashId> (255 means from stack)
  | hashCU   -- HASHCU
  | hashSU   -- HASHSU
  | sha256U  -- SHA256U
  | chkSignU -- CHKSIGNU
  | chkSignS -- CHKSIGNS
  | ext (op : CryptoExtInstr)
  deriving Repr

inductive TonEnvInstr : Type
  | balance            -- BALANCE
  | now                -- NOW
  | blockLt            -- BLOCKLT
  | lTime              -- LTIME
  | randSeed           -- RANDSEED
  | myAddr             -- MYADDR
  | configRoot         -- CONFIGROOT
  | configDict         -- CONFIGDICT
  | configParam (opt : Bool) -- CONFIGPARAM / CONFIGOPTPARAM
  | myCode             -- MYCODE
  | incomingValue      -- INCOMINGVALUE
  | storageFees        -- STORAGEFEES
  | prevBlocksInfoTuple -- PREVBLOCKSINFOTUPLE
  | prevMcBlocks       -- PREVMCBLOCKS
  | prevKeyBlock       -- PREVKEYBLOCK
  | prevMcBlocks100    -- PREVMCBLOCKS_100
  | unpackedConfigTuple -- UNPACKEDCONFIGTUPLE
  | duePayment         -- DUEPAYMENT
  | getParam (idx : Nat) -- GETPARAM <idx>
  | randu256           -- RANDU256
  | rand               -- RAND
  | setRand (mix : Bool) -- SETRAND / ADDRAND
  | getGlobVar         -- GETGLOBVAR
  | getGlob (idx : Nat) -- GETGLOB <idx>
  | setGlobVar         -- SETGLOBVAR
  | setGlob (idx : Nat) -- SETGLOB <idx>
  | accept             -- ACCEPT
  | setGasLimit        -- SETGASLIMIT
  | gasConsumed        -- GASCONSUMED
  | commit             -- COMMIT
  | ldGrams            -- LDGRAMS
  | stGrams            -- STGRAMS
  | ldMsgAddr (quiet : Bool) -- LDMSGADDR{Q}
  | parseMsgAddr (quiet : Bool) -- PARSEMSGADDR{Q}
  | rewriteStdAddr (quiet : Bool) -- REWRITESTDADDR{Q}
  | rewriteVarAddr (quiet : Bool) -- REWRITEVARADDR{Q}
  | ldStdAddr (quiet : Bool) -- LDSTDADDR{Q}
  | ldOptStdAddr (quiet : Bool) -- LDOPTSTDADDR{Q}
  | stStdAddr (quiet : Bool) -- STSTDADDR{Q}
  | stOptStdAddr (quiet : Bool) -- STOPTSTDADDR{Q}
  | globalId             -- GLOBALID
  | getGasFee            -- GETGASFEE
  | getStorageFee        -- GETSTORAGEFEE
  | getGasFeeSimple      -- GETGASFEESIMPLE
  | getForwardFee          -- GETFORWARDFEE
  | getPrecompiledGas   -- GETPRECOMPILEDGAS
  | getOriginalFwdFee  -- GETORIGINALFWDFEE
  | getForwardFeeSimple    -- GETFORWARDFEESIMPLE
  | getExtraBalance       -- GETEXTRABALANCE
  | inMsgParam (idx : Nat) -- INMSG_* / INMSGPARAM <idx>
  | sendMsg            -- SENDMSG
  | sendRawMsg         -- SENDRAWMSG
  | rawReserve         -- RAWRESERVE
  | rawReserveX        -- RAWRESERVEX
  | setCode            -- SETCODE
  | setLibCode         -- SETLIBCODE
  | changeLib          -- CHANGELIB
  deriving Repr

inductive DebugInstr : Type
  | dumpStk            -- DUMPSTK
  | strDump            -- STRDUMP
  | dump (idx : Nat)   -- DUMP <idx>
  | debug (i : Nat)    -- DEBUG <i> (0x01..0x13)
  | debug1 (t : Nat)   -- DEBUG_1 <t> (0x15..0x1f)
  | debug2 (t : Nat)   -- DEBUG_2 <t> (0x30..0xef)
  | debugStr (s : Slice) -- DEBUGSTR <s> (inline bytes)
  | extCall (id : Nat) -- EXTCALL <id>
  deriving Repr

inductive ContExtInstr : Type
  | condSel               -- CONDSEL
  | condSelChk            -- CONDSELCHK
  | ifretAlt              -- IFRETALT
  | ifnotretAlt           -- IFNOTRETALT
  | ifbitjmp (i : Nat)    -- IFBITJMP <i>
  | ifnbitjmp (i : Nat)   -- IFNBITJMP <i>
  | ifbitjmpref (i : Nat) (code : Slice)  -- IFBITJMPREF <i> (1 ref)
  | ifnbitjmpref (i : Nat) (code : Slice) -- IFNBITJMPREF <i> (1 ref)
  | pow2                  -- POW2
  | fitsx                 -- FITSX
  | ufitsx                -- UFITSX
  | qand                  -- QAND
  | qor                   -- QOR
  | qxor                  -- QXOR
  | qnot                  -- QNOT
  | qfitsx                -- QFITSX
  | qufitsx               -- QUFITSX
  | qbitsize              -- QBITSIZE
  | qmin                  -- QMIN
  | isnan                 -- ISNAN
  | chknan                -- CHKNAN
  | qsgn                  -- QSGN
  | qless                 -- QLESS
  | qequal                -- QEQUAL
  | qleq                  -- QLEQ
  | qgreater              -- QGREATER
  | qneq                  -- QNEQ
  | qgeq                  -- QGEQ
  | repeat (brk : Bool)          -- REPEAT / REPEATBRK
  | repeatEnd (brk : Bool)       -- REPEATEND / REPEATENDBRK
  | until (brk : Bool)           -- UNTILBRK
  | untilEnd (brk : Bool)        -- UNTILEND / UNTILENDBRK
  | while (brk : Bool)           -- WHILEBRK
  | whileEnd (brk : Bool)        -- WHILEEND / WHILEENDBRK
  | again (brk : Bool)           -- AGAIN / AGAINBRK
  | againEnd (brk : Bool)        -- AGAINEND / AGAINENDBRK
  | jmpDict (idx : Nat)          -- JMPDICT <idx>
  | pushCtrX                     -- PUSHCTRX
  | popCtrX                      -- POPCTRX
  | setContCtrX                  -- SETCONTCTRX
  | setContCtrMany (mask : Nat)  -- SETCONTCTRMANY <mask>
  | setContCtrManyX              -- SETCONTCTRMANYX
  | setRetCtr (idx : Nat)        -- SETRETCTR c<idx>
  | setAltCtr (idx : Nat)        -- SETALTCTR c<idx>
  | popSave (idx : Nat)          -- POPSAVE c<idx>
  | saveAltCtr (idx : Nat)       -- SAVEALTCTR c<idx>
  | saveBothCtr (idx : Nat)      -- SAVEBOTHCTR c<idx>
  | runvm (mode : Nat)           -- RUNVM <mode>
  | runvmx                      -- RUNVMX (mode from stack)
  | atexit                -- ATEXIT
  | atexitAlt             -- ATEXITALT
  | setExitAlt            -- SETEXITALT
  | thenret               -- THENRET
  | thenretAlt            -- THENRETALT
  | invert                -- INVERT
  | booleval              -- BOOLEVAL
  deriving Repr

/-! Extra arithmetic opcodes (mostly newer TVM versions). -/

inductive ArithExtInstr : Type
  | qaddInt (n : Int) -- QADDINT <tinyint8>
  | qmulInt (n : Int) -- QMULINT <tinyint8>
  | qeqInt (n : Int) -- QEQINT <tinyint8>
  | qneqInt (n : Int) -- QNEQINT <tinyint8>
  | qgtInt (n : Int) -- QGTINT <tinyint8>
  | fitsConst (unsigned : Bool) (quiet : Bool) (bits : Nat) -- {Q}{U}FITS <tinyint8+1>
  | lshiftVar (quiet : Bool) -- QLSHIFT_VAR
  | rshiftVar (quiet : Bool) -- QRSHIFT_VAR
  | shrMod (mul : Bool) (add : Bool) (d : Nat) (roundMode : Int) (quiet : Bool) (z : Option Nat)
      -- {Q}{MUL}{ADD}{RSHIFT,MODPOW2,RSHIFTMOD}{R,C}{#} (z from stack unless `z` is provided)
  | shlDivMod (d : Nat) (roundMode : Int) (add : Bool) (quiet : Bool) (z : Option Nat)
      -- {Q}{ADD}LSHIFT{DIV,MOD,DIVMOD}{R,C}{#} (z from stack unless `z` is provided)
  deriving Repr

/-! Extra cell opcodes (mostly newer TVM versions). -/

inductive CellExtInstr : Type
  | btos -- BTOS
  | plduz (c : Nat) -- PLDUZ (arg is 3-bit `c`)
  | ldVarInt (signed : Bool) (lenBits : Nat) -- LDVAR{,U}INT{16,32}
  | xload (quiet : Bool) -- XLOAD / XLOADQ
  | stVarInt (signed : Bool) (lenBits : Nat) -- STVAR{,U}INT{16,32}
  | stLeInt (unsigned : Bool) (bytes : Nat) -- ST{I,U}LE{4,8}
  | stRefConst (c : Cell) -- STREFCONST
  | stRef2Const (c1 : Cell) (c2 : Cell) -- STREF2CONST
  | hashbu -- HASHBU
  | cdataSize (quiet : Bool) -- CDATASIZE / CDATASIZEQ
  | sdataSize (quiet : Bool) -- SDATASIZE / SDATASIZEQ
  deriving Repr

inductive Instr : Type
  | nop
  | pushInt (n : IntVal)
  | pushPow2 (exp : Nat) -- PUSHPOW2 <exp>
  | pushPow2Dec (exp : Nat) -- PUSHPOW2DEC <exp>  (2^exp - 1)
  | pushNegPow2 (exp : Nat) -- PUSHNEGPOW2 <exp>  (-2^exp)
  | push (idx : Nat)    -- PUSH s[idx]
  | pop (idx : Nat)     -- POP s[idx]
  | xchg0 (idx : Nat)   -- XCHG s0,s[idx]
  | xchg1 (idx : Nat)   -- XCHG s1,s[idx]
  | xchg (x : Nat) (y : Nat) -- XCHG s<x>,s<y>
  | xchg2 (x : Nat) (y : Nat) -- XCHG2 s<x>,s<y>
  | xchg3 (x : Nat) (y : Nat) (z : Nat) -- XCHG3 s<x>,s<y>,s<z>
  | xcpu (x : Nat) (y : Nat) -- XCPU s<x>,s<y>
  | xc2pu (x : Nat) (y : Nat) (z : Nat) -- XC2PU s<x>,s<y>,s<z>
  | xcpuxc (x : Nat) (y : Nat) (z : Nat) -- XCPUXC s<x>,s<y>,s<z-1>
  | xcpu2 (x : Nat) (y : Nat) (z : Nat) -- XCPU2 s<x>,s<y>,s<z>
  | puxc2 (x : Nat) (y : Nat) (z : Nat) -- PUXC2 s<x>,s<y-1>,s<z-1>
  | puxc (x : Nat) (y : Nat) -- PUXC s<x>,s<y-1> (see C++ stackops)
  | puxcpu (x : Nat) (y : Nat) (z : Nat) -- PUXCPU s<x>,s<y-1>,s<z-1>
  | pu2xc (x : Nat) (y : Nat) (z : Nat) -- PU2XC s<x>,s<y-1>,s<z-2>
  | push2 (x : Nat) (y : Nat) -- PUSH2 s<x>,s<y>
  | push3 (x : Nat) (y : Nat) (z : Nat) -- PUSH3 s<x>,s<y>,s<z>
  | blkSwap (x : Nat) (y : Nat) -- BLKSWAP <x>,<y>
  | blkPush (x : Nat) (y : Nat) -- BLKPUSH <x>,<y>
  | rot                -- ROT
  | rotRev             -- ROTREV
  | twoSwap            -- 2SWAP
  | twoDup             -- 2DUP
  | twoOver            -- 2OVER
  | reverse (x : Nat) (y : Nat) -- REVERSE <x>,<y>
  | pick               -- PICK
  | roll               -- ROLL
  | rollRev            -- ROLLREV
  | blkSwapX           -- BLKSWX
  | reverseX           -- REVX
  | dropX              -- DROPX
  | xchgX              -- XCHGX
  | depth              -- DEPTH
  | chkDepth           -- CHKDEPTH
  | onlyTopX           -- ONLYTOPX
  | onlyX              -- ONLYX
  | tuck               -- TUCK
  | pushCtr (idx : Nat) -- PUSHCTRX <idx> (we'll use it for c4/c5/c7 too)
  | popCtr (idx : Nat)  -- POPCTRX <idx>
  | setContCtr (idx : Nat) -- SETCONTCTR c<idx>
  | ctos
  | xctos
  | cellExt (op : CellExtInstr)
  | newc
  | endc
  | endcst
  | ends
  | ldu (bits : Nat)
  | loadInt (unsigned : Bool) (prefetch : Bool) (quiet : Bool) (bits : Nat)
  | loadIntVar (unsigned : Bool) (prefetch : Bool) (quiet : Bool) -- {P}LD{I,U}X{Q}
  | ldref
  | ldrefRtos
  | pldRefIdx (idx : Nat) -- PLDREFIDX <idx>
  | loadSliceX (prefetch : Bool) (quiet : Bool) -- {PLD,LD}SLICEX{Q}
  | loadSliceFixed (prefetch : Bool) (quiet : Bool) (bits : Nat) -- {P}LDSLICE{Q} <bits>
  | sti (bits : Nat)
  | stu (bits : Nat)
  | stIntVar (unsigned : Bool) (rev : Bool) (quiet : Bool) -- ST{I,U}X{R}{Q}
  | stIntFixed (unsigned : Bool) (rev : Bool) (quiet : Bool) (bits : Nat) -- ST{I,U}{R}{Q} <bits>
  | stSlice (rev : Bool) (quiet : Bool) -- {STSLICE,STSLICER}{Q?}
  | stb (rev : Bool) (quiet : Bool) -- {STB,STBR}{Q?}
  | stbRef (rev : Bool) (quiet : Bool) -- {STBREF,STBREFR}{Q?} and ENDCST (8-bit)
  | stSliceConst (s : Slice) -- STSLICECONST (inline constant slice)
  | stZeroes -- STZEROES
  | stOnes   -- STONES
  | stSame   -- STSAME
  | stref -- STREF
  | strefq -- STREFQ
  | bbits -- BBITS
  | setcp (cp : Int)
  | setcpX
  | ifret
  | ifnotret
  | if_         -- IF
  | ifnot       -- IFNOT
  | inc
  | qinc
  | dec
  | qdec
  | negate
  | qnegate
  | qpow2
  | add
  | qadd
  | addInt (n : Int) -- ADDINT <tinyint8>
  | sub
  | qsub
  | qsubr
  | subr
  | mulInt (n : Int) -- MULINT <tinyint8>
  | mul
  | qmul
  | min
  | max
  | qmax
  | minmax
  | qminmax
  | abs (quiet : Bool) -- ABS / QABS
  | bitsize -- BITSIZE
  | ubitsize (quiet : Bool) -- UBITSIZE / QUBITSIZE
  | arithExt (op : ArithExtInstr)
  | mulShrModConst (d : Nat) (roundMode : Int) (z : Nat) -- MUL{RSHIFT,MODPOW2,RSHIFTMOD}# <z>
  | divMod (d : Nat) (roundMode : Int) (add : Bool) (quiet : Bool) -- {Q}{ADD}{DIV,MOD,DIVMOD}{R,C}
  | mulDivMod (d : Nat) (roundMode : Int) (add : Bool) (quiet : Bool) -- {Q}{MUL,MULADD}{DIV,MOD,DIVMOD}{R,C}
  | lshiftConst (quiet : Bool) (bits : Nat) -- {Q}LSHIFT <tinyint8+1>
  | rshiftConst (quiet : Bool) (bits : Nat) -- {Q}RSHIFT <tinyint8+1>
  | lshift            -- LSHIFT
  | rshift            -- RSHIFT
  | equal
  | neq
  | throw (exc : Int)      -- THROW <exc>
  | throwIf (exc : Int)    -- THROWIF <exc>
  | throwIfNot (exc : Int) -- THROWIFNOT <exc>
  | throwArg (exc : Int)      -- THROWARG <exc>
  | throwArgIf (exc : Int)    -- THROWARGIF <exc>
  | throwArgIfNot (exc : Int) -- THROWARGIFNOT <exc>
  | throwAny (hasParam : Bool) (hasCond : Bool) (throwCond : Bool) -- THROW{ARG}ANY{IF,IFNOT}
  | try_               -- TRY
  | tryArgs (params : Nat) (retVals : Nat) -- TRYARGS <params>,<retVals>
  | saveCtr (idx : Nat)  -- SAVECTR c<idx>
  | sameAlt             -- SAMEALT
  | sameAltSave         -- SAMEALTSAVE
  | boolAnd             -- BOOLAND
  | boolOr              -- BOOLOR
  | composBoth          -- COMPOSBOTH
  | contExt (op : ContExtInstr)
  | setContArgs (copy : Nat) (more : Int) -- SETCONTARGS <copy>,<more>
  | setContVarArgs      -- SETCONTVARARGS
  | setNumVarArgs       -- SETNUMVARARGS
  | returnArgs (count : Nat) -- RETURNARGS <count>
  | returnVarArgs       -- RETURNVARARGS
  | bless               -- BLESS
  | blessVarArgs        -- BLESSVARARGS
  | blessArgs (copy : Nat) (more : Int) -- BLESSARGS <copy>,<more>
  | dictPushConst (dict : Cell) (keyBits : Nat) -- DICTPUSHCONST: pushes dict-root cell + key size
  | dictGet (intKey : Bool) (unsigned : Bool) (byRef : Bool) -- DICT{I,U}GET{REF?} / DICTGET{REF?}
  | dictGetNear (args4 : Nat) -- DICTGET{NEXT,PREV}{EQ} and DICT{I,U}GET{NEXT,PREV}{EQ}
  | dictGetMinMax (args5 : Nat) -- DICT{I,U}{MIN,MAX,REMMIN,REMMAX}{REF?}
  | dictGetExec (unsigned : Bool) (doCall : Bool) (pushZ : Bool) -- DICT{I,U}GET{JMP,EXEC}{Z?}
  | dictSet (intKey : Bool) (unsigned : Bool) (byRef : Bool) (mode : DictSetMode) -- DICT{I,U}{SET,REPLACE,ADD}{REF?}
  | dictSetB (intKey : Bool) (unsigned : Bool) (mode : DictSetMode) -- DICT{I,U}{SET,REPLACE,ADD}B
  | dictReplaceB (intKey : Bool) (unsigned : Bool) -- DICT{I,U}?REPLACEB (builder value)
  | dictExt (op : DictExtInstr)
  | stdict              -- STDICT
  | skipdict            -- SKIPDICT
  | lddict (preload : Bool) (quiet : Bool) -- {P}LDDICT{Q}
  | and_
  | or
  | xor
  | not_
  | sgn
  | less
  | leq
  | greater
  | geq
  | cmp
  | qcmp
  | sbits
  | srefs
  | sbitrefs
  | cdepth             -- CDEPTH
  | sempty            -- SEMPTY
  | sdempty           -- SDEMPTY
  | srempty           -- SREMPTY
  | sdCntLead0         -- SDCNTLEAD0
  | sdCntTrail0        -- SDCNTTRAIL0
  | sdEq              -- SDEQ
  | sdPpfx            -- SDPPFX
  | sdPpfxRev         -- SDPPFXREV
  | sdPfx             -- SDPFX
  | sdPfxRev          -- SDPFXREV
  | sdLexCmp          -- SDLEXCMP
  | sdcutfirst        -- SDCUTFIRST
  | sdskipfirst       -- SDSKIPFIRST
  | sdcutlast         -- SDCUTLAST
  | sdskiplast        -- SDSKIPLAST
  | sdBeginsX (quiet : Bool)        -- SDBEGINSX{Q}
  | sdBeginsConst (quiet : Bool) (pref : Slice) -- SDBEGINS{Q} <const>
  | lessInt (n : Int) -- LESSINT <tinyint8>
  | qlessInt (n : Int) -- QLESSINT <tinyint8>
  | eqInt (n : Int)   -- EQINT <tinyint8>
  | gtInt (n : Int)   -- GTINT <tinyint8>
  | neqInt (n : Int)  -- NEQINT <tinyint8>
  | pushNull          -- PUSHNULL
  | isNull            -- ISNULL
  | nullSwapIf        -- NULLSWAPIF
  | nullSwapIfNot     -- NULLSWAPIFNOT
  | nullRotrIf        -- NULLROTRIF
  | nullRotrIfNot     -- NULLROTRIFNOT
  | nullSwapIf2       -- NULLSWAPIF2
  | nullSwapIfNot2    -- NULLSWAPIFNOT2
  | nullRotrIf2       -- NULLROTRIF2
  | nullRotrIfNot2    -- NULLROTRIFNOT2
  | tupleOp (op : TupleInstr)
  | cellOp (op : CellInstr)
  | cryptoOp (op : CryptoInstr)
  | tonEnvOp (op : TonEnvInstr)
  | blkdrop2 (x : Nat) (y : Nat) -- BLKDROP2 <x>,<y>
  | pushSliceConst (s : Slice) -- PUSHSLICE (inline constant slice)
  | pushCont (code : Slice) -- PUSHCONT (inline continuation)
  | pushRef (c : Cell) -- PUSHREF (1 ref)
  | pushRefSlice (c : Cell) -- PUSHREFSLICE (1 ref)
  | pushRefCont (code : Cell) -- PUSHREFCONT (ref-based continuation)
  | execute
  | jmpx
  | callxArgs (params : Nat) (retVals : Int) -- CALLXARGS <params>,<retVals> (retVals may be -1)
  | jmpxArgs (params : Nat) -- JMPXARGS <params>
  | callcc                 -- CALLCC
  | jmpxData               -- JMPXDATA
  | callccArgs (params : Nat) (retVals : Int) -- CALLCCARGS <params>,<retVals> (retVals in [-1..14])
  | callxVarArgs           -- CALLXVARARGS
  | jmpxVarArgs            -- JMPXVARARGS
  | callccVarArgs          -- CALLCCVARARGS
  | ret
  | retAlt
  | retBool
  | retVarArgs          -- RETVARARGS
  | retData             -- RETDATA
  | retArgs (n : Nat) -- RETARGS <n>
  | ifjmp
  | ifnotjmp
  | ifelse
  | ifref (code : Slice)       -- IFREF (1 ref)
  | ifnotref (code : Slice)    -- IFNOTREF (1 ref)
  | ifjmpref (code : Slice)    -- IFJMPREF (1 ref)
  | ifnotjmpref (code : Slice) -- IFNOTJMPREF (1 ref)
  | ifrefElse (code : Slice)   -- IFREFELSE (1 ref)
  | ifelseRef (code : Slice)   -- IFELSEREF (1 ref)
  | ifrefElseRef (t : Slice) (f : Slice) -- IFREFELSEREF (2 refs)
  | callRef (code : Slice)     -- CALLREF (1 ref)
  | jmpRef (code : Slice)      -- JMPREF (1 ref)
  | jmpRefData (code : Slice)  -- JMPREFDATA (1 ref)
  | callDict (idx : Nat)       -- CALLDICT <idx>
  | prepareDict (idx : Nat)    -- PREPAREDICT <idx>
  | until             -- UNTIL
  | while_             -- WHILE
  | blkdrop (n : Nat) -- BLKDROP <n>
  | drop2              -- 2DROP
  | debugOp (op : DebugInstr)
  deriving Repr

def CryptoExtInstr.pretty : CryptoExtInstr → String
  | .ecrecover => "ECRECOVER"
  | .secp256k1XonlyPubkeyTweakAdd => "SECP256K1_XONLY_PUBKEY_TWEAK_ADD"
  | .p256ChkSignU => "P256_CHKSIGNU"
  | .p256ChkSignS => "P256_CHKSIGNS"
  | .rist255FromHash => "RIST255_FROMHASH"
  | .rist255Validate => "RIST255_VALIDATE"
  | .rist255Add => "RIST255_ADD"
  | .rist255Sub => "RIST255_SUB"
  | .rist255Mul => "RIST255_MUL"
  | .rist255MulBase => "RIST255_MULBASE"
  | .rist255PushL => "RIST255_PUSHL"
  | .rist255Qvalidate => "RIST255_QVALIDATE"
  | .rist255Qadd => "RIST255_QADD"
  | .rist255Qsub => "RIST255_QSUB"
  | .rist255Qmul => "RIST255_QMUL"
  | .rist255QmulBase => "RIST255_QMULBASE"
  | .blsVerify => "BLS_VERIFY"
  | .blsAggregate => "BLS_AGGREGATE"
  | .blsFastAggregateVerify => "BLS_FASTAGGREGATEVERIFY"
  | .blsAggregateVerify => "BLS_AGGREGATEVERIFY"
  | .blsG1Add => "BLS_G1_ADD"
  | .blsG1Sub => "BLS_G1_SUB"
  | .blsG1Neg => "BLS_G1_NEG"
  | .blsG1Mul => "BLS_G1_MUL"
  | .blsG1MultiExp => "BLS_G1_MULTIEXP"
  | .blsG1Zero => "BLS_G1_ZERO"
  | .blsMapToG1 => "BLS_MAP_TO_G1"
  | .blsG1InGroup => "BLS_G1_INGROUP"
  | .blsG1IsZero => "BLS_G1_ISZERO"
  | .blsG2Add => "BLS_G2_ADD"
  | .blsG2Sub => "BLS_G2_SUB"
  | .blsG2Neg => "BLS_G2_NEG"
  | .blsG2Mul => "BLS_G2_MUL"
  | .blsG2MultiExp => "BLS_G2_MULTIEXP"
  | .blsG2Zero => "BLS_G2_ZERO"
  | .blsMapToG2 => "BLS_MAP_TO_G2"
  | .blsG2InGroup => "BLS_G2_INGROUP"
  | .blsG2IsZero => "BLS_G2_ISZERO"
  | .blsPairing => "BLS_PAIRING"
  | .blsPushR => "BLS_PUSHR"

def CryptoInstr.pretty : CryptoInstr → String
  | .hashExt hashId append rev =>
      let a := if append then "A" else ""
      let r := if rev then "R" else ""
      let idStr := if hashId = 255 then "-1" else toString hashId
      s!"HASHEXT{a}{r} {idStr}"
  | .hashCU => "HASHCU"
  | .hashSU => "HASHSU"
  | .sha256U => "SHA256U"
  | .chkSignU => "CHKSIGNU"
  | .chkSignS => "CHKSIGNS"
  | .ext op => op.pretty

def TonEnvInstr.pretty : TonEnvInstr → String
  | .balance => "BALANCE"
  | .now => "NOW"
  | .blockLt => "BLOCKLT"
  | .lTime => "LTIME"
  | .randSeed => "RANDSEED"
  | .myAddr => "MYADDR"
  | .configRoot => "CONFIGROOT"
  | .configDict => "CONFIGDICT"
  | .configParam opt => if opt then "CONFIGOPTPARAM" else "CONFIGPARAM"
  | .myCode => "MYCODE"
  | .incomingValue => "INCOMINGVALUE"
  | .storageFees => "STORAGEFEES"
  | .prevBlocksInfoTuple => "PREVBLOCKSINFOTUPLE"
  | .prevMcBlocks => "PREVMCBLOCKS"
  | .prevKeyBlock => "PREVKEYBLOCK"
  | .prevMcBlocks100 => "PREVMCBLOCKS_100"
  | .unpackedConfigTuple => "UNPACKEDCONFIGTUPLE"
  | .duePayment => "DUEPAYMENT"
  | .getParam idx => s!"GETPARAM {idx}"
  | .randu256 => "RANDU256"
  | .rand => "RAND"
  | .setRand mix => if mix then "ADDRAND" else "SETRAND"
  | .getGlobVar => "GETGLOBVAR"
  | .getGlob idx => s!"GETGLOB {idx}"
  | .setGlobVar => "SETGLOBVAR"
  | .setGlob idx => s!"SETGLOB {idx}"
  | .accept => "ACCEPT"
  | .setGasLimit => "SETGASLIMIT"
  | .gasConsumed => "GASCONSUMED"
  | .commit => "COMMIT"
  | .ldGrams => "LDGRAMS"
  | .stGrams => "STGRAMS"
  | .ldMsgAddr quiet =>
      let q := if quiet then "Q" else ""
      s!"LDMSGADDR{q}"
  | .parseMsgAddr quiet =>
      let q := if quiet then "Q" else ""
      s!"PARSEMSGADDR{q}"
  | .rewriteStdAddr quiet =>
      let q := if quiet then "Q" else ""
      s!"REWRITESTDADDR{q}"
  | .rewriteVarAddr quiet =>
      let q := if quiet then "Q" else ""
      s!"REWRITEVARADDR{q}"
  | .ldStdAddr quiet =>
      let q := if quiet then "Q" else ""
      s!"LDSTDADDR{q}"
  | .ldOptStdAddr quiet =>
      let q := if quiet then "Q" else ""
      s!"LDOPTSTDADDR{q}"
  | .stStdAddr quiet =>
      let q := if quiet then "Q" else ""
      s!"STSTDADDR{q}"
  | .stOptStdAddr quiet =>
      let q := if quiet then "Q" else ""
      s!"STOPTSTDADDR{q}"
  | .globalId => "GLOBALID"
  | .getGasFee => "GETGASFEE"
  | .getStorageFee => "GETSTORAGEFEE"
  | .getGasFeeSimple => "GETGASFEESIMPLE"
  | .getForwardFee => "GETFORWARDFEE"
  | .getPrecompiledGas => "GETPRECOMPILEDGAS"
  | .getOriginalFwdFee => "GETORIGINALFWDFEE"
  | .getForwardFeeSimple => "GETFORWARDFEESIMPLE"
  | .getExtraBalance => "GETEXTRABALANCE"
  | .inMsgParam idx =>
      match idx with
      | 0 => "INMSG_BOUNCE"
      | 1 => "INMSG_BOUNCED"
      | 2 => "INMSG_SRC"
      | 3 => "INMSG_FWDFEE"
      | 4 => "INMSG_LT"
      | 5 => "INMSG_UTIME"
      | 6 => "INMSG_ORIGVALUE"
      | 7 => "INMSG_VALUE"
      | 8 => "INMSG_VALUEEXTRA"
      | 9 => "INMSG_STATEINIT"
      | _ => s!"INMSGPARAM {idx}"
  | .sendMsg => "SENDMSG"
  | .sendRawMsg => "SENDRAWMSG"
  | .rawReserve => "RAWRESERVE"
  | .rawReserveX => "RAWRESERVEX"
  | .setCode => "SETCODE"
  | .setLibCode => "SETLIBCODE"
  | .changeLib => "CHANGELIB"

def DebugInstr.pretty : DebugInstr → String
  | .dumpStk => "DUMPSTK"
  | .strDump => "STRDUMP"
  | .dump idx => s!"DUMP {idx}"
  | .debug i => s!"DEBUG {i}"
  | .debug1 t => s!"DEBUG_1 {t}"
  | .debug2 t => s!"DEBUG_2 {t}"
  | .debugStr s => s!"DEBUGSTR(bytes={s.bitsRemaining / 8})"
  | .extCall id => s!"EXTCALL {id}"

def TupleInstr.pretty : TupleInstr → String
  | .mktuple n => s!"TUPLE {n}"
  | .index idx => s!"INDEX {idx}"
  | .index2 i j => s!"INDEX2 {i},{j}"
  | .index3 i j k => s!"INDEX3 {i},{j},{k}"
  | .untuple n => s!"UNTUPLE {n}"
  | .unpackFirst n => s!"UNPACKFIRST {n}"
  | .explode maxLen => s!"EXPLODE {maxLen}"
  | .setIndex idx => s!"SETINDEX {idx}"
  | .indexQ idx => s!"INDEXQ {idx}"
  | .setIndexQ idx => s!"SETINDEXQ {idx}"
  | .mktupleVar => "TUPLEVAR"
  | .indexVar => "INDEXVAR"
  | .untupleVar => "UNTUPLEVAR"
  | .unpackFirstVar => "UNPACKFIRSTVAR"
  | .explodeVar => "EXPLODEVAR"
  | .setIndexVar => "SETINDEXVAR"
  | .indexVarQ => "INDEXVARQ"
  | .setIndexVarQ => "SETINDEXVARQ"
  | .tlen => "TLEN"
  | .qtlen => "QTLEN"
  | .isTuple => "ISTUPLE"
  | .last => "LAST"
  | .tpush => "TPUSH"
  | .tpop => "TPOP"

def CellInstr.pretty : CellInstr → String
  | .sdFirst => "SDFIRST"
  | .sdSfx => "SDSFX"
  | .sdSfxRev => "SDSFXREV"
  | .sdPsfx => "SDPSFX"
  | .sdPsfxRev => "SDPSFXREV"
  | .sdCntLead1 => "SDCNTLEAD1"
  | .sdCntTrail1 => "SDCNTTRAIL1"
  | .strefR quiet => if quiet then "STREFRQ" else "STREFR"
  | .endxc => "ENDXC"
  | .sdSubstr => "SDSUBSTR"
  | .scutfirst => "SCUTFIRST"
  | .sskipfirst => "SSKIPFIRST"
  | .scutlast => "SCUTLAST"
  | .sskiplast => "SSKIPLAST"
  | .subslice => "SUBSLICE"
  | .split quiet => if quiet then "SPLITQ" else "SPLIT"
  | .pldRefVar => "PLDREFVAR"
  | .loadLeInt unsigned bytes prefetch quiet =>
      let p := if prefetch then "PLD" else "LD"
      let iu := if unsigned then "U" else "I"
      let q := if quiet then "Q" else ""
      s!"{p}{iu}LE{bytes}{q}"
  | .ldZeroes => "LDZEROES"
  | .ldOnes => "LDONES"
  | .ldSame => "LDSAME"
  | .sdepth => "SDEPTH"
  | .clevel => "CLEVEL"
  | .clevelMask => "CLEVELMASK"
  | .chashI i => s!"CHASHI {i}"
  | .cdepthI i => s!"CDEPTHI {i}"
  | .chashIX => "CHASHIX"
  | .cdepthIX => "CDEPTHIX"
  | .schkBits quiet => if quiet then "SCHKBITSQ" else "SCHKBITS"
  | .schkRefs quiet => if quiet then "SCHKREFSQ" else "SCHKREFS"
  | .schkBitRefs quiet => if quiet then "SCHKBITREFSQ" else "SCHKBITREFS"
  | .bdepth => "BDEPTH"
  | .brefs => "BREFS"
  | .bbitrefs => "BBITREFS"
  | .brembits => "BREMBITS"
  | .bremrefs => "BREMREFS"
  | .brembitrefs => "BREMBITREFS"
  | .bchkBitsImm bits quiet =>
      let q := if quiet then "Q" else ""
      s!"BCHKBITS{q} {bits}"
  | .bchk needBits needRefs quiet =>
      let kind :=
        if needBits && needRefs then "BCHKBITREFS"
        else if needBits then "BCHKBITS"
        else if needRefs then "BCHKREFS"
        else "BCHK"
      let q := if quiet then "Q" else ""
      s!"{kind}{q}"

def CellExtInstr.pretty : CellExtInstr → String
  | .btos => "BTOS"
  | .plduz c => s!"PLDUZ {c}"
  | .ldVarInt signed lenBits =>
      let iu := if signed then "INT" else "UINT"
      s!"LDVAR{iu}(lenBits={lenBits})"
  | .xload quiet =>
      if quiet then "XLOADQ" else "XLOAD"
  | .stVarInt signed lenBits =>
      let iu := if signed then "INT" else "UINT"
      s!"STVAR{iu}(lenBits={lenBits})"
  | .stLeInt unsigned bytes =>
      let iu := if unsigned then "U" else "I"
      s!"ST{iu}LE{bytes}"
  | .stRefConst _ => "STREFCONST"
  | .stRef2Const _ _ => "STREF2CONST"
  | .hashbu => "HASHBU"
  | .cdataSize quiet => if quiet then "CDATASIZEQ" else "CDATASIZE"
  | .sdataSize quiet => if quiet then "SDATASIZEQ" else "SDATASIZE"

def ArithExtInstr.pretty : ArithExtInstr → String
  | .qaddInt n => s!"QADDINT {n}"
  | .qmulInt n => s!"QMULINT {n}"
  | .qeqInt n => s!"QEQINT {n}"
  | .qneqInt n => s!"QNEQINT {n}"
  | .qgtInt n => s!"QGTINT {n}"
  | .fitsConst unsigned quiet bits =>
      let u := if unsigned then "U" else ""
      let q := if quiet then "Q" else ""
      s!"{q}{u}FITS {bits}"
  | .lshiftVar quiet =>
      if quiet then "QLSHIFT_VAR" else "LSHIFT_VAR"
  | .rshiftVar quiet =>
      if quiet then "QRSHIFT_VAR" else "RSHIFT_VAR"
  | .shrMod mulMode addMode d roundMode quiet z =>
      let q := if quiet then "Q" else ""
      let m := if mulMode then "MUL" else ""
      let a := if addMode then "ADD" else ""
      let base :=
        match d with
        | 1 => "RSHIFT"
        | 2 => "MODPOW2"
        | 3 => "RSHIFTMOD"
        | _ => "SHRMOD"
      let suf :=
        if roundMode = -1 then
          ""
        else if roundMode = 0 then
          "R"
        else if roundMode = 1 then
          "C"
        else
          ""
      let hash := if z.isSome then "#" else ""
      s!"{q}{m}{a}{base}{suf}{hash}"
  | .shlDivMod d roundMode addMode quiet z =>
      let q := if quiet then "Q" else ""
      let a := if addMode then "ADD" else ""
      let base :=
        match d with
        | 1 => "LSHIFTDIV"
        | 2 => "LSHIFTMOD"
        | 3 => "LSHIFTDIVMOD"
        | _ => "LSHIFTDIV/MOD"
      let suf :=
        if roundMode = -1 then
          ""
        else if roundMode = 0 then
          "R"
        else if roundMode = 1 then
          "C"
        else
          ""
      let hash := if z.isSome then "#" else ""
      s!"{q}{a}{base}{suf}{hash}"

def ContExtInstr.pretty : ContExtInstr → String
  | .condSel => "CONDSEL"
  | .condSelChk => "CONDSELCHK"
  | .ifretAlt => "IFRETALT"
  | .ifnotretAlt => "IFNOTRETALT"
  | .ifbitjmp i => s!"IFBITJMP {i}"
  | .ifnbitjmp i => s!"IFNBITJMP {i}"
  | .ifbitjmpref i _ => s!"IFBITJMPREF {i}"
  | .ifnbitjmpref i _ => s!"IFNBITJMPREF {i}"
  | .pow2 => "POW2"
  | .fitsx => "FITSX"
  | .ufitsx => "UFITSX"
  | .qand => "QAND"
  | .qor => "QOR"
  | .qxor => "QXOR"
  | .qnot => "QNOT"
  | .qfitsx => "QFITSX"
  | .qufitsx => "QUFITSX"
  | .qbitsize => "QBITSIZE"
  | .qmin => "QMIN"
  | .isnan => "ISNAN"
  | .chknan => "CHKNAN"
  | .qsgn => "QSGN"
  | .qless => "QLESS"
  | .qequal => "QEQUAL"
  | .qleq => "QLEQ"
  | .qgreater => "QGREATER"
  | .qneq => "QNEQ"
  | .qgeq => "QGEQ"
  | .repeat brk => if brk then "REPEATBRK" else "REPEAT"
  | .repeatEnd brk => if brk then "REPEATENDBRK" else "REPEATEND"
  | .until brk => if brk then "UNTILBRK" else "UNTIL"
  | .untilEnd brk => if brk then "UNTILENDBRK" else "UNTILEND"
  | .while brk => if brk then "WHILEBRK" else "WHILE"
  | .whileEnd brk => if brk then "WHILEENDBRK" else "WHILEEND"
  | .again brk => if brk then "AGAINBRK" else "AGAIN"
  | .againEnd brk => if brk then "AGAINENDBRK" else "AGAINEND"
  | .jmpDict idx => s!"JMPDICT {idx}"
  | .pushCtrX => "PUSHCTRX"
  | .popCtrX => "POPCTRX"
  | .setContCtrX => "SETCONTCTRX"
  | .setContCtrMany mask => s!"SETCONTCTRMANY {mask}"
  | .setContCtrManyX => "SETCONTCTRMANYX"
  | .setRetCtr idx => s!"SETRETCTR {idx}"
  | .setAltCtr idx => s!"SETALTCTR {idx}"
  | .popSave idx => s!"POPSAVE {idx}"
  | .saveAltCtr idx => s!"SAVEALTCTR {idx}"
  | .saveBothCtr idx => s!"SAVEBOTHCTR {idx}"
  | .runvm mode => s!"RUNVM {mode}"
  | .runvmx => "RUNVMX"
  | .atexit => "ATEXIT"
  | .atexitAlt => "ATEXITALT"
  | .setExitAlt => "SETEXITALT"
  | .thenret => "THENRET"
  | .thenretAlt => "THENRETALT"
  | .invert => "INVERT"
  | .booleval => "BOOLEVAL"

def Instr.pretty : Instr → String
  | .nop => "NOP"
  | .pushInt .nan => "PUSHNAN"
  | .pushInt (.num n) => s!"PUSHINT {n}"
  | .pushPow2 exp => s!"PUSHPOW2 {exp}"
  | .pushPow2Dec exp => s!"PUSHPOW2DEC {exp}"
  | .pushNegPow2 exp => s!"PUSHNEGPOW2 {exp}"
  | .push idx => s!"PUSH {idx}"
  | .pop idx => s!"POP {idx}"
  | .xchg0 idx => s!"XCHG_0 {idx}"
  | .xchg1 idx => s!"XCHG_1 {idx}"
  | .xchg x y => s!"XCHG {x},{y}"
  | .xchg2 x y => s!"XCHG2 {x},{y}"
  | .xchg3 x y z => s!"XCHG3 {x},{y},{z}"
  | .xcpu x y => s!"XCPU {x},{y}"
  | .xc2pu x y z => s!"XC2PU {x},{y},{z}"
  | .xcpuxc x y z => s!"XCPUXC {x},{y},{Int.ofNat z - 1}"
  | .xcpu2 x y z => s!"XCPU2 {x},{y},{z}"
  | .puxc2 x y z => s!"PUXC2 {x},{Int.ofNat y - 1},{Int.ofNat z - 1}"
  | .puxc x y => s!"PUXC {x},{Int.ofNat y - 1}"
  | .puxcpu x y z => s!"PUXCPU {x},{Int.ofNat y - 1},{Int.ofNat z - 1}"
  | .pu2xc x y z => s!"PU2XC {x},{Int.ofNat y - 1},{Int.ofNat z - 2}"
  | .push2 x y => s!"PUSH2 {x},{y}"
  | .push3 x y z => s!"PUSH3 {x},{y},{z}"
  | .blkSwap x y => s!"BLKSWAP {x},{y}"
  | .blkPush x y => s!"BLKPUSH {x},{y}"
  | .rot => "ROT"
  | .rotRev => "ROTREV"
  | .twoSwap => "2SWAP"
  | .twoDup => "2DUP"
  | .twoOver => "2OVER"
  | .reverse x y => s!"REVERSE {x},{y}"
  | .pick => "PICK"
  | .roll => "ROLL"
  | .rollRev => "ROLLREV"
  | .blkSwapX => "BLKSWX"
  | .reverseX => "REVX"
  | .dropX => "DROPX"
  | .xchgX => "XCHGX"
  | .depth => "DEPTH"
  | .chkDepth => "CHKDEPTH"
  | .onlyTopX => "ONLYTOPX"
  | .onlyX => "ONLYX"
  | .tuck => "TUCK"
  | .pushCtr idx => s!"PUSHCTR {idx}"
  | .popCtr idx => s!"POPCTR {idx}"
  | .setContCtr idx => s!"SETCONTCTR c{idx}"
  | .ctos => "CTOS"
  | .xctos => "XCTOS"
  | .cellExt op => op.pretty
  | .newc => "NEWC"
  | .endc => "ENDC"
  | .endcst => "ENDCST"
  | .ends => "ENDS"
  | .ldu bits => s!"LDU {bits}"
  | .loadInt unsigned prefetch quiet bits =>
      let p := if prefetch then "PLD" else "LD"
      let iu := if unsigned then "U" else "I"
      let q := if quiet then "Q" else ""
      s!"{p}{iu}{q} {bits}"
  | .loadIntVar unsigned prefetch quiet =>
      let p := if prefetch then "PLD" else "LD"
      let iu := if unsigned then "UX" else "IX"
      let q := if quiet then "Q" else ""
      s!"{p}{iu}{q}"
  | .ldref => "LDREF"
  | .ldrefRtos => "LDREFRTOS"
  | .pldRefIdx idx => s!"PLDREFIDX {idx}"
  | .loadSliceX prefetch quiet =>
      let p := if prefetch then "PLD" else "LD"
      let q := if quiet then "Q" else ""
      s!"{p}SLICEX{q}"
  | .loadSliceFixed prefetch quiet bits =>
      let p := if prefetch then "PLD" else "LD"
      let q := if quiet then "Q" else ""
      s!"{p}SLICE{q} {bits}"
  | .sti bits => s!"STI {bits}"
  | .stu bits => s!"STU {bits}"
  | .stIntVar unsigned rev quiet =>
      let iu := if unsigned then "STUX" else "STIX"
      let r := if rev then "R" else ""
      let q := if quiet then "Q" else ""
      s!"{iu}{r}{q}"
  | .stIntFixed unsigned rev quiet bits =>
      let iu := if unsigned then "STU" else "STI"
      let r := if rev then "R" else ""
      let q := if quiet then "Q" else ""
      s!"{iu}{r}{q} {bits}"
  | .stSlice rev quiet =>
      let base := if rev then "STSLICER" else "STSLICE"
      let q := if quiet then "Q" else ""
      s!"{base}{q}"
  | .stb rev quiet =>
      let base := if rev then "STBR" else "STB"
      let q := if quiet then "Q" else ""
      s!"{base}{q}"
  | .stbRef rev quiet =>
      let base := if rev then "STBREFR" else "STBREF"
      let q := if quiet then "Q" else ""
      s!"{base}{q}"
  | .stSliceConst s => s!"STSLICECONST(bits={s.bitsRemaining},refs={s.refsRemaining})"
  | .stZeroes => "STZEROES"
  | .stOnes => "STONES"
  | .stSame => "STSAME"
  | .stref => "STREF"
  | .strefq => "STREFQ"
  | .bbits => "BBITS"
  | .setcp cp => s!"SETCP {cp}"
  | .setcpX => "SETCPX"
  | .ifret => "IFRET"
  | .ifnotret => "IFNOTRET"
  | .if_ => "IF"
  | .ifnot => "IFNOT"
  | .inc => "INC"
  | .qinc => "QINC"
  | .dec => "DEC"
  | .qdec => "QDEC"
  | .negate => "NEGATE"
  | .qnegate => "QNEGATE"
  | .qpow2 => "QPOW2"
  | .add => "ADD"
  | .qadd => "QADD"
  | .addInt n => s!"ADDINT {n}"
  | .sub => "SUB"
  | .qsub => "QSUB"
  | .qsubr => "QSUBR"
  | .subr => "SUBR"
  | .mulInt n => s!"MULINT {n}"
  | .mul => "MUL"
  | .qmul => "QMUL"
  | .min => "MIN"
  | .max => "MAX"
  | .qmax => "QMAX"
  | .minmax => "MINMAX"
  | .qminmax => "QMINMAX"
  | .abs quiet => if quiet then "QABS" else "ABS"
  | .bitsize => "BITSIZE"
  | .ubitsize quiet => if quiet then "QUBITSIZE" else "UBITSIZE"
  | .arithExt op => op.pretty
  | .mulShrModConst d roundMode z =>
      let base :=
        match d with
        | 1 => "MULRSHIFT"
        | 2 => "MULMODPOW2"
        | 3 => "MULRSHIFTMOD"
        | _ => "MULSHR/MOD"
      let suf :=
        if roundMode = -1 then
          ""
        else if roundMode = 0 then
          "F"
        else if roundMode = 1 then
          "R"
        else
          ""
      s!"{base}{suf}# {z}"
  | .divMod d roundMode addMode quiet =>
      let name :=
        (if addMode then "ADD" else "") ++
        (if (d &&& 1) = 1 then "DIV" else "") ++
        (if (d &&& 2) = 2 then "MOD" else "")
      let name := if quiet then "Q" ++ name else name
      let suf :=
        if roundMode = -1 then
          ""
        else if roundMode = 0 then
          "R"
        else if roundMode = 1 then
          "C"
        else
          ""
      name ++ suf
  | .mulDivMod d roundMode addMode quiet =>
      let name :=
        (if addMode then "MULADD" else "MUL") ++
        (if (d &&& 1) = 1 then "DIV" else "") ++
        (if (d &&& 2) = 2 then "MOD" else "")
      let name := if quiet then "Q" ++ name else name
      let suf :=
        if roundMode = -1 then
          ""
        else if roundMode = 0 then
          "R"
        else if roundMode = 1 then
          "C"
        else
          ""
      name ++ suf
  | .lshiftConst quiet bits =>
      let q := if quiet then "Q" else ""
      s!"{q}LSHIFT {bits}"
  | .rshiftConst quiet bits =>
      let q := if quiet then "Q" else ""
      s!"{q}RSHIFT {bits}"
  | .lshift => "LSHIFT"
  | .rshift => "RSHIFT"
  | .equal => "EQUAL"
  | .neq => "NEQ"
  | .saveCtr idx => s!"SAVECTR {idx}"
  | .sameAlt => "SAMEALT"
  | .sameAltSave => "SAMEALTSAVE"
  | .boolAnd => "BOOLAND"
  | .boolOr => "BOOLOR"
  | .composBoth => "COMPOSBOTH"
  | .contExt op => op.pretty
  | .setContArgs copy more => s!"SETCONTARGS {copy},{more}"
  | .setContVarArgs => "SETCONTVARARGS"
  | .setNumVarArgs => "SETNUMVARARGS"
  | .returnArgs n => s!"RETURNARGS {n}"
  | .returnVarArgs => "RETURNVARARGS"
  | .bless => "BLESS"
  | .blessVarArgs => "BLESSVARARGS"
  | .blessArgs copy more => s!"BLESSARGS {copy},{more}"
  | .dictGet intKey unsigned byRef =>
      let iu := if intKey then (if unsigned then "U" else "I") else ""
      let r := if byRef then "REF" else ""
      s!"DICT{iu}GET{r}"
  | .dictGetNear args4 =>
      let iu := if (args4 &&& 8) = 8 then (if (args4 &&& 4) = 4 then "U" else "I") else ""
      let dir := if (args4 &&& 2) = 2 then "PREV" else "NEXT"
      let eq := if (args4 &&& 1) = 1 then "EQ" else ""
      s!"DICT{iu}GET{dir}{eq}"
  | .dictGetMinMax args5 =>
      let iu := if (args5 &&& 4) = 4 then (if (args5 &&& 2) = 2 then "U" else "I") else ""
      let rem := if (args5 &&& 16) = 16 then "REM" else ""
      let mm := if (args5 &&& 8) = 8 then "MAX" else "MIN"
      let r := if (args5 &&& 1) = 1 then "REF" else ""
      s!"DICT{iu}{rem}{mm}{r}"
  | .throw exc => s!"THROW {exc}"
  | .throwIf exc => s!"THROWIF {exc}"
  | .throwIfNot exc => s!"THROWIFNOT {exc}"
  | .throwArg exc => s!"THROWARG {exc}"
  | .throwArgIf exc => s!"THROWARGIF {exc}"
  | .throwArgIfNot exc => s!"THROWARGIFNOT {exc}"
  | .throwAny hasParam hasCond throwCond =>
      let arg := if hasParam then "ARG" else ""
      let cond :=
        if hasCond then
          if throwCond then "IF" else "IFNOT"
        else
          ""
      s!"THROW{arg}ANY{cond}"
  | .try_ => "TRY"
  | .tryArgs p r => s!"TRYARGS {p},{r}"
  | .dictPushConst _ keyBits => s!"DICTPUSHCONST {keyBits}"
  | .dictGetExec unsigned doCall pushZ =>
      let iu := if unsigned then "U" else "I"
      let je := if doCall then "EXEC" else "JMP"
      let z := if pushZ then "Z" else ""
      s!"DICT{iu}GET{je}{z}"
  | .dictSet intKey unsigned byRef mode =>
      let iu := if intKey then (if unsigned then "U" else "I") else ""
      let name :=
        match mode with
        | .set => "SET"
        | .replace => "REPLACE"
        | .add => "ADD"
      let r := if byRef then "REF" else ""
      s!"DICT{iu}{name}{r}"
  | .dictSetB intKey unsigned mode =>
      let iu := if intKey then (if unsigned then "U" else "I") else ""
      let name :=
        match mode with
        | .set => "SET"
        | .replace => "REPLACE"
        | .add => "ADD"
      s!"DICT{iu}{name}B"
  | .dictReplaceB intKey unsigned =>
      let iu := if intKey then (if unsigned then "U" else "I") else ""
      s!"DICT{iu}REPLACEB"
  | .stdict => "STDICT"
  | .skipdict => "SKIPDICT"
  | .lddict preload quiet =>
      let p := if preload then "P" else ""
      let q := if quiet then "Q" else ""
      s!"{p}LDDICT{q}"
  | .and_ => "AND"
  | .or => "OR"
  | .xor => "XOR"
  | .not_ => "NOT"
  | .sgn => "SGN"
  | .less => "LESS"
  | .leq => "LEQ"
  | .greater => "GREATER"
  | .geq => "GEQ"
  | .cmp => "CMP"
  | .qcmp => "QCMP"
  | .sbits => "SBITS"
  | .srefs => "SREFS"
  | .sbitrefs => "SBITREFS"
  | .cdepth => "CDEPTH"
  | .sempty => "SEMPTY"
  | .sdempty => "SDEMPTY"
  | .srempty => "SREMPTY"
  | .sdCntLead0 => "SDCNTLEAD0"
  | .sdCntTrail0 => "SDCNTTRAIL0"
  | .sdEq => "SDEQ"
  | .sdPpfx => "SDPPFX"
  | .sdPpfxRev => "SDPPFXREV"
  | .sdPfx => "SDPFX"
  | .sdPfxRev => "SDPFXREV"
  | .sdLexCmp => "SDLEXCMP"
  | .sdcutfirst => "SDCUTFIRST"
  | .sdskipfirst => "SDSKIPFIRST"
  | .sdcutlast => "SDCUTLAST"
  | .sdskiplast => "SDSKIPLAST"
  | .sdBeginsX quiet =>
      let q := if quiet then "Q" else ""
      s!"SDBEGINSX{q}"
  | .sdBeginsConst quiet pref =>
      let q := if quiet then "Q" else ""
      s!"SDBEGINS{q}(bits={pref.bitsRemaining})"
  | .lessInt n => s!"LESSINT {n}"
  | .qlessInt n => s!"QLESSINT {n}"
  | .eqInt n => s!"EQINT {n}"
  | .gtInt n => s!"GTINT {n}"
  | .neqInt n => s!"NEQINT {n}"
  | .pushNull => "PUSHNULL"
  | .isNull => "ISNULL"
  | .nullSwapIf => "NULLSWAPIF"
  | .nullSwapIfNot => "NULLSWAPIFNOT"
  | .nullRotrIf => "NULLROTRIF"
  | .nullRotrIfNot => "NULLROTRIFNOT"
  | .nullSwapIf2 => "NULLSWAPIF2"
  | .nullSwapIfNot2 => "NULLSWAPIFNOT2"
  | .nullRotrIf2 => "NULLROTRIF2"
  | .nullRotrIfNot2 => "NULLROTRIFNOT2"
  | .tupleOp op => op.pretty
  | .cellOp op => op.pretty
  | .cryptoOp op => op.pretty
  | .tonEnvOp op => op.pretty
  | .debugOp op => op.pretty
  | .dictExt op => s!"{reprStr op}"
  | .blkdrop2 x y => s!"BLKDROP2 {x},{y}"
  | .pushSliceConst s => s!"PUSHSLICE(bits={s.bitsRemaining},refs={s.refsRemaining})"
  | .pushCont code => s!"PUSHCONT(bits={code.bitsRemaining},refs={code.refsRemaining})"
  | .pushRef c => s!"PUSHREF(bits={c.bits.size},refs={c.refs.size})"
  | .pushRefSlice c => s!"PUSHREFSLICE(bits={c.bits.size},refs={c.refs.size})"
  | .pushRefCont c => s!"PUSHREFCONT(bits={c.bits.size},refs={c.refs.size})"
  | .execute => "EXECUTE"
  | .jmpx => "JMPX"
  | .callxArgs params retVals => s!"CALLXARGS {params},{retVals}"
  | .jmpxArgs params => s!"JMPXARGS {params}"
  | .callcc => "CALLCC"
  | .jmpxData => "JMPXDATA"
  | .callccArgs params retVals => s!"CALLCCARGS {params},{retVals}"
  | .callxVarArgs => "CALLXVARARGS"
  | .jmpxVarArgs => "JMPXVARARGS"
  | .callccVarArgs => "CALLCCVARARGS"
  | .ret => "RET"
  | .retAlt => "RETALT"
  | .retBool => "RETBOOL"
  | .retVarArgs => "RETVARARGS"
  | .retData => "RETDATA"
  | .retArgs n => s!"RETARGS {n}"
  | .ifjmp => "IFJMP"
  | .ifnotjmp => "IFNOTJMP"
  | .ifelse => "IFELSE"
  | .ifref _ => "IFREF"
  | .ifnotref _ => "IFNOTREF"
  | .ifjmpref _ => "IFJMPREF"
  | .ifnotjmpref _ => "IFNOTJMPREF"
  | .ifrefElse _ => "IFREFELSE"
  | .ifelseRef _ => "IFELSEREF"
  | .ifrefElseRef _ _ => "IFREFELSEREF"
  | .callRef _ => "CALLREF"
  | .jmpRef _ => "JMPREF"
  | .jmpRefData _ => "JMPREFDATA"
  | .callDict idx => s!"CALLDICT {idx}"
  | .prepareDict idx => s!"PREPAREDICT {idx}"
  | .until => "UNTIL"
  | .while_ => "WHILE"
  | .blkdrop n => s!"BLKDROP {n}"
  | .drop2 => "2DROP"

instance : ToString Instr := ⟨Instr.pretty⟩

instance : BEq Instr := ⟨fun a b => reprStr a == reprStr b⟩

/- The structural `BEq` below is nicer and faster at runtime, but it makes Lean's
elaboration hit the default heartbeat limit due to the size of `Instr`.
Re-enable once we refactor `Instr` into smaller parts. -/
/-
instance : BEq Instr := ⟨fun a b =>
  match a, b with
  | .nop, .nop => true
  | .pushInt x, .pushInt y => x == y
  | .pushPow2 x, .pushPow2 y => x == y
  | .pushPow2Dec x, .pushPow2Dec y => x == y
  | .pushNegPow2 x, .pushNegPow2 y => x == y
  | .push x, .push y => x == y
  | .pop x, .pop y => x == y
  | .xchg0 x, .xchg0 y => x == y
  | .xchg1 x, .xchg1 y => x == y
  | .xchg x1 y1, .xchg x2 y2 => x1 == x2 && y1 == y2
  | .xchg2 x1 y1, .xchg2 x2 y2 => x1 == x2 && y1 == y2
  | .xchg3 x1 y1 z1, .xchg3 x2 y2 z2 => x1 == x2 && y1 == y2 && z1 == z2
  | .xcpu x1 y1, .xcpu x2 y2 => x1 == x2 && y1 == y2
  | .xc2pu x1 y1 z1, .xc2pu x2 y2 z2 => x1 == x2 && y1 == y2 && z1 == z2
  | .xcpuxc x1 y1 z1, .xcpuxc x2 y2 z2 => x1 == x2 && y1 == y2 && z1 == z2
  | .xcpu2 x1 y1 z1, .xcpu2 x2 y2 z2 => x1 == x2 && y1 == y2 && z1 == z2
  | .puxc2 x1 y1 z1, .puxc2 x2 y2 z2 => x1 == x2 && y1 == y2 && z1 == z2
  | .puxc x1 y1, .puxc x2 y2 => x1 == x2 && y1 == y2
  | .puxcpu x1 y1 z1, .puxcpu x2 y2 z2 => x1 == x2 && y1 == y2 && z1 == z2
  | .push2 x1 y1, .push2 x2 y2 => x1 == x2 && y1 == y2
  | .push3 x1 y1 z1, .push3 x2 y2 z2 => x1 == x2 && y1 == y2 && z1 == z2
  | .blkSwap x1 y1, .blkSwap x2 y2 => x1 == x2 && y1 == y2
  | .rot, .rot => true
  | .rotRev, .rotRev => true
  | .twoSwap, .twoSwap => true
  | .twoOver, .twoOver => true
  | .reverse x1 y1, .reverse x2 y2 => x1 == x2 && y1 == y2
  | .tuck, .tuck => true
  | .pushCtr x, .pushCtr y => x == y
  | .popCtr x, .popCtr y => x == y
  | .setContCtr x, .setContCtr y => x == y
  | .ctos, .ctos => true
  | .xctos, .xctos => true
  | .newc, .newc => true
  | .endc, .endc => true
  | .ends, .ends => true
  | .ldu x, .ldu y => x == y
  | .loadInt ux px qx bx, .loadInt uy py qy by_ => ux == uy && px == py && qx == qy && bx == by_
  | .loadIntVar ux px qx, .loadIntVar uy py qy => ux == uy && px == py && qx == qy
  | .ldref, .ldref => true
  | .pldRefIdx x, .pldRefIdx y => x == y
  | .loadSliceX px qx, .loadSliceX py qy => px == py && qx == qy
  | .loadSliceFixed px qx bx, .loadSliceFixed py qy by_ => px == py && qx == qy && bx == by_
  | .sti x, .sti y => x == y
  | .stu x, .stu y => x == y
  | .stIntVar ux rx qx, .stIntVar uy ry qy => ux == uy && rx == ry && qx == qy
  | .stIntFixed ux rx qx bx, .stIntFixed uy ry qy by_ => ux == uy && rx == ry && qx == qy && bx == by_
  | .stSlice rx qx, .stSlice ry qy => rx == ry && qx == qy
  | .stSliceConst x, .stSliceConst y => x.bitPos == y.bitPos && x.refPos == y.refPos && x.cell == y.cell
  | .stZeroes, .stZeroes => true
  | .stOnes, .stOnes => true
  | .stSame, .stSame => true
  | .stref, .stref => true
  | .strefq, .strefq => true
  | .setcp x, .setcp y => x == y
  | .ifret, .ifret => true
  | .ifnotret, .ifnotret => true
  | .if_, .if_ => true
  | .ifnot, .ifnot => true
  | .condSel, .condSel => true
  | .condSelChk, .condSelChk => true
  | .ifretAlt, .ifretAlt => true
  | .ifnotretAlt, .ifnotretAlt => true
  | .ifbitjmp i, .ifbitjmp j => i == j
  | .ifnbitjmp i, .ifnbitjmp j => i == j
  | .ifbitjmpref i x, .ifbitjmpref j y =>
      i == j && x.bitPos == y.bitPos && x.refPos == y.refPos && x.cell == y.cell
  | .ifnbitjmpref i x, .ifnbitjmpref j y =>
      i == j && x.bitPos == y.bitPos && x.refPos == y.refPos && x.cell == y.cell
  | .inc, .inc => true
  | .qinc, .qinc => true
  | .dec, .dec => true
  | .qdec, .qdec => true
  | .negate, .negate => true
  | .qnegate, .qnegate => true
  | .qpow2, .qpow2 => true
  | .add, .add => true
  | .sub, .sub => true
  | .qsub, .qsub => true
  | .qsubr, .qsubr => true
  | .subr, .subr => true
  | .mulInt x, .mulInt y => x == y
  | .mul, .mul => true
  | .qmul, .qmul => true
  | .min, .min => true
  | .max, .max => true
  | .qmax, .qmax => true
  | .minmax, .minmax => true
  | .bitsize, .bitsize => true
  | .qminmax, .qminmax => true
  | .mulShrModConst dx rx zx, .mulShrModConst dy ry zy => dx == dy && rx == ry && zx == zy
  | .divMod dx rx ax qx, .divMod dy ry ay qy => dx == dy && rx == ry && ax == ay && qx == qy
  | .lshiftConst qx bx, .lshiftConst qy by_ => qx == qy && bx == by_
  | .rshiftConst qx bx, .rshiftConst qy by_ => qx == qy && bx == by_
  | .equal, .equal => true
  | .neq, .neq => true
  | .throw x, .throw y => x == y
  | .throwIf x, .throwIf y => x == y
  | .throwIfNot x, .throwIfNot y => x == y
  | .throwAny p1 c1 t1, .throwAny p2 c2 t2 => p1 == p2 && c1 == c2 && t1 == t2
  | .saveCtr x, .saveCtr y => x == y
  | .sameAlt, .sameAlt => true
  | .sameAltSave, .sameAltSave => true
  | .dictPushConst dx nx, .dictPushConst dy ny => dx == dy && nx == ny
  | .dictGet ix ux rx, .dictGet iy uy ry => ix == iy && ux == uy && rx == ry
  | .dictGetExec ux cx zx, .dictGetExec uy cy zy => ux == uy && cx == cy && zx == zy
  | .dictSet ikx ukx rx mx, .dictSet iky uky ry my => ikx == iky && ukx == uky && rx == ry && mx == my
  | .dictReplaceB kx ux, .dictReplaceB ky uy => kx == ky && ux == uy
  | .stdict, .stdict => true
  | .skipdict, .skipdict => true
  | .lddict px qx, .lddict py qy => px == py && qx == qy
  | .and_, .and_ => true
  | .or, .or => true
  | .not_, .not_ => true
  | .sgn, .sgn => true
  | .less, .less => true
  | .leq, .leq => true
  | .greater, .greater => true
  | .geq, .geq => true
  | .cmp, .cmp => true
  | .qcmp, .qcmp => true
  | .sbits, .sbits => true
  | .srefs, .srefs => true
  | .sbitrefs, .sbitrefs => true
  | .sempty, .sempty => true
  | .sdempty, .sdempty => true
  | .srempty, .srempty => true
  | .sdCntTrail0, .sdCntTrail0 => true
  | .sdEq, .sdEq => true
  | .sdPpfx, .sdPpfx => true
  | .sdPpfxRev, .sdPpfxRev => true
  | .sdPfx, .sdPfx => true
  | .sdPfxRev, .sdPfxRev => true
  | .sdLexCmp, .sdLexCmp => true
  | .sdcutfirst, .sdcutfirst => true
  | .sdskipfirst, .sdskipfirst => true
  | .sdcutlast, .sdcutlast => true
  | .sdskiplast, .sdskiplast => true
  | .sdBeginsX qx, .sdBeginsX qy => qx == qy
  | .sdBeginsConst qx sx, .sdBeginsConst qy sy =>
      qx == qy && sx.bitPos == sy.bitPos && sx.refPos == sy.refPos && sx.cell == sy.cell
  | .lessInt x, .lessInt y => x == y
  | .qlessInt x, .qlessInt y => x == y
  | .eqInt x, .eqInt y => x == y
  | .gtInt x, .gtInt y => x == y
  | .neqInt x, .neqInt y => x == y
  | .pushNull, .pushNull => true
  | .isNull, .isNull => true
  | .nullSwapIfNot, .nullSwapIfNot => true
  | .mktuple x, .mktuple y => x == y
  | .index x, .index y => x == y
  | .untuple x, .untuple y => x == y
  | .blkdrop2 x1 y1, .blkdrop2 x2 y2 => x1 == x2 && y1 == y2
  | .pushSliceConst x, .pushSliceConst y => x.bitPos == y.bitPos && x.refPos == y.refPos && x.cell == y.cell
  | .pushCont x, .pushCont y => x.bitPos == y.bitPos && x.refPos == y.refPos && x.cell == y.cell
  | .execute, .execute => true
  | .jmpx, .jmpx => true
  | .callxArgs px rx, .callxArgs py ry => px == py && rx == ry
  | .jmpxArgs x, .jmpxArgs y => x == y
  | .callcc, .callcc => true
  | .jmpxData, .jmpxData => true
  | .callccArgs px rx, .callccArgs py ry => px == py && rx == ry
  | .callxVarArgs, .callxVarArgs => true
  | .jmpxVarArgs, .jmpxVarArgs => true
  | .callccVarArgs, .callccVarArgs => true
  | .ret, .ret => true
  | .retAlt, .retAlt => true
  | .retBool, .retBool => true
  | .retArgs x, .retArgs y => x == y
  | .ifjmp, .ifjmp => true
  | .ifnotjmp, .ifnotjmp => true
  | .ifelse, .ifelse => true
  | .ifref x, .ifref y => x.bitPos == y.bitPos && x.refPos == y.refPos && x.cell == y.cell
  | .ifnotref x, .ifnotref y => x.bitPos == y.bitPos && x.refPos == y.refPos && x.cell == y.cell
  | .ifjmpref x, .ifjmpref y => x.bitPos == y.bitPos && x.refPos == y.refPos && x.cell == y.cell
  | .ifnotjmpref x, .ifnotjmpref y => x.bitPos == y.bitPos && x.refPos == y.refPos && x.cell == y.cell
  | .ifrefElse x, .ifrefElse y => x.bitPos == y.bitPos && x.refPos == y.refPos && x.cell == y.cell
  | .ifelseRef x, .ifelseRef y => x.bitPos == y.bitPos && x.refPos == y.refPos && x.cell == y.cell
  | .ifrefElseRef x1 y1, .ifrefElseRef x2 y2 =>
      x1.bitPos == x2.bitPos && x1.refPos == x2.refPos && x1.cell == x2.cell &&
      y1.bitPos == y2.bitPos && y1.refPos == y2.refPos && y1.cell == y2.cell
  | .callRef x, .callRef y => x.bitPos == y.bitPos && x.refPos == y.refPos && x.cell == y.cell
  | .jmpRef x, .jmpRef y => x.bitPos == y.bitPos && x.refPos == y.refPos && x.cell == y.cell
  | .jmpRefData x, .jmpRefData y => x.bitPos == y.bitPos && x.refPos == y.refPos && x.cell == y.cell
  | .callDict x, .callDict y => x == y
  | .while_, .while_ => true
  | .blkdrop x, .blkdrop y => x == y
  | .drop2, .drop2 => true
  | .balance, .balance => true
  | .now, .now => true
  | .getParam x, .getParam y => x == y
  | .randu256, .randu256 => true
  | .rand, .rand => true
  | .setRand x, .setRand y => x == y
  | .getGlobVar, .getGlobVar => true
  | .getGlob x, .getGlob y => x == y
  | .setGlobVar, .setGlobVar => true
  | .setGlob x, .setGlob y => x == y
  | .accept, .accept => true
  | .setGasLimit, .setGasLimit => true
  | .gasConsumed, .gasConsumed => true
  | .commit, .commit => true
  | .ldGrams, .ldGrams => true
  | .stGrams, .stGrams => true
  | .ldMsgAddr qx, .ldMsgAddr qy => qx == qy
  | .rewriteStdAddr qx, .rewriteStdAddr qy => qx == qy
  | .hashCU, .hashCU => true
  | .hashSU, .hashSU => true
  | .chkSignU, .chkSignU => true
  | .chkSignS, .chkSignS => true
  | .sendMsg, .sendMsg => true
  | .sendRawMsg, .sendRawMsg => true
  | .rawReserve, .rawReserve => true
  | _, _ => false⟩
-/

end TvmLean
