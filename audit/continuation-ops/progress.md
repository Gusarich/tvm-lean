# Continuation Audit Progress

## Stats
- Completed: 98/98
- Running: 0
- Bugs reported: 61 (good: 60, bad: 0, pending: 1)
- Fuzz coverage: 98/98 continuation suites configured with instruction-specific fuzz generators (93 `mkContMutationFuzzSpecWithProfile` + 5 explicit per-instr generators)
- Fuzz target: 500 cases per continuation suite (49,000 total)
- Replay-era validation (before custom mutator rollout): 98/98 pass (`audit/continuation-ops/fuzz_validation_20260212_095402.log`)
- Custom-mutator validation (post-RUNVM fix): 98/98 pass (`audit/continuation-ops/fuzz_validation_custom_20260212_123542_post_runvm_fix.log`)
- Fuzz config check: 98/98 continuation suites declare exactly 500 fuzz cases; 0 replay fuzz specs remain in `Tests/Instr/Cont`

## Instances

| ID | Instruction | Status | Findings |
|----|-------------|--------|----------|
| A001 | IF | done | matched C++ after switching to `VM.call`; 35 oracle |
| A002 | IFNOT | done | matched C++ after switching to `VM.call`; 39 oracle |
| A003 | IFJMP | done | matched C++ after switching to `VM.jump`; 42 oracle |
| A004 | IFNOTJMP | done | matched C++; 36 oracle |
| A005 | IFELSE | done | matched C++; 39 oracle |
| A006 | CONDSEL | done | matched C++ after adding `checkUnderflow 3`; 36 oracle |
| A007 | CONDSELCHK | done | matched C++ after adding `checkUnderflow 3`; 33 oracle |
| A008 | IFRET | done | matched C++; 38 oracle |
| A009 | IFNOTRET | done | matched C++; 39 oracle |
| A010 | IFRETALT | done | matched C++; 54 oracle |
| A011 | IFNOTRETALT | done | matched C++; 39 oracle |
| A012 | REPEAT | done | matched C++ after fixing repeat-count NaN error mapping; 41 oracle |
| A013 | REPEATEND | done | matched C++ after `extractCc 0` + repeat tail underflow alignment; 44 oracle |
| A014 | UNTIL | done | matched C++ after `extractCc 1` / `untilEnd extractCc 0`; 37 oracle |
| A015 | UNTILEND | done | matched C++ with runtime `untilBody` jump-underflow parity; 39 oracle |
| A016 | WHILE | done | matched C++ after restoring upfront `checkUnderflow 2`; 51 oracle |
| A017 | WHILEEND | done | matched C++; 44 oracle |
| A018 | AGAIN | done | matched C++ with `AGAINBRK` capture via `extractCc 3`; 42 oracle |
| A019 | AGAINEND | done | matched C++ with `AGAINEND` capture via `extractCc 0`; 40 oracle |
| A020 | REPEATBRK | done | matched C++; corrected unit expectation for `c1_envelope_if` over ordinary `extractCc(1)` result; 49 oracle |
| A021 | REPEATENDBRK | done | matched C++; 39 oracle |
| A022 | UNTILBRK | done | matched C++ after runtime `untilBody` false-branch jump-underflow parity fix; 39 oracle |
| A023 | UNTILENDBRK | done | matched C++; 45 oracle |
| A024 | WHILEBRK | done | matched C++ after runtime `whileCond` false-branch jump-underflow parity fix; 42 oracle |
| A025 | WHILEENDBRK | done | matched C++; 38 oracle |
| A026 | AGAINBRK | done | matched C++ after runtime `.againBody` ordering fix; 42 oracle |
| A027 | AGAINENDBRK | done | matched C++; removed invalid `initCregs` oracle-only assumptions; 40 oracle |
| A028 | IFBITJMP | done | matched C++ after pop/re-push operand-order fix; 44 oracle |
| A029 | IFNBITJMP | done | matched C++; 44 oracle |
| A030 | IFBITJMPREF | done | matched C++; 47 oracle |
| A031 | IFNBITJMPREF | done | matched C++ after pop/re-push operand-order fix; 42 oracle |
| A032 | IFREF | done | matched C++ after restoring full `VM.call` semantics for ref-call path; 36 oracle |
| A033 | IFNOTREF | done | matched C++ after restoring full `VM.call` semantics for ref-call path; 49 oracle |
| A034 | IFJMPREF | done | matched C++ after restoring `VM.jump` semantics on taken branch; 36 oracle |
| A035 | IFNOTJMPREF | done | matched C++ after restoring `VM.jump` semantics on taken branch; 42 oracle |
| A036 | IFREFELSE | done | matched C++ after restoring `VM.call` semantics; 45 oracle |
| A037 | IFELSEREF | done | matched C++ after restoring `VM.call` semantics; 63 oracle |
| A038 | IFREFELSEREF | done | matched C++ after restoring `VM.call` semantics and selected-ref special rejection parity; 48 oracle |
| A039 | CALLREF | done | matched C++ after special-cell rejection parity before `VM.call`; 34 oracle |
| A040 | JMPREF | done | matched C++ after special-cell rejection parity before `VM.jump`; 40 oracle |
| A041 | JMPREFDATA | done | matched C++ after ref-load/special-check/push-code/jump ordering alignment; 44 oracle |
| A042 | CALLDICT | done | matched C++ after `idx &&& 0x3fff` canonicalization; 42 oracle |
| A043 | EXECUTE | done | matched C++; fixed one unit oracle-assumption in raw jump-to-`quit0` path; 46 oracle |
| A044 | JMPX | done | matched C++; 43 oracle |
| A045 | CALLCC | done | matched C++; removed two oracle-only captured-stack assumptions unsupported by runner token model; 43 oracle |
| A046 | RETDATA | done | matched C++; removed two oracle-only captured-stack assumptions unsupported by runner token model; 36 oracle |
| A047 | RUNVMX | done | matched C++ after NaN/range, commit-level, and OOG-check parity fixes; 45 oracle |
| A048 | CALLDICT_LONG | done | matched C++; 42 oracle |
| A049 | PUSHCTR | done | matched C++; pruned four oracle type-order cases that depend on oracle c0..c3 init mismatch; 39 oracle |
| A050 | RET | done | matched C++ after fixing jump-path cdata re-application in `VM.jump`; 43 oracle |
| A051 | RETALT | done | matched C++; 41 oracle |
| A052 | RETBOOL | done | matched C++; 50 oracle |
| A053 | JMPXDATA | done | matched C++; 51 oracle |
| A054 | CALLXVARARGS | done | matched C++ after NaN vararg pop error-mapping fix (`rangeChk`); 52 oracle |
| A055 | RETVARARGS | done | matched C++ after NaN vararg pop error-mapping fix (`rangeChk`); 46 oracle |
| A056 | JMPXVARARGS | done | matched C++ after NaN params pop error-mapping fix (`rangeChk`); 40 oracle |
| A057 | CALLCCVARARGS | done | matched C++ after NaN vararg pop fix and `extractCc(copy=depth)` gas parity fix; 63 oracle |
| A058 | RETURNVARARGS | done | matched C++; 51 oracle |
| A059 | SETCONTVARARGS | done | matched C++ after NaN vararg pop error-mapping fix (`rangeChk`); 52 oracle |
| A060 | SETNUMVARARGS | done | matched C++ after NaN vararg pop error-mapping fix (`rangeChk`); 48 oracle |
| A061 | BLESS | done | matched C++; 62 oracle |
| A062 | BLESSVARARGS | done | matched C++ after NaN `more` pop error-mapping fix (`rangeChk`); 51 oracle |
| A063 | PUSHCTRX | done | matched C++; 51 oracle |
| A064 | POPCTRX | done | matched C++ after dynamic ctr-index validation-before-pop fix; 51 oracle |
| A065 | SETCONTCTRX | done | matched C++; 54 oracle |
| A066 | SETCONTCTRMANYX | done | matched C++; 60 oracle |
| A067 | BOOLAND | done | matched C++ after adding upfront `checkUnderflow 2`; 42 oracle |
| A068 | BOOLOR | done | matched C++ after adding upfront `checkUnderflow 2`; 39 oracle |
| A069 | COMPOSBOTH | done | matched C++ after adding upfront `checkUnderflow 2`; 41 oracle |
| A070 | ATEXIT | done | matched C++; 46 oracle |
| A071 | ATEXITALT | done | matched C++; 34 oracle |
| A072 | SETEXITALT | done | matched C++; 31 oracle |
| A073 | THENRET | done | matched C++; 38 oracle |
| A074 | THENRETALT | done | matched C++; 32 oracle |
| A075 | INVERT | done | matched C++; 32 oracle |
| A076 | BOOLEVAL | done | matched C++ after booleval c0/c1+jump ordering fix; 39 oracle |
| A077 | SAMEALT | done | matched C++; 43 oracle |
| A078 | SAMEALTSAVE | done | matched C++; 48 oracle |
| A079 | SETCONTCTRMANY | done | matched C++; 52 oracle |
| A080 | CALLCCARGS | done | matched C++; 50 oracle |
| A081 | JMPDICT | done | matched C++ after idx canonicalization (`idx &&& 0x3fff`); 44 oracle |
| A082 | PREPAREDICT | done | matched C++ after idx canonicalization (`idx &&& 0x3fff`); 42 oracle |
| A083 | JMPXARGS | done | matched C++ after removing opcode-local truncation/gas and delegating stack shaping to `VM.jump`; 47 oracle |
| A084 | RETARGS | done | matched C++ after params canonicalization (`args &&& 0x0f`); 41 oracle |
| A085 | RETURNARGS | done | matched C++ after params canonicalization (`count &&& 0x0f`); 44 oracle |
| A086 | SETCONTARGS | done | matched C++; 38 oracle |
| A087 | BLESSARGS | done | matched C++; 43 oracle |
| A088 | SETCONTCTR | done | matched C++ after idx canonicalization (`idx &&& 0x0f`); 51 oracle |
| A089 | SETRETCTR | done | matched C++; 49 oracle |
| A090 | SETALTCTR | done | matched C++; 47 oracle |
| A091 | POPSAVE | done | matched C++ after duplicate-define tolerance in c0-save path; 55 oracle |
| A092 | SAVECTR | done | matched C++ after idx canonicalization + invalid-index typeChk mapping parity; 46 oracle |
| A093 | SAVEALTCTR | done | matched C++ after invalid-index typeChk mapping parity; 46 oracle |
| A094 | SAVEBOTHCTR | done | matched C++ after duplicate-define no-op parity in c0/c1 savelists; 42 oracle |
| A095 | RUNVM | done | matched C++ after immediate canonicalization, restore-parent state parity, invalid-opcode gas-bit parity fixes, and OOG return-code inversion parity; 50 oracle |
| A096 | POPCTR | done | matched C++ after `set`-failure→`typeChk` mapping parity; 53 oracle |
| A097 | CALLXARGS | done | matched C++; 55 oracle |
| A098 | CALLXARGS_1 | done | matched C++; 47 oracle |

## Bug Outcomes

| Bug | Title | Outcome | Notes |
|-----|-------|---------|-------|
| B001 | `IF` used `callTo` instead of full `call` semantics | fixed | `TvmLean/Semantics/Exec/Flow/If.lean` |
| B002 | `IFNOT` used `callTo` instead of full `call` semantics | fixed | `TvmLean/Semantics/Exec/Flow/Ifnot.lean` |
| B003 | `IFJMP` used `jumpTo` instead of full `jump` semantics | fixed | `TvmLean/Semantics/Exec/Flow/Ifjmp.lean` |
| B004 | `CONDSEL`/`CONDSELCHK` lacked upfront underflow guard | fixed | `TvmLean/Semantics/Exec/Cont/CondSel.lean` |
| B005 | `VM.jump` ignored continuation captured-stack merge | fixed | `TvmLean/Semantics/VM/Ops/Cont.lean` |
| B006 | Repeat count `NaN` mapped to wrong error (`intOv` vs C++ `rangeChk`) | fixed | `TvmLean/Semantics/Exec/Flow/LoopExt.lean` |
| B007 | `REPEATEND` used current `cc` instead of `extract_cc(0)` | fixed | `TvmLean/Semantics/Exec/Flow/LoopExt.lean` |
| B008 | `UNTIL`/`UNTILEND` capture path used wrong continuation source | fixed | `TvmLean/Semantics/Exec/Flow/Until.lean`, `TvmLean/Semantics/Exec/Flow/LoopExt.lean` |
| B009 | `repeatBody(count=0)` missed C++ nargs underflow check before jumping `after` | fixed | `TvmLean/Semantics/Step/Step.lean` |
| B010 | `.while_` missed C++ `check_underflow(2)` before pop/type checks | fixed | `TvmLean/Semantics/Exec/Flow/While.lean` |
| B011 | `IFBITJMP` consumed operand using fetch-like semantics instead of pop/re-push order | fixed | `TvmLean/Semantics/Exec/Flow/IfBitJmp.lean` |
| B012 | `whileCond(false)` runtime path missed jump-time `after.nargs` underflow parity | fixed | `TvmLean/Semantics/Step/Step.lean`, `TvmLean/Semantics/Exec/Flow/Runvm.lean`, `TvmLean/Semantics/Step/Trace.lean` |
| B013 | `untilBody(false)` runtime path missed jump-time `body.nargs` underflow parity | fixed | `TvmLean/Semantics/Step/Step.lean`, `TvmLean/Semantics/Exec/Flow/Runvm.lean` |
| B014 | `.againBody` no-`c0` runtime branch had C++-mismatched install/jump ordering | fixed | `TvmLean/Semantics/Step/Step.lean`, `TvmLean/Semantics/Exec/Flow/Runvm.lean` |
| B015 | `IFNBITJMPREF` used fetch-like operand access instead of C++ pop/re-push order | fixed | `TvmLean/Semantics/Exec/Flow/IfBitJmp.lean` |
| B016 | `IFREF`/`IFNOTREF` used `callTo` instead of full `VM.call` semantics | fixed | `TvmLean/Semantics/Exec/Flow/Ifref.lean`, `TvmLean/Semantics/Exec/Flow/Ifnotref.lean` |
| B017 | `IFJMPREF` taken path used `jumpTo` instead of full `VM.jump` semantics | fixed | `TvmLean/Semantics/Exec/Flow/Ifjmpref.lean` |
| B018 | `IFNOTJMPREF` taken path used `jumpTo` instead of full `VM.jump` semantics | fixed | `TvmLean/Semantics/Exec/Flow/Ifnotjmpref.lean` |
| B019 | `IFREFELSE` used `callTo` instead of full `VM.call` semantics | fixed | `TvmLean/Semantics/Exec/Flow/IfrefElse.lean` |
| B020 | `IFELSEREF` used `callTo` instead of full `VM.call` semantics | fixed | `TvmLean/Semantics/Exec/Flow/IfelseRef.lean` |
| B021 | `IFREFELSEREF` used `callTo` and missed selected-ref special rejection parity | fixed | `TvmLean/Semantics/Exec/Flow/IfrefElseRef.lean` |
| B022 | `CALLREF` missed special-cell rejection parity before call | fixed | `TvmLean/Semantics/Exec/Flow/CallRef.lean` |
| B023 | `JMPREF`/`JMPREFDATA` missed special-cell rejection parity before jump | fixed | `TvmLean/Semantics/Exec/Flow/JmpRef.lean` |
| B024 | `JMPREFDATA` ordering diverged from C++ (`load`/`check`/`push_code`/`jump`) | fixed | `TvmLean/Semantics/Exec/Flow/JmpRef.lean` |
| B025 | `CALLDICT` missed C++ argument canonicalization (`args &= 0x3fff`) | fixed | `TvmLean/Semantics/Exec/Flow/CallDict.lean` |
| B026 | Oracle harness ignores `OracleGasLimits`/`initCregs`/`initC7` when invoking Fift | pending | `Tests/Harness/OracleHarness.lean`, `TvmLean/Validation/Oracle/Runner.lean` |
| B027 | `RUNVMX` parsed `NaN` gas args with wrong error mapping (needed `rangeChk`) | fixed | `TvmLean/Semantics/Exec/Flow/Runvm.lean` |
| B028 | `RUNVMX` parsed `NaN` `stack_size` with wrong error mapping (needed `rangeChk`) | fixed | `TvmLean/Semantics/Exec/Flow/Runvm.lean` |
| B029 | `RUNVMX try_commit` accepted non-zero-level `c4`/`c5` (C++ rejects) | fixed | `TvmLean/Semantics/Exec/Flow/Runvm.lean` |
| B030 | `RUNVMX` missed immediate OOG checks after key gas/stack-gas charges | fixed | `TvmLean/Semantics/Exec/Flow/Runvm.lean` |
| B031 | `CALLCC`/`RETDATA`/`PUSHCTR` oracle cases assumed unsupported continuation-init states in runner | fixed | `Tests/Instr/Cont/CALLCC.lean`, `Tests/Instr/Cont/RETDATA.lean`, `Tests/Instr/Cont/PUSHCTR.lean` |
| B032 | `VM.jump` re-applied active continuation `cdata` after jump-time shaping (RET mismatch) | fixed | `TvmLean/Semantics/VM/Ops/Cont.lean` |
| B033 | `CALLXVARARGS` mapped NaN vararg pop to `intOv` instead of C++ `rangeChk` | fixed | `TvmLean/Semantics/Exec/Flow/CallxVarArgs.lean` |
| B034 | `RETVARARGS` mapped NaN vararg pop to `intOv` instead of C++ `rangeChk` | fixed | `TvmLean/Semantics/Exec/Flow/RetVarArgs.lean` |
| B035 | `JMPXVARARGS` mapped NaN params pop to `intOv` instead of C++ `rangeChk` | fixed | `TvmLean/Semantics/Exec/Flow/JmpxVarArgs.lean` |
| B036 | `BLESSVARARGS` mapped NaN `more` pop to `intOv` instead of C++ `rangeChk` | fixed | `TvmLean/Semantics/Exec/Cont/Bless.lean` |
| B037 | `SETCONTVARARGS` mapped NaN `copy/more` pop to `intOv` instead of C++ `rangeChk` | fixed | `TvmLean/Semantics/Exec/Cont/SetContVarArgs.lean` |
| B038 | `SETNUMVARARGS` mapped NaN `more` pop to `intOv` instead of C++ `rangeChk` | fixed | `TvmLean/Semantics/Exec/Cont/SetNumVarArgs.lean` |
| B039 | `VM.extractCc` charged split gas when `copy == depth` (C++ charges only for strict split) | fixed | `TvmLean/Semantics/Exec/Common.lean` |
| B040 | `BOOLOR` missed upfront C++ `check_underflow(2)` before continuation type checks | fixed | `TvmLean/Semantics/Exec/Cont/BoolOr.lean` |
| B041 | `POPCTRX` validated dynamic ctr index after value pop (C++ checks index first) | fixed | `TvmLean/Semantics/Exec/Cont/ChangeExt.lean` |
| B042 | `COMPOSBOTH` missed upfront C++ `check_underflow(2)` before continuation type checks | fixed | `TvmLean/Semantics/Exec/Cont/ComposBoth.lean` |
| B043 | `BOOLAND` missed upfront C++ `check_underflow(2)` before continuation type checks | fixed | `TvmLean/Semantics/Exec/Cont/BoolAnd.lean` |
| B044 | `BOOLEVAL` used C++-mismatched order for `extractCc` / `c0,c1` setup / jump | fixed | `TvmLean/Semantics/Exec/Cont/AtExit.lean` |
| B045 | `JMPDICT` missed C++ immediate canonicalization (`args &= 0x3fff`) | fixed | `TvmLean/Semantics/Exec/Flow/LoopExt.lean` |
| B046 | `PREPAREDICT` missed C++ immediate canonicalization (`args &= 0x3fff`) | fixed | `TvmLean/Semantics/Exec/Flow/PrepareDict.lean` |
| B047 | `JMPXARGS` performed opcode-local stack truncation/gas instead of C++ `jump(..., pass_args)` path | fixed | `TvmLean/Semantics/Exec/Flow/JmpxArgs.lean` |
| B048 | `RETARGS` missed C++ params canonicalization (`args &= 15`) before return | fixed | `TvmLean/Semantics/Exec/Flow/RetArgs.lean` |
| B049 | `RETURNARGS` missed C++ params canonicalization (`count &= 15`) before return | fixed | `TvmLean/Semantics/Exec/Cont/ReturnArgs.lean` |
| B050 | `SETCONTCTR` missed C++ idx canonicalization (`idx &= 15`) | fixed | `TvmLean/Semantics/Exec/Cont/SetContCtr.lean` |
| B051 | `POPSAVE` propagated duplicate c0-save define failure (C++ treats as non-fatal no-op) | fixed | `TvmLean/Semantics/Exec/Cont/ChangeExt.lean` |
| B052 | `SAVECTR` lacked C++ arg canonicalization (`idx &= 15`) and invalid-index typeChk path parity | fixed | `TvmLean/Semantics/Exec/Cont/SaveCtr.lean` |
| B053 | `SAVEALTCTR` mapped invalid direct idx to `rangeChk` instead of C++ `typeChk` | fixed | `TvmLean/Semantics/Exec/Cont/ChangeExt.lean` |
| B054 | `SAVEBOTHCTR` wrongly propagated duplicate-define failures (C++ ignores define failures) | fixed | `TvmLean/Semantics/Exec/Cont/ChangeExt.lean` |
| B055 | `POPCTR` propagated invalid-index `rangeChk` instead of C++ `throw_typechk(st->set(...))` behavior | fixed | `TvmLean/Semantics/Exec/Cont/PopCtr.lean` |
| B056 | `RUNVM` immediate path missed C++ canonicalization (`exec_runvm(..., args & 4095)`) | fixed | `TvmLean/Semantics/Exec/Flow/Runvm.lean` |
| B057 | `RUNVM` restore-parent path missed C++ propagation of child `libraries`/`chksgnCounter`/`loadedCells` | fixed | `TvmLean/Semantics/Exec/Flow/Runvm.lean` |
| B058 | `RUNVM` child invalid-opcode gas-bit charging diverged from C++ dummy-dispatch behavior | fixed | `TvmLean/Semantics/Exec/Flow/Runvm.lean` |
| B059 | `CONDSELCHK` custom fuzz emitted oracle-unsupported stack tokens (non-full slices / non-empty tuples / non-`quit(0)` continuations) | fixed | `Tests/Instr/Cont/CONDSELCHK.lean` |
| B060 | `ADD` missed C++ underflow-first precedence (`check_underflow(2)` before typed pops), causing `CALLREF` custom-mutator mismatches (`lean=7`, `oracle=2`) on depth-1 non-int add bodies | fixed | `TvmLean/Semantics/Exec/Arith/Add.lean`; validated by `CALLREF` fuzz rerun |
| B061 | `RUNVM` custom-mutator fuzz reveals Lean/oracle stack divergence on mutated `mode8/return-gas` seed (OOG return-code inversion) | fixed | `TvmLean/Semantics/Exec/Flow/Runvm.lean`; full continuation fuzz sweep now passes 98/98 (`audit/continuation-ops/fuzz_validation_custom_20260212_123542_post_runvm_fix.log`) |
