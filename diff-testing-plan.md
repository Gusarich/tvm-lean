# TVM Lean Diff Testing Plan

Repo overview: `docs/START_HERE.md`.

## Goal

Validate the Lean TVM implementation against real historical TON blockchain transactions by comparing execution results (exit code, gas used, final state) between the Lean VM and actual on-chain outcomes.

## Architecture Overview

```
┌─────────────────────────────────────────────────────────────────────┐
│                        Transaction Source                           │
│                  (ClickHouse indexer / TON API)                     │
└─────────────────────────────────────────────────────────────────────┘
                                  │
                                  ▼
┌─────────────────────────────────────────────────────────────────────┐
│                     State Reconstruction                            │
│              (TxTracer-core / direct API calls)                     │
│                                                                     │
│   Collects for each transaction:                                    │
│   • Account code BOC (at that block)                                │
│   • Account data BOC (c4, at that block)                            │
│   • Incoming message cell + body slice                              │
│   • Block config / c7 tuple (required for full register diff; via Sandbox) │
│   • Library cells (if any)                                          │
└─────────────────────────────────────────────────────────────────────┘
                                  │
                                  ▼
┌─────────────────────────────────────────────────────────────────────┐
│                      Test Case Generator                            │
│                                                                     │
│   Produces JSON/binary test fixtures:                               │
│   {                                                                 │
│     "tx_hash": "...",                                               │
│     "code_boc": "<base64>",                                         │
│     "data_boc": "<base64>",                                         │
│     "stack_init": {                                                 │
│       "balance_grams": "123",                                       │
│       "msg_balance_grams": "456",                                   │
│       "now": "1700000000",                                          │
│       "lt": "12345678900001",                                       │
│       "rand_seed": "0",                                             │
│       "storage_fees": "0",                                          │
│       "due_payment": "0",                                           │
│       "in_msg_boc": "<base64>",                                     │
│       "in_msg_body_boc": "<base64>",                                │
│       "in_msg_extern": false                                        │
│     },                                                              │
│     "expected": {                                                   │
│       "exit_code": 0,                                               │
│       "gas_used": "12345",                                          │
│       "gas_limit": "1000000",                                       │
│       "gas_max": "1000000",                                         │
│       "gas_credit": "0",                                            │
│       "c4_boc": "<base64>",                                         │
│       "c5_boc": "<base64>",                                         │
│       "c7": { "type": "tuple", "items": [/* ... */] }               │
│     }                                                               │
│   }                                                                 │
└─────────────────────────────────────────────────────────────────────┘
                                  │
                    ┌─────────────┴─────────────┐
                    ▼                           ▼
         ┌──────────────────┐        ┌──────────────────┐
         │     Lean VM      │        │   Ground Truth   │
         │                  │        │  (from indexer)  │
         │  tvm-lean        │        │                  │
         │  --code X.boc    │        │  exit_code: 0    │
         │  --data Y.boc    │        │  gas_used: 12345 │
         │  --msg Z.boc     │        │                  │
         └──────────────────┘        └──────────────────┘
                    │                           │
                    └─────────────┬─────────────┘
                                  ▼
                    ┌──────────────────────────┐
                    │       Comparator         │
                    │                          │
                    │  • exit_code match?      │
                    │  • gas_used match?       │
                    │  • c4 cell match?        │
                    │  • c5 (actions) match?   │
                    │  • c7 tuple match?       │
                    └──────────────────────────┘
                                  │
                                  ▼
                    ┌──────────────────────────┐
                    │     Results Database     │
                    │                          │
                    │  • PASS / FAIL / SKIP    │
                    │  • Discrepancy details   │
                    │  • Unsupported opcodes   │
                    └──────────────────────────┘
```

## Phase 1: Transaction Selection

### Query Strategy

Start with simple, successful transactions to validate the happy path:

```sql
SELECT 
  t.hash as tx_hash,
  t.account,
  t.lt,
  t.compute_exit_code,
  t.compute_gas_used,
  t.account_state_hash_before,
  t.account_state_hash_after,
  t.mc_block_seqno
FROM transactions t
WHERE 
  t.compute_exit_code = 0           -- successful execution
  AND t.aborted = false             -- not aborted
  AND t.compute_skipped = false     -- compute phase ran
  AND t.now > 1704067200            -- after Jan 1, 2024
ORDER BY t.lt ASC
LIMIT 1000
```

### Filtering Criteria

**Start with (Tier 1):**
- `compute_exit_code = 0` (success)
- Simple contracts (wallets, basic jetton transfers)
- Small gas usage (`compute_gas_used < 50000`)

**Later expand to (Tier 2):**
- Non-zero exit codes (exception handling)
- More complex contracts
- Higher gas usage

**Skip initially:**
- Transactions with unresolved library references (need extra handling / resolution)
- Tick/tock transactions (special execution context)
- Split/merge transactions

## Phase 2: State Reconstruction

### Option A: Use TxTracer-core (Recommended for Start)

```typescript
// diff-test/collector/src/collect.ts (outline)
import {
  computeMinLt,
  findBaseTxByHash,
  findFullBlockForSeqno,
  findRawTxByHash,
  findShardBlockForTx,
  getBlockAccount,
  retrace,
} from "txtracer-core"

import { beginCell, storeMessage } from "@ton/core"

async function collectTestCase(txHash: string): Promise<TestCase> {
  const trace = await retrace(false, txHash)
  const computeInfo = trace.emulatedTx.computeInfo
  if (computeInfo === "skipped") throw new Error("compute phase skipped")

  // Resolve the pre-transaction account snapshot at the masterchain block.
  // (See the full implementation for edge cases and fallbacks.)
  const baseTx = await findBaseTxByHash(false, txHash)
  const rawTx = (await findRawTxByHash(false, baseTx))[0]
  const shardBlock = await findShardBlockForTx(false, rawTx)
  const mcBlock = await findFullBlockForSeqno(false, shardBlock.master_ref_seqno)

  // Optional: enforce "first tx in master block" to avoid in-block state replay.
  const minLt = computeMinLt(rawTx.tx, baseTx.address, mcBlock)
  if (rawTx.tx.lt !== minLt) throw new Error("tx is not first in master block")

  const shardAcc = await getBlockAccount(false, baseTx.address, mcBlock)
  const st: any = shardAcc.account?.storage?.state
  const inMsg: any = rawTx.tx.inMessage
  if (!inMsg) throw new Error("no inMessage in transaction")

  // For non-active accounts, TVM initializes code/data from the inbound message `init` (if present).
  const dataCell = st?.type === "active" ? (st.state?.data ?? beginCell().endCell()) : (inMsg.init?.data ?? beginCell().endCell())
  const codeCell = st?.type === "active" ? st.state?.code : inMsg.init?.code
  if (!codeCell) throw new Error("no code cell")

  const inMsgCell = beginCell().store(storeMessage(inMsg)).endCell()
  const inBodyCell = inMsg.body ?? beginCell().endCell()

  const desc: any = rawTx.tx.description
  if (desc?.type !== "generic") throw new Error("unsupported tx description type")
  const computePhase: any = desc.computePhase
  if (computePhase?.type !== "vm") throw new Error("compute phase is not vm")

  // Match `Transaction::prepare_vm_stack` balance at compute start.
  const storageFees: bigint = desc.storagePhase?.storageFeesCollected ?? 0n
  const duePayment: bigint = desc.storagePhase?.storageFeesDue ?? 0n
  const msgImportFee: bigint = inMsg.info.type === "external-in" ? inMsg.info.importFee : 0n
  const creditCoins: bigint =
    desc.creditPhase?.credit?.coins ??
    (inMsg.info.type === "internal" ? inMsg.info.value.coins : 0n)
  const balanceBefore: bigint = shardAcc.account?.storage?.balance?.coins ?? 0n
  const balanceExec: bigint = balanceBefore - msgImportFee - storageFees + creditCoins

  return {
    tx_hash: txHash,
    code_boc: codeCell.toBoc().toString("base64"),
    data_boc: dataCell.toBoc().toString("base64"),
    stack_init: {
      balance_grams: balanceExec.toString(10),
      msg_balance_grams: creditCoins.toString(10),
      now: String(rawTx.tx.now),
      lt: rawTx.tx.lt.toString(10),
      rand_seed: "0", // from shard block `rand_seed` (base64 → bigint)
      storage_fees: storageFees.toString(10),
      due_payment: duePayment.toString(10),
      in_msg_boc: inMsgCell.toBoc().toString("base64"),
      in_msg_body_boc: inBodyCell.toBoc().toString("base64"),
      in_msg_extern: inMsg.info.type !== "internal",
    },
    expected: {
      // IMPORTANT: blockchain `compute_exit_code` is the *uncomplemented* code.
      exit_code: computePhase.exitCode,
      gas_used: computePhase.gasUsed.toString(10),
      gas_limit: "1000000", // computed from block config (see `computeGasInit`)
      gas_max: "1000000",
      gas_credit: "0",
    },
  }
}
```

### Option B: Direct from Indexer + TON API

If TxTracer has issues or you need more control:

```typescript
// direct-collector.ts
import { TonClient4 } from "@ton/ton"

async function getHistoricalState(
  client: TonClient4,
  address: string,
  mcSeqno: number
) {
  // Get account state at specific masterchain block
  const state = await client.getAccountLite(mcSeqno, address)
  return {
    code: state.account.code,
    data: state.account.data,
    balance: state.account.balance,
  }
}
```

## Phase 3: Lean VM Harness

### Extend Current CLI

```lean
-- TvmLean/DiffTest.lean

structure TestCase where
  tx_hash : String
  code_boc : String
  data_boc : String
  stack_init : StackInit
  expected : Expected

def runTestCase (cfg : RunConfig) (tc : TestCase) : IO TestResult := do
  ...
  | .halt exitCode stF =>
      -- `VmState.run` returns bitwise-complemented exit codes (like C++ `vm.run()`).
      -- Blockchain `compute_exit_code` is the uncomplemented one (like C++ `cp.exit_code = ~vm.run()`).
      let actualExit : Int := ~~~ exitCode
      ...
```

### CLI Extension

```bash
lake build tvm-lean-diff-test

# Run single fixture
lake exe tvm-lean-diff-test -- --case diff-test/fixtures/<TX_HASH>.json

# Run a whole directory (optional JSON report)
lake exe tvm-lean-diff-test -- --dir diff-test/fixtures --skip-unsupported --out diff-test/results.json
```

## Phase 4: Comparison Logic

### What to Compare

| Field | Priority | Notes |
|-------|----------|-------|
| `exit_code` | Critical | Must match exactly (uncomplemented `compute_exit_code`) |
| `gas_used` | High | Must match exactly (currently asserted when present in fixture) |
| `c4_cell` | High | Final c4 cell must match (when fixture includes `expected.c4_boc`) |
| `c5_cell` | Medium | Final actions cell must match (when fixture includes `expected.c5_boc`) |
| `c7` | Medium | Final c7 tuple must match (when fixture includes `expected.c7`) |
| `stack` | Low | Only for exit_code != 0 |

### Handling Discrepancies

```typescript
enum DiscrepancyType {
  EXIT_CODE_MISMATCH,      // Critical bug
  GAS_MISMATCH,            // Gas accounting bug
  STATE_MISMATCH,          // Execution divergence
  UNSUPPORTED_OPCODE,      // Expected, track for coverage
  DECODE_ERROR,            // BOC/encoding issue
  TIMEOUT,                 // Fuel exhaustion
}

interface Discrepancy {
  type: DiscrepancyType
  txHash: string
  expected: any
  actual: any
  // For debugging:
  lastSuccessfulOpcode?: string
  stackAtFailure?: string[]
}
```

## Phase 5: Results Tracking

### SQLite Schema for Results

```sql
CREATE TABLE test_runs (
  id INTEGER PRIMARY KEY,
  run_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
  lean_commit TEXT,
  total_tests INTEGER,
  passed INTEGER,
  failed INTEGER,
  skipped INTEGER
);

CREATE TABLE test_results (
  id INTEGER PRIMARY KEY,
  run_id INTEGER REFERENCES test_runs(id),
  tx_hash TEXT,
  status TEXT,  -- PASS, FAIL, SKIP
  expected_exit_code INTEGER,
  actual_exit_code INTEGER,
  expected_gas INTEGER,
  actual_gas INTEGER,
  discrepancy_type TEXT,
  error_message TEXT,
  unsupported_opcode TEXT
);

CREATE TABLE opcode_coverage (
  opcode TEXT PRIMARY KEY,
  times_seen INTEGER,
  times_succeeded INTEGER,
  first_failure_tx TEXT
);
```

### Dashboard Query

```sql
-- Overall pass rate
SELECT 
  COUNT(*) as total,
  SUM(CASE WHEN status = 'PASS' THEN 1 ELSE 0 END) as passed,
  ROUND(100.0 * SUM(CASE WHEN status = 'PASS' THEN 1 ELSE 0 END) / COUNT(*), 2) as pass_rate
FROM test_results
WHERE run_id = (SELECT MAX(id) FROM test_runs);

-- Most common failure reasons
SELECT 
  discrepancy_type,
  COUNT(*) as count
FROM test_results
WHERE status = 'FAIL'
GROUP BY discrepancy_type
ORDER BY count DESC;

-- Unsupported opcodes by frequency
SELECT 
  unsupported_opcode,
  COUNT(*) as count
FROM test_results
WHERE discrepancy_type = 'UNSUPPORTED_OPCODE'
GROUP BY unsupported_opcode
ORDER BY count DESC;
```

## Phase 6: Iteration Loop

### Daily Workflow

```
1. Run test suite overnight
   └─> ./run-diff-tests.sh --since yesterday --limit 10000

2. Morning: Review failures
   └─> ./analyze-failures.sh
   
3. Prioritize by impact
   └─> Most common unsupported opcode? Implement it.
   └─> Exit code mismatch? Debug the specific case.
   └─> Gas mismatch? Check instruction gas costs.

4. Implement fix
   └─> Add opcode to decodeCp0 + execInstr
   └─> Add unit test
   
5. Re-run failed subset
   └─> ./run-diff-tests.sh --only-failed
   
6. Commit & repeat
```

### Coverage Targets

| Milestone | Target | Notes |
|-----------|--------|-------|
| Week 1 | 50% pass rate | Basic opcodes working |
| Week 2 | 70% pass rate | Common patterns covered |
| Week 4 | 90% pass rate | Long tail of opcodes |
| Week 8 | 99% pass rate | Edge cases, exotic cells |

## Immediate Next Steps

1. **Set up test fixture collection**
   - Install txtracer-core
   - Write collector script
   - Generate first 100 test cases from recent simple transactions

2. **Extend Lean CLI**
   - Add JSON test case parser
   - Add c7 setup (now, lt, balance, address)
   - Add comparison output

3. **Run first batch**
   - Expect many UNSUPPORTED_OPCODE failures
   - Use opcode frequency to prioritize implementation

4. **Build feedback loop**
   - Script to analyze failures
   - Script to re-run after fixes
   - Track progress over time

## Files to Create

```
tvm-lean/
├── diff-test/
│   ├── collector/           # TypeScript, uses txtracer-core
│   │   ├── package.json
│   │   ├── collect.ts       # Main collector script
│   │   └── queries.sql      # ClickHouse queries
│   ├── fixtures/            # Generated test cases
│   │   └── *.json
│   ├── results/             # Test run outputs
│   │   └── *.sqlite
│   └── scripts/
│       ├── run-tests.sh
│       ├── analyze.sh
│       └── report.sh
├── TvmLean/
│   ├── DiffTest.lean        # Test runner in Lean
│   └── ...
└── diff-testing-plan.md     # This file
```
