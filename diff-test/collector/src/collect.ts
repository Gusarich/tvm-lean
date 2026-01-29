import { mkdir, readFile, writeFile } from "node:fs/promises";
import path from "node:path";

import {
  collectUsedLibraries,
  computeMinLt,
  findBaseTxByHash,
  findFullBlockForSeqno,
  findRawTxByHash,
  findShardBlockForTx,
  getBlockConfig,
  getBlockAccount,
  shardAccountToBase64,
} from "txtracer-core";

import { beginCell, Cell, Dictionary, loadShardAccount, storeMessage, type TupleItem } from "@ton/core";
import { Blockchain, Executor } from "@ton/sandbox";

import { computeGasInit, parseGlobalConfig } from "./gas.js";

type TupleItemJson =
  | { type: "null" }
  | { type: "nan" }
  | { type: "int"; value: string }
  | { type: "cell" | "slice" | "builder"; boc: string }
  | { type: "tuple"; items: TupleItemJson[] };

type Fixture = {
  tx_hash: string;
  code_boc: string;
  // Code cell exposed as `MYCODE` in c7 (can differ from `code_boc` when the executable code is a resolved library).
  mycode_boc?: string;
  data_boc: string;
  stack_init: {
    balance_grams: string;
    msg_balance_grams: string;
    now: string;
    lt: string;
    rand_seed: string;
    storage_fees: string;
    due_payment: string;
    in_msg_boc: string;
    in_msg_body_boc: string;
    in_msg_extern: boolean;
    // Full blockchain config cell (HashmapE 32 -> Cell), used by CONFIGROOT (c7 params[9]) and for accurate c7 init.
    config_root_boc?: string;
    // Selected ConfigParams used by UNPACKEDCONFIGTUPLE (c7 params[14]).
    config_storage_prices_boc?: string; // ConfigParam 18 (StoragePrices dict)
    config_global_id_boc?: string; // ConfigParam 19 (Global ID)
    config_mc_gas_prices_boc?: string; // ConfigParam 20 (GasPrices for masterchain)
    config_gas_prices_boc?: string; // ConfigParam 21 (GasPrices for basechain)
    config_size_limits_boc?: string; // ConfigParam 43 (SizeLimits)
    // ConfigParam 24 / 25 (MsgForwardPrices), used by GETORIGINALFWDFEE and related opcodes.
    config_mc_fwd_prices_boc?: string;
    config_fwd_prices_boc?: string;
    // ConfigParam 45 (PrecompiledContractsConfig), used to override compute_phase.gas_used and to populate GETPRECOMPILEDGAS.
    config_precompiled_contracts_boc?: string;
  };
  expected: {
    exit_code: number;
    gas_used?: string;
    gas_limit?: string;
    gas_max?: string;
    gas_credit?: string;
    c4_boc?: string;
    c5_boc?: string;
    c7?: TupleItemJson;
    // Optional verbose VM log from the sandbox emulator (useful for debugging gas/step mismatches).
    vm_log?: string;
  };
};

function parseArgs(argv: string[]) {
  const opts: {
    testnet: boolean;
    outDir: string;
    txs: string[];
    txFile?: string;
    allowNonFirst: boolean;
    expectedState: boolean;
    includeVmLog: boolean;
  } = {
    testnet: false,
    outDir: path.resolve(process.cwd(), "..", "fixtures"),
    txs: [],
    allowNonFirst: false,
    expectedState: true,
    includeVmLog: false,
  };

  for (let i = 0; i < argv.length; i++) {
    const a = argv[i]!;
    if (a === "--testnet") {
      opts.testnet = true;
    } else if (a === "--out-dir") {
      opts.outDir = path.resolve(argv[++i]!);
    } else if (a === "--tx") {
      opts.txs.push(argv[++i]!);
    } else if (a === "--tx-file") {
      opts.txFile = argv[++i]!;
    } else if (a === "--allow-nonfirst") {
      opts.allowNonFirst = true;
    } else if (a === "--expected-state") {
      opts.expectedState = true;
    } else if (a === "--no-expected-state") {
      opts.expectedState = false;
    } else if (a === "--include-vm-log") {
      opts.includeVmLog = true;
    } else if (a === "--") {
      // ignore
    } else {
      throw new Error(`unknown arg: ${a}`);
    }
  }

  return opts;
}

async function readTxFile(filePath: string): Promise<string[]> {
  const text = await readFile(filePath, "utf8");
  return text
    .split(/\r?\n/g)
    .map((l: string) => l.trim())
    .filter((l: string) => l.length > 0 && !l.startsWith("#"));
}

function bocBase64(c: any): string {
  return c.toBoc().toString("base64");
}

function emptyCell(): any {
  return beginCell().endCell();
}

function bytesToBigIntBE(buf: Buffer): bigint {
  let x = 0n;
  for (const b of buf) x = (x << 8n) + BigInt(b);
  return x;
}

function tupleItemToJson(item: TupleItem): TupleItemJson {
  if (item.type === "null") return { type: "null" };
  if (item.type === "nan") return { type: "nan" };
  if (item.type === "int") return { type: "int", value: item.value.toString(10) };
  if (item.type === "cell") return { type: "cell", boc: bocBase64(item.cell) };
  if (item.type === "slice") return { type: "slice", boc: bocBase64(item.cell) };
  if (item.type === "builder") return { type: "builder", boc: bocBase64(item.cell) };
  if (item.type === "tuple") return { type: "tuple", items: item.items.map(tupleItemToJson) };
  // eslint-disable-next-line @typescript-eslint/restrict-template-expressions
  throw new Error(`unsupported TupleItem type: ${(item as any).type}`);
}

function patchC7BlockLt(c7: TupleItemJson, blockLt: bigint): TupleItemJson {
  if (c7.type !== "tuple") return c7;
  const env = c7.items[0];
  if (!env || env.type !== "tuple") return c7;

  const envItems = [...env.items];
  if (envItems.length <= 4) return c7;

  envItems[4] = { type: "int", value: blockLt.toString(10) };
  const c7Items = [...c7.items];
  c7Items[0] = { type: "tuple", items: envItems };
  return { type: "tuple", items: c7Items };
}

function extractConfigParamCell(configCellB64: string, idx: number): Cell | null {
  const params = Cell.fromBase64(configCellB64)
    .beginParse()
    .loadDictDirect(Dictionary.Keys.Int(32), Dictionary.Values.Cell()) as Dictionary<number, Cell>;
  return params.get(idx) ?? null;
}

async function collectFixture(
  testnet: boolean,
  txHash: string,
  allowNonFirst: boolean,
  sandbox?: { executor: any; debugExecutor?: Executor },
  includeVmLog?: boolean,
): Promise<Fixture> {
  const baseTx = await findBaseTxByHash(testnet, txHash);
  if (!baseTx) throw new Error("tx not found via findBaseTxByHash");
  const rawTxs = await findRawTxByHash(testnet, baseTx);
  const rawTx = rawTxs.find((r) => r.tx.hash().equals(baseTx.hash));
  if (!rawTx) throw new Error("no RawTransaction returned by findRawTxByHash");

  const shardBlock = await findShardBlockForTx(testnet, rawTx);
  if (!shardBlock) throw new Error("could not find shard block for tx");

  const masterSeqno = shardBlock.master_ref_seqno;
  const mcBlock = await findFullBlockForSeqno(testnet, masterSeqno);

  const minLt = computeMinLt(rawTx.tx, baseTx.address, mcBlock);
  if (!allowNonFirst && rawTx.tx.lt !== minLt) {
    throw new Error(`tx is not first in master block (lt=${rawTx.tx.lt}, minLt=${minLt})`);
  }

  const shardAcc = await getBlockAccount(testnet, baseTx.address, mcBlock);

  // Extract account data (c4) from the account snapshot before the master-block.
  let dataCell: any = emptyCell();
  const st: any = shardAcc.account?.storage?.state;
  if (st?.type === "active") {
    dataCell = st.state?.data ?? emptyCell();
  } else {
    // For non-active accounts, TVM initializes c4 from the message `init.data` (if present).
    dataCell = rawTx.tx.inMessage?.init?.data ?? emptyCell();
  }

  // Code to execute: prefer library-resolved code cell (loadedCode), fall back to snapshot code.
  let codeCell: any = undefined;
  if (st?.type === "active") {
    codeCell = st.state?.code;
  } else {
    // For non-active accounts, TVM initializes code from the message `init.code` (if present).
    codeCell = rawTx.tx.inMessage?.init?.code;
  }
  if (!codeCell) throw new Error("no code cell (inactive account?)");
  const myCodeCell = codeCell;

  const [libsCell, loadedCode] = await collectUsedLibraries(testnet, shardAcc, rawTx.tx as any, []);
  if (loadedCode) codeCell = loadedCode;

  const inMsg = rawTx.tx.inMessage;
  if (!inMsg) throw new Error("no inMessage in transaction");
  const inMsgCell = beginCell().store(storeMessage(inMsg as any) as any).endCell();
  const inBodyCell = (inMsg as any).body ?? emptyCell();

  const inMsgExtern = inMsg.info.type !== "internal";
  const msgImportFee = inMsg.info.type === "external-in" ? inMsg.info.importFee : 0n;
  const randSeed = Buffer.from(String(shardBlock.rand_seed), "base64");
  const randSeedInt = bytesToBigIntBE(randSeed);

  const desc: any = rawTx.tx.description;
  if (desc?.type !== "generic") throw new Error(`unsupported tx description type: ${desc?.type ?? "unknown"}`);
  const computePhase: any = desc.computePhase;
  if (computePhase?.type !== "vm") throw new Error(`compute phase is not vm (type=${computePhase?.type ?? "unknown"})`);

  // Match `Transaction::prepare_vm_stack` / compute phase balance:
  // - balance is debited by external message import fee (if any)
  // - storage fees are collected before compute phase
  // - internal message value (credit phase) is added before compute phase
  const storageFees: bigint = desc.storagePhase?.storageFeesCollected ?? 0n;
  const duePayment: bigint = desc.storagePhase?.storageFeesDue ?? 0n;
  const creditCoins: bigint =
    desc.creditPhase?.credit?.coins ??
    (inMsg.info.type === "internal" ? inMsg.info.value.coins : 0n);

  const balanceBefore: bigint = shardAcc.account?.storage?.balance?.coins ?? 0n;
  const balanceExec: bigint = balanceBefore - msgImportFee - storageFees + creditCoins;

  const blockConfig = await getBlockConfig(testnet, mcBlock as any);
  const cfg = parseGlobalConfig(blockConfig);
  const gasInit = computeGasInit(cfg, {
    workchain: baseTx.address.workChain,
    address: baseTx.address,
    now: rawTx.tx.now,
    balanceGrams: balanceExec,
    msgBalanceGrams: creditCoins,
    inMsgExtern,
  });

  const fixture: Fixture = {
    tx_hash: txHash,
    code_boc: bocBase64(codeCell),
    mycode_boc: bocBase64(myCodeCell),
    data_boc: bocBase64(dataCell),
    stack_init: {
      balance_grams: balanceExec.toString(10),
      msg_balance_grams: creditCoins.toString(10),
      now: String(rawTx.tx.now),
      lt: rawTx.tx.lt.toString(10),
      rand_seed: randSeedInt.toString(10),
      storage_fees: storageFees.toString(10),
      due_payment: duePayment.toString(10),
      in_msg_boc: bocBase64(inMsgCell),
      in_msg_body_boc: bocBase64(inBodyCell),
      in_msg_extern: inMsgExtern,
      config_root_boc: blockConfig,
    },
    expected: {
      exit_code: computePhase.exitCode,
      gas_used: computePhase.gasUsed.toString(10),
      gas_limit: gasInit.gasLimit.toString(10),
      gas_max: gasInit.gasMax.toString(10),
      gas_credit: gasInit.gasCredit.toString(10),
    },
  };

  const storagePricesCell = extractConfigParamCell(blockConfig, 18);
  const globalIdCell = extractConfigParamCell(blockConfig, 19);
  const mcGasPricesCell = extractConfigParamCell(blockConfig, 20);
  const gasPricesCell = extractConfigParamCell(blockConfig, 21);
  const mcFwdPricesCell = extractConfigParamCell(blockConfig, 24);
  const fwdPricesCell = extractConfigParamCell(blockConfig, 25);
  const sizeLimitsCell = extractConfigParamCell(blockConfig, 43);
  const precompiledContractsCell = extractConfigParamCell(blockConfig, 45);
  if (storagePricesCell) fixture.stack_init.config_storage_prices_boc = bocBase64(storagePricesCell);
  if (globalIdCell) fixture.stack_init.config_global_id_boc = bocBase64(globalIdCell);
  if (mcGasPricesCell) fixture.stack_init.config_mc_gas_prices_boc = bocBase64(mcGasPricesCell);
  if (gasPricesCell) fixture.stack_init.config_gas_prices_boc = bocBase64(gasPricesCell);
  if (mcFwdPricesCell) fixture.stack_init.config_mc_fwd_prices_boc = bocBase64(mcFwdPricesCell);
  if (fwdPricesCell) fixture.stack_init.config_fwd_prices_boc = bocBase64(fwdPricesCell);
  if (sizeLimitsCell) fixture.stack_init.config_size_limits_boc = bocBase64(sizeLimitsCell);
  if (precompiledContractsCell) fixture.stack_init.config_precompiled_contracts_boc = bocBase64(precompiledContractsCell);

  if (sandbox) {
    const shardAcc0: any = { ...shardAcc, lastTransactionLt: 0n, lastTransactionHash: 0n };
    const shardAccountBase64 = shardAccountToBase64(shardAcc0);

    const exec: any = sandbox.executor;
    if (typeof exec.runTransaction !== "function") {
      throw new Error("sandbox executor does not support runTransaction");
    }
    const verbosity = includeVmLog ? "full_location_gas" : "full_location_stack_verbose";

    const txRes = await exec.runTransaction({
      config: blockConfig,
      libs: libsCell ?? null,
      verbosity,
      shardAccount: shardAccountBase64,
      message: inMsgCell,
      now: rawTx.tx.now,
      lt: rawTx.tx.lt,
      randomSeed: randSeed,
      ignoreChksig: false,
      debugEnabled: true,
    });

    if (!txRes?.result?.success) throw new Error(`sandbox emulation failed: ${txRes?.result?.error ?? "unknown error"}`);
    if (includeVmLog) {
      fixture.expected.vm_log = String(txRes.result.vmLog ?? "");
    }

    const shardAccountAfter = loadShardAccount(Cell.fromBase64(String(txRes.result.shardAccount)).asSlice());
    const stAfter: any = shardAccountAfter.account?.storage?.state;
    const finalDataCell: any = stAfter?.type === "active" ? stAfter.state?.data ?? emptyCell() : emptyCell();
    fixture.expected.c4_boc = bocBase64(finalDataCell);

    const actionsB64: any = txRes.result.actions;
    if (typeof actionsB64 === "string" && actionsB64.length > 0) {
      fixture.expected.c5_boc = actionsB64;
    }

    if (sandbox.debugExecutor) {
      const dbg = sandbox.debugExecutor;
      const { emptr } = dbg.sbsTransactionSetup({
        config: blockConfig,
        libs: libsCell ?? null,
        verbosity,
        shardAccount: shardAccountBase64,
        message: inMsgCell,
        now: rawTx.tx.now,
        lt: rawTx.tx.lt,
        randomSeed: randSeed,
        ignoreChksig: false,
        debugEnabled: true,
      });

      try {
        const maxSteps = 5_000_000;
        let steps = 0;
        while (true) {
          steps++;
          const done = dbg.sbsTransactionStep(emptr);
          if (done) break;
          if (steps >= maxSteps) {
            throw new Error(`debugger step limit exceeded (>${maxSteps})`);
          }
        }

        const c7 = dbg.sbsTransactionC7(emptr);
        const blockLt = rawTx.tx.lt - (rawTx.tx.lt % 1000000n);
        fixture.expected.c7 = patchC7BlockLt(tupleItemToJson(c7), blockLt);

        // Override balance/in_msg_value from c7 to match the exact VM init values used by the emulator.
        if (c7.type === "tuple" && c7.items[0]?.type === "tuple") {
          const env = c7.items[0];
          const bal = env.items[7];
          if (bal?.type === "tuple" && bal.items[0]?.type === "int") {
            fixture.stack_init.balance_grams = bal.items[0].value.toString(10);
          }
          const inMsgVal = env.items[11];
          if (inMsgVal?.type === "tuple" && inMsgVal.items[0]?.type === "int") {
            fixture.stack_init.msg_balance_grams = inMsgVal.items[0].value.toString(10);
          }
        }

        // Capture MYCODE from c7 (this may differ from `code_boc` if the executable code was a resolved library).
        if (c7.type === "tuple" && c7.items[0]?.type === "tuple") {
          const myCode = c7.items[0].items[10];
          if (myCode?.type === "cell") {
            fixture.mycode_boc = bocBase64(myCode.cell);
          }
        }
      } finally {
        dbg.destroyEmulator(emptr);
      }
    }
  }

  return fixture;
}

async function main() {
  const opts = parseArgs(process.argv.slice(2));
  const txs = [...opts.txs, ...(opts.txFile ? await readTxFile(opts.txFile) : [])];
  if (txs.length === 0) {
    throw new Error("no tx hashes provided (use --tx or --tx-file)");
  }
  if (opts.includeVmLog && !opts.expectedState) {
    throw new Error("--include-vm-log requires --expected-state (sandbox emulation)");
  }

  await mkdir(opts.outDir, { recursive: true });

  let sandbox: { executor: any; debugExecutor?: Executor } | undefined = undefined;
  if (opts.expectedState) {
    const blockchain = await Blockchain.create();
    blockchain.verbosity.print = false;
    blockchain.verbosity.vmLogs = "vm_logs_verbose";
    const debugExecutor = await Executor.create({ debug: true });
    sandbox = { executor: blockchain.executor as any, debugExecutor };
  }

  for (const txHash of txs) {
    const outPath = path.join(opts.outDir, `${txHash}.json`);
    try {
      const fixture = await collectFixture(opts.testnet, txHash, opts.allowNonFirst, sandbox, opts.includeVmLog);
      await writeFile(outPath, JSON.stringify(fixture, null, 2), "utf8");
      // eslint-disable-next-line no-console
      console.log(`✓ ${txHash}`);
    } catch (e: any) {
      // eslint-disable-next-line no-console
      console.log(`✗ ${txHash}: ${e?.stack ?? e?.message ?? String(e)}`);
    }
  }
}

main().catch((e) => {
  // eslint-disable-next-line no-console
  console.error(e);
  process.exit(1);
});
