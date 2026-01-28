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

import { beginCell, Cell, loadShardAccount, storeMessage, type TupleItem } from "@ton/core";
import { Blockchain } from "@ton/sandbox";

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
  } = {
    testnet: false,
    outDir: path.resolve(process.cwd(), "..", "fixtures"),
    txs: [],
    allowNonFirst: false,
    expectedState: false,
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

async function collectFixture(
  testnet: boolean,
  txHash: string,
  allowNonFirst: boolean,
  sandbox?: { executor: any },
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
    },
    expected: {
      exit_code: computePhase.exitCode,
      gas_used: computePhase.gasUsed.toString(10),
      gas_limit: gasInit.gasLimit.toString(10),
      gas_max: gasInit.gasMax.toString(10),
      gas_credit: gasInit.gasCredit.toString(10),
    },
  };

  if (sandbox) {
    const shardAcc0: any = { ...shardAcc, lastTransactionLt: 0n, lastTransactionHash: 0n };
    const shardAccountBase64 = shardAccountToBase64(shardAcc0);

    const exec: any = sandbox.executor;
    if (typeof exec.runTransaction !== "function") {
      throw new Error("sandbox executor does not support runTransaction");
    }

    const txRes = await exec.runTransaction({
      config: blockConfig,
      libs: libsCell ?? null,
      verbosity: "full_location_stack_verbose",
      shardAccount: shardAccountBase64,
      message: inMsgCell,
      now: rawTx.tx.now,
      lt: rawTx.tx.lt,
      randomSeed: randSeed,
      ignoreChksig: false,
      debugEnabled: true,
    });

    if (!txRes?.result?.success) throw new Error(`sandbox emulation failed: ${txRes?.result?.error ?? "unknown error"}`);

    const shardAccountAfter = loadShardAccount(Cell.fromBase64(String(txRes.result.shardAccount)).asSlice());
    const stAfter: any = shardAccountAfter.account?.storage?.state;
    const finalDataCell: any = stAfter?.type === "active" ? stAfter.state?.data ?? emptyCell() : emptyCell();
    fixture.expected.c4_boc = bocBase64(finalDataCell);

    const actionsB64: any = txRes.result.actions;
    if (typeof actionsB64 === "string" && actionsB64.length > 0) {
      fixture.expected.c5_boc = actionsB64;
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

  await mkdir(opts.outDir, { recursive: true });

  let sandbox: { executor: any } | undefined = undefined;
  if (opts.expectedState) {
    const blockchain = await Blockchain.create();
    blockchain.verbosity.print = false;
    blockchain.verbosity.vmLogs = "vm_logs_verbose";
    sandbox = { executor: blockchain.executor as any };
  }

  for (const txHash of txs) {
    const outPath = path.join(opts.outDir, `${txHash}.json`);
    try {
      const fixture = await collectFixture(opts.testnet, txHash, opts.allowNonFirst, sandbox);
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
