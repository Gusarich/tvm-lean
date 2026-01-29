import { mkdir, rm, writeFile, appendFile, access, readFile, readdir } from "node:fs/promises";
import path from "node:path";
import { spawn } from "node:child_process";

import { Address, beginCell, Cell, Dictionary, loadShardAccount, storeMessage, type TupleItem } from "@ton/core";
import { Blockchain, Executor } from "@ton/sandbox";
import { collectUsedLibraries, findFullBlockForSeqno, findRawTxByHash, getBlockAccount, getBlockConfig, shardAccountToBase64 } from "txtracer-core";

import { computeGasInit, parseGlobalConfig, type ParsedGlobalConfig } from "./gas.js";

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
  };
};

type SweepOpts = {
  testnet: boolean;
  sinceUtime: number;
  untilUtime: number;
  outDir: string;
  allowNonFirst: boolean;
  maxBlocks?: number;
  maxTxs?: number;
  maxFixtures?: number;
  runLean: boolean;
  batchSize: number;
  leanBin: string;
  resultsPath: string;
  fuel: number;
  gasLimit: number;
  skipUnsupported: boolean;
  traceFailures: boolean;
  traceAll: boolean;
  traceMax: number;
  keepFixtures: boolean;
  expectedState: boolean;
};

function parseTimeToUtime(s: string): number {
  const trimmed = s.trim();
  if (/^\d+$/.test(trimmed)) return Number(trimmed);
  const iso = /^\d{4}-\d{2}-\d{2}$/.test(trimmed) ? `${trimmed}T00:00:00Z` : trimmed;
  const d = new Date(iso);
  if (Number.isNaN(d.getTime())) throw new Error(`invalid time: ${s}`);
  return Math.floor(d.getTime() / 1000);
}

function txHashHexFromBase64(b64: string): string {
  return Buffer.from(b64, "base64").toString("hex").toUpperCase();
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
    .loadDictDirect(Dictionary.Keys.Int(32), Dictionary.Values.Cell());
  return params.get(idx) ?? null;
}

async function fetchToncenterBlocks(
  testnet: boolean,
  params: Record<string, string | number>,
): Promise<{ blocks: Array<{ seqno: number; gen_utime: string }> }> {
  const base = testnet ? "https://testnet.toncenter.com" : "https://toncenter.com";
  const url = new URL(`${base}/api/v3/blocks`);
  for (const [k, v] of Object.entries(params)) url.searchParams.set(k, String(v));
  const apiKey = process.env["TONCENTER_API_KEY"];
  const headers = apiKey ? { "X-API-Key": apiKey } : undefined;

  const maxAttempts = 8;
  for (let attempt = 1; attempt <= maxAttempts; attempt++) {
    const res = await fetch(url, { headers });
    if (res.ok) return (await res.json()) as any;

    const body = await res.text();
    const retryAfter = Number(res.headers.get("retry-after") ?? "");
    const backoffMs =
      Number.isFinite(retryAfter) && retryAfter > 0
        ? Math.min(60_000, retryAfter * 1000)
        : Math.min(60_000, 500 * 2 ** (attempt - 1));

    if (res.status === 429 && attempt < maxAttempts) {
      // eslint-disable-next-line no-console
      console.log(`toncenter blocks: HTTP 429 (rate limit), retrying in ${backoffMs}ms...`);
      await new Promise((r) => setTimeout(r, backoffMs));
      continue;
    }

    throw new Error(`toncenter blocks: HTTP ${res.status} ${body}`);
  }

  throw new Error("toncenter blocks: exhausted retries");
}

async function getSeqnoRange(testnet: boolean, sinceUtime: number, untilUtime: number): Promise<[number, number]> {
  const start = await fetchToncenterBlocks(testnet, {
    workchain: -1,
    shard: "8000000000000000",
    start_utime: sinceUtime,
    limit: 1,
    sort: "asc",
  });
  const end = await fetchToncenterBlocks(testnet, {
    workchain: -1,
    shard: "8000000000000000",
    end_utime: untilUtime,
    limit: 1,
    sort: "desc",
  });
  const startSeqno = start.blocks?.[0]?.seqno;
  const endSeqno = end.blocks?.[0]?.seqno;
  if (startSeqno === undefined) throw new Error("no master blocks found at --since");
  if (endSeqno === undefined) throw new Error("no master blocks found at --until");
  return [startSeqno, endSeqno];
}

function parseArgs(argv: string[]): SweepOpts {
  const opts: Partial<SweepOpts> = {
    testnet: false,
    outDir: path.resolve(process.cwd(), "..", "fixtures"),
    allowNonFirst: false,
    runLean: false,
    batchSize: 200,
    leanBin: path.resolve(process.cwd(), "..", "..", ".lake", "build", "bin", "tvm-lean-diff-test"),
    resultsPath: path.resolve(process.cwd(), "..", "results.jsonl"),
    fuel: 1_000_000,
    gasLimit: 1_000_000,
    skipUnsupported: false,
    traceFailures: false,
    traceAll: false,
    traceMax: 200,
    keepFixtures: false,
    expectedState: true,
  };

  for (let i = 0; i < argv.length; i++) {
    const a = argv[i]!;
    if (a === "--testnet") {
      opts.testnet = true;
    } else if (a === "--since") {
      opts.sinceUtime = parseTimeToUtime(argv[++i]!);
    } else if (a === "--until") {
      opts.untilUtime = parseTimeToUtime(argv[++i]!);
    } else if (a === "--out-dir") {
      opts.outDir = path.resolve(argv[++i]!);
    } else if (a === "--allow-nonfirst") {
      opts.allowNonFirst = true;
    } else if (a === "--max-blocks") {
      opts.maxBlocks = Number(argv[++i]!);
    } else if (a === "--max-txs") {
      opts.maxTxs = Number(argv[++i]!);
    } else if (a === "--max-fixtures") {
      opts.maxFixtures = Number(argv[++i]!);
    } else if (a === "--run-lean") {
      opts.runLean = true;
    } else if (a === "--batch-size") {
      opts.batchSize = Number(argv[++i]!);
    } else if (a === "--lean-bin") {
      opts.leanBin = path.resolve(argv[++i]!);
    } else if (a === "--results") {
      opts.resultsPath = path.resolve(argv[++i]!);
    } else if (a === "--fuel") {
      opts.fuel = Number(argv[++i]!);
    } else if (a === "--gas-limit") {
      opts.gasLimit = Number(argv[++i]!);
    } else if (a === "--skip-unsupported") {
      opts.skipUnsupported = true;
    } else if (a === "--trace-failures") {
      opts.traceFailures = true;
    } else if (a === "--trace-all") {
      opts.traceAll = true;
    } else if (a === "--trace-max") {
      opts.traceMax = Number(argv[++i]!);
    } else if (a === "--keep-fixtures") {
      opts.keepFixtures = true;
    } else if (a === "--expected-state") {
      opts.expectedState = true;
    } else if (a === "--no-expected-state") {
      opts.expectedState = false;
    } else if (a === "--") {
      // ignore
    } else {
      throw new Error(`unknown arg: ${a}`);
    }
  }

  if (opts.sinceUtime === undefined) throw new Error("missing required arg: --since <YYYY-MM-DD|ISO|utime>");
  if (opts.untilUtime === undefined) opts.untilUtime = Math.floor(Date.now() / 1000);

  return opts as SweepOpts;
}

async function runLeanBatch(opts: SweepOpts, batchDir: string) {
  const reportPath = path.join(batchDir, "_report.json");
  await rm(reportPath, { force: true });

  await new Promise<void>((resolve, reject) => {
    const traceArgs: string[] = [];
    if (opts.traceAll) traceArgs.push("--trace-all", "--trace-max", String(opts.traceMax));
    else if (opts.traceFailures) traceArgs.push("--trace-failures", "--trace-max", String(opts.traceMax));
    const skipArgs: string[] = [];
    if (opts.skipUnsupported) skipArgs.push("--skip-unsupported");
    const p = spawn(
      opts.leanBin,
      [
        "--dir",
        batchDir,
        "--fuel",
        String(opts.fuel),
        "--gas-limit",
        String(opts.gasLimit),
        ...skipArgs,
        ...traceArgs,
        "--out",
        reportPath,
      ],
      { stdio: "inherit" },
    );
    p.on("error", reject);
    p.on("exit", (code) => {
      if (code === 0) resolve();
      else reject(new Error(`lean diff runner exited with code ${code}`));
    });
  });

  const reportText = await readFile(reportPath, "utf8");
  const arr = JSON.parse(reportText) as unknown[];
  const out = arr.map((r) => JSON.stringify(r) + "\n").join("");
  await appendFile(opts.resultsPath, out);
}

async function main() {
  const opts = parseArgs(process.argv.slice(2));

  if (opts.runLean && !opts.expectedState) {
    throw new Error("--run-lean requires --expected-state (tvm-lean-diff-test compares c7 and other final VM registers)");
  }

  if (opts.runLean) {
    await access(opts.leanBin).catch(() => {
      throw new Error(`Lean diff runner not found at ${opts.leanBin}. Build it with: (cd ../.. && lake build tvm-lean-diff-test)`);
    });
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

  const [startSeqno, endSeqno] = await getSeqnoRange(opts.testnet, opts.sinceUtime, opts.untilUtime);
  console.log(`masterchain seqno range: ${startSeqno}..${endSeqno}`);

  // NOTE: the Lean diff runner ignores JSON files under any path segment that starts with `_`.
  // So this directory name must *not* start with `_`.
  const batchDir = path.join(opts.outDir, "batch");
  if (opts.runLean) {
    await rm(batchDir, { recursive: true, force: true });
    await mkdir(batchDir, { recursive: true });
  }

  let totalTxs = 0;
  let totalFixtures = 0;
  let stop = false;

  const skipped = {
    nonFirst: 0,
    nonGeneric: 0,
    computeNotVm: 0,
    noInMsg: 0,
    noCode: 0,
    errors: 0,
  };

  const randSeedByShardBlock = new Map<string, Buffer>();
  const blockConfigByMc = new Map<number, { configCell: string; parsed: ParsedGlobalConfig }>();

  for (let seqno = startSeqno; seqno <= endSeqno; seqno++) {
    if (opts.maxBlocks !== undefined && seqno - startSeqno >= opts.maxBlocks) break;

    const block0 = await findFullBlockForSeqno(opts.testnet, seqno);
    const block = {
      shards: [...block0.shards].sort((a: any, b: any) => (a.workchain === -1 ? -1 : 0) - (b.workchain === -1 ? -1 : 0)),
    };

    let blockCfg = blockConfigByMc.get(seqno);
    if (!blockCfg) {
      const configCell = await getBlockConfig(opts.testnet, block0 as any);
      blockCfg = { configCell, parsed: parseGlobalConfig(configCell) };
      blockConfigByMc.set(seqno, blockCfg);
    }

    // Compute min-lt per account inside this master block (used to skip non-first txs).
    const minLtByAccount = new Map<string, bigint>();
    for (const shard of block.shards as any[]) {
      for (const tx of shard.transactions as any[]) {
        const lt = BigInt(tx.lt);
        const prev = minLtByAccount.get(tx.account);
        if (prev === undefined || lt < prev) minLtByAccount.set(tx.account, lt);
      }
    }

    const shardAccountCache = new Map<string, any>();

    for (const shard of block.shards as any[]) {
      if (shard.workchain !== 0 && shard.workchain !== -1) continue;

      for (const txEntry of shard.transactions as any[]) {
        if (opts.maxTxs !== undefined && totalTxs >= opts.maxTxs) {
          stop = true;
          break;
        }
        if (opts.maxFixtures !== undefined && totalFixtures >= opts.maxFixtures) {
          stop = true;
          break;
        }
        totalTxs++;

        const lt = BigInt(txEntry.lt);
        const account = String(txEntry.account);

        const minLt = minLtByAccount.get(account);
        if (!opts.allowNonFirst && minLt !== undefined && lt !== minLt) {
          skipped.nonFirst++;
          continue;
        }

        const txHashHex = txHashHexFromBase64(String(txEntry.hash));
        try {
          const address = Address.parse(account);
          const hashBuf = Buffer.from(String(txEntry.hash), "base64");
          const baseInfo: any = { lt, hash: hashBuf, address: address as any };

          const rawTxs = await findRawTxByHash(opts.testnet, baseInfo);
          const rawTx = rawTxs.find((r: any) => r.tx.hash().equals(hashBuf));
          if (!rawTx) throw new Error("could not locate raw tx in account tx list");

          const desc: any = rawTx.tx.description;
          if (desc?.type !== "generic") {
            skipped.nonGeneric++;
            continue;
          }
          const computePhase: any = desc.computePhase;
          if (computePhase?.type !== "vm") {
            skipped.computeNotVm++;
            continue;
          }

          const inMsg: any = rawTx.tx.inMessage;
          if (!inMsg) {
            skipped.noInMsg++;
            continue;
          }

          const addrKey = address.toRawString();
          let shardAcc = shardAccountCache.get(addrKey);
          if (!shardAcc) {
            shardAcc = await getBlockAccount(opts.testnet, address as any, block as any);
            shardAccountCache.set(addrKey, shardAcc);
          }

          let dataCell: any = emptyCell();
          let codeCell: any = undefined;
          let libsCell: any = undefined;

          const st: any = shardAcc.account?.storage?.state;
          if (st?.type === "active") {
            dataCell = st.state?.data ?? emptyCell();
            codeCell = st.state?.code;
          } else {
            // For non-active accounts, TVM initializes code/data from the message `init` (if present).
            dataCell = rawTx.tx.inMessage?.init?.data ?? emptyCell();
            codeCell = rawTx.tx.inMessage?.init?.code;
          }
          if (!codeCell) {
            skipped.noCode++;
            continue;
          }
          const myCodeCell = codeCell;

          const [libs, loadedCode] = await collectUsedLibraries(opts.testnet, shardAcc, rawTx.tx as any, []);
          libsCell = libs;
          if (loadedCode) codeCell = loadedCode;

          const inMsgCell = beginCell().store(storeMessage(inMsg) as any).endCell();
          const inBodyCell = inMsg.body ?? emptyCell();
          const inMsgExtern = inMsg.info.type !== "internal";
          const msgImportFee = inMsg.info.type === "external-in" ? inMsg.info.importFee : 0n;
          const storageFees: bigint = desc.storagePhase?.storageFeesCollected ?? 0n;
          const duePayment: bigint = desc.storagePhase?.storageFeesDue ?? 0n;
          const creditCoins: bigint =
            desc.creditPhase?.credit?.coins ??
            (inMsg.info.type === "internal" ? inMsg.info.value.coins : 0n);
          const balanceBefore: bigint = shardAcc.account?.storage?.balance?.coins ?? 0n;
          const balanceExec: bigint = balanceBefore - msgImportFee - storageFees + creditCoins;
          const gasInit = computeGasInit(blockCfg.parsed, {
            workchain: address.workChain,
            address,
            now: rawTx.tx.now,
            balanceGrams: balanceExec,
            msgBalanceGrams: creditCoins,
            inMsgExtern,
          });

          // Needed for a realistic c7 environment (Lean uses it in defaultInitC7),
          // and for sandbox emulation when `--expected-state` is enabled.
          const shardBlockKey = `${rawTx.block.workchain}:${rawTx.block.shard}:${rawTx.block.seqno}`;
          let randSeed = randSeedByShardBlock.get(shardBlockKey);
          if (!randSeed) {
            const shardInt = BigInt(rawTx.block.shard);
            const shardUint = shardInt < 0n ? shardInt + 0x10000000000000000n : shardInt;
            const blocks = await fetchToncenterBlocks(opts.testnet, {
              workchain: rawTx.block.workchain,
              shard: "0x" + shardUint.toString(16),
              seqno: rawTx.block.seqno,
              limit: 1,
            });
            const b0: any = (blocks as any).blocks?.[0];
            if (!b0?.rand_seed) throw new Error(`toncenter: missing rand_seed for shard block ${shardBlockKey}`);
            randSeed = Buffer.from(String(b0.rand_seed), "base64");
            randSeedByShardBlock.set(shardBlockKey, randSeed);
          }
          const randSeedInt = bytesToBigIntBE(randSeed);

          const fixture: Fixture = {
            tx_hash: txHashHex,
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
              config_root_boc: blockCfg.configCell,
            },
            expected: {
              exit_code: computePhase.exitCode,
              gas_used: computePhase.gasUsed.toString(10),
              gas_limit: gasInit.gasLimit.toString(10),
              gas_max: gasInit.gasMax.toString(10),
              gas_credit: gasInit.gasCredit.toString(10),
            },
          };

          const storagePricesCell = extractConfigParamCell(blockCfg.configCell, 18);
          const globalIdCell = extractConfigParamCell(blockCfg.configCell, 19);
          const mcGasPricesCell = extractConfigParamCell(blockCfg.configCell, 20);
          const gasPricesCell = extractConfigParamCell(blockCfg.configCell, 21);
          const mcFwdPricesCell = extractConfigParamCell(blockCfg.configCell, 24);
          const fwdPricesCell = extractConfigParamCell(blockCfg.configCell, 25);
          const sizeLimitsCell = extractConfigParamCell(blockCfg.configCell, 43);
          const precompiledContractsCell = extractConfigParamCell(blockCfg.configCell, 45);
          if (storagePricesCell) fixture.stack_init.config_storage_prices_boc = bocBase64(storagePricesCell);
          if (globalIdCell) fixture.stack_init.config_global_id_boc = bocBase64(globalIdCell);
          if (mcGasPricesCell) fixture.stack_init.config_mc_gas_prices_boc = bocBase64(mcGasPricesCell);
          if (gasPricesCell) fixture.stack_init.config_gas_prices_boc = bocBase64(gasPricesCell);
          if (mcFwdPricesCell) fixture.stack_init.config_mc_fwd_prices_boc = bocBase64(mcFwdPricesCell);
          if (fwdPricesCell) fixture.stack_init.config_fwd_prices_boc = bocBase64(fwdPricesCell);
          if (sizeLimitsCell) fixture.stack_init.config_size_limits_boc = bocBase64(sizeLimitsCell);
          if (precompiledContractsCell) fixture.stack_init.config_precompiled_contracts_boc = bocBase64(precompiledContractsCell);

          if (sandbox) {
            const blockConfig = blockCfg.configCell;

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

            if (sandbox.debugExecutor) {
              const dbg = sandbox.debugExecutor;
              const { emptr } = dbg.sbsTransactionSetup({
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

                if (c7.type === "tuple" && c7.items[0]?.type === "tuple") {
                  // Override balance/in_msg_value from c7 to match the exact VM init values used by the emulator.
                  const env = c7.items[0];
                  const bal = env.items[7];
                  if (bal?.type === "tuple" && bal.items[0]?.type === "int") {
                    fixture.stack_init.balance_grams = bal.items[0].value.toString(10);
                  }
                  const inMsgVal = env.items[11];
                  if (inMsgVal?.type === "tuple" && inMsgVal.items[0]?.type === "int") {
                    fixture.stack_init.msg_balance_grams = inMsgVal.items[0].value.toString(10);
                  }

                  // Capture MYCODE from c7 (can differ from `code_boc`, e.g. when the executable code was a resolved library).
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

          const outPath = path.join(opts.runLean ? batchDir : opts.outDir, `${txHashHex}.json`);
          await writeFile(outPath, JSON.stringify(fixture, null, 2), "utf8");
          if (opts.runLean && opts.keepFixtures) {
            const keepPath = path.join(opts.outDir, `${txHashHex}.json`);
            await writeFile(keepPath, JSON.stringify(fixture, null, 2), "utf8");
          }
          totalFixtures++;

          if (opts.runLean && totalFixtures % opts.batchSize === 0) {
            await runLeanBatch(opts, batchDir);
            await rm(batchDir, { recursive: true, force: true });
            await mkdir(batchDir, { recursive: true });
          }
        } catch (e: any) {
          skipped.errors++;
          const msg = e?.stack ?? e?.message ?? String(e);
          console.log(`✗ ${txHashHex}: ${msg}`);
        }
      }

      if (stop) break;
    }

    console.log(`mc_seqno=${seqno} scanned=${totalTxs} fixtures=${totalFixtures}`);
    if (stop) break;
  }

  if (opts.runLean) {
    // Run the final partial batch, if any.
    const files = await readdir(batchDir).catch(() => []);
    if (files.some((f) => f.endsWith(".json"))) {
      await runLeanBatch(opts, batchDir);
    }
  }

  console.log(
    `skipped: nonFirst=${skipped.nonFirst} nonGeneric=${skipped.nonGeneric} computeNotVm=${skipped.computeNotVm} noInMsg=${skipped.noInMsg} noCode=${skipped.noCode} errors=${skipped.errors}`,
  );
}

main().catch((e) => {
  // eslint-disable-next-line no-console
  console.error(e);
  process.exit(1);
});
