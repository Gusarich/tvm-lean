import { spawn } from "node:child_process";
import { createHash } from "node:crypto";
import { rm, writeFile } from "node:fs/promises";
import os from "node:os";
import path from "node:path";

import {
  Address,
  beginCell,
  Cell,
  Dictionary,
  loadMessage,
  type CommonMessageInfo,
  type ExternalAddress,
} from "@ton/core";

export type StackInitForFift = {
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
  config_root_boc?: string;
  config_storage_prices_boc?: string;
  config_global_id_boc?: string;
  config_mc_gas_prices_boc?: string;
  config_gas_prices_boc?: string;
  config_size_limits_boc?: string;
  config_mc_fwd_prices_boc?: string;
  config_fwd_prices_boc?: string;
  config_precompiled_contracts_boc?: string;
};

export type FixtureForFift = {
  code_boc: string;
  mycode_boc?: string;
  data_boc: string;
  stack_init: StackInitForFift;
  expected: {
    gas_limit?: string;
    gas_max?: string;
    gas_credit?: string;
  };
};

export type FiftExpectedState = {
  exitRaw: number;
  gasUsed: bigint;
  c4_boc: string;
  c5_boc: string;
};

type FiftValue =
  | { kind: "null" }
  | { kind: "int"; value: bigint }
  | { kind: "cell"; boc: string }
  | { kind: "slice"; boc: string }
  | { kind: "tuple"; items: FiftValue[] };

function q(s: string): string {
  return `"${s.replaceAll("\\", "\\\\").replaceAll('"', '\\"')}"`;
}

function toBytesFromHex(hex: string): Buffer {
  if (hex.length % 2 !== 0) {
    throw new Error(`hex length must be even, got ${hex.length}`);
  }
  return Buffer.from(hex, "hex");
}

function decodeBocToCell(input: string): Cell {
  const raw = input.trim();
  let bytes: Buffer;
  if (raw.startsWith("hex:")) {
    bytes = toBytesFromHex(raw.slice(4));
  } else if (raw.startsWith("base64:")) {
    bytes = Buffer.from(raw.slice(7), "base64");
  } else {
    bytes = Buffer.from(raw, "base64");
  }
  return Cell.fromBoc(bytes)[0]!;
}

function normalizeBocBase64(input: string): string {
  return decodeBocToCell(input).toBoc().toString("base64");
}

function parseIntDec(v: string | undefined, fallback: bigint): bigint {
  if (!v || v.trim().length === 0) return fallback;
  try {
    return BigInt(v);
  } catch {
    return fallback;
  }
}

function toU256BytesBE(x: bigint): Buffer {
  const out = Buffer.alloc(32);
  let v = x;
  for (let i = 31; i >= 0; i--) {
    out[i] = Number(v & 0xffn);
    v >>= 8n;
  }
  return out;
}

function bytesToBigIntBE(buf: Buffer): bigint {
  let x = 0n;
  for (const b of buf) x = (x << 8n) + BigInt(b);
  return x;
}

function addrNoneSliceBoc(): string {
  return beginCell().storeAddress(null).endCell().toBoc().toString("base64");
}

function addrToSliceBoc(addr: Address | ExternalAddress | null | undefined): string {
  return beginCell().storeAddress(addr ?? null).endCell().toBoc().toString("base64");
}

function maybeCellVal(boc: string | undefined): FiftValue {
  return boc && boc.length > 0
    ? { kind: "cell", boc: normalizeBocBase64(boc) }
    : { kind: "null" };
}

function maybeSliceVal(boc: string | undefined): FiftValue {
  return boc && boc.length > 0
    ? { kind: "slice", boc: normalizeBocBase64(boc) }
    : { kind: "null" };
}

function lookupPrecompiledGasUsage(
  configPrecompiledContractsBoc: string | undefined,
  myCodeBoc: string,
): FiftValue {
  if (!configPrecompiledContractsBoc || configPrecompiledContractsBoc.length === 0) {
    return { kind: "null" };
  }

  try {
    const cfgCell = decodeBocToCell(configPrecompiledContractsBoc);
    const s = cfgCell.beginParse();
    const tag = s.loadUint(8);
    if (tag !== 0xc0) return { kind: "null" };
    const hasRoot = s.loadUint(1);
    if (hasRoot === 0) return { kind: "null" };
    const root = s.loadRef();

    const precompiledValue = {
      parse: (src: any): bigint => {
        const entryTag = src.loadUint(8);
        if (entryTag !== 0xb0) {
          throw new Error(`unexpected precompiled entry tag: 0x${entryTag.toString(16)}`);
        }
        return src.loadUintBig(64);
      },
      serialize: (_src: bigint, _builder: any): void => {
        throw new Error("not implemented");
      },
    };

    const dict = Dictionary.loadDirect(Dictionary.Keys.BigUint(256), precompiledValue, root) as Dictionary<bigint, bigint>;

    const myCodeHash = decodeBocToCell(myCodeBoc).hash();
    const key = bytesToBigIntBE(myCodeHash);
    const gasUsage = dict.get(key);
    if (gasUsage === undefined) return { kind: "null" };
    return { kind: "int", value: gasUsage };
  } catch {
    return { kind: "null" };
  }
}

type StoragePricesEntry = {
  validSince: bigint;
  bitPrice: bigint;
  cellPrice: bigint;
  mcBitPrice: bigint;
  mcCellPrice: bigint;
};

function selectCurrentStoragePricesSliceBoc(
  configStoragePricesBoc: string | undefined,
  now: bigint,
): string | null {
  if (!configStoragePricesBoc || configStoragePricesBoc.length === 0) return null;

  const cfgCell = decodeBocToCell(configStoragePricesBoc);
  const storagePricesValue = {
    parse: (src: any): StoragePricesEntry => {
      const tag = src.loadUint(8);
      if (tag !== 0xcc) {
        throw new Error(`invalid StoragePrices tag: 0x${tag.toString(16)}`);
      }
      return {
        validSince: BigInt(src.loadUint(32)),
        bitPrice: src.loadUintBig(64),
        cellPrice: src.loadUintBig(64),
        mcBitPrice: src.loadUintBig(64),
        mcCellPrice: src.loadUintBig(64),
      };
    },
    serialize: (src: StoragePricesEntry, builder: any): void => {
      builder.storeUint(0xcc, 8);
      builder.storeUint(Number(src.validSince), 32);
      builder.storeUint(src.bitPrice, 64);
      builder.storeUint(src.cellPrice, 64);
      builder.storeUint(src.mcBitPrice, 64);
      builder.storeUint(src.mcCellPrice, 64);
    },
  };

  const dict = Dictionary.loadDirect(
    Dictionary.Keys.BigUint(32),
    storagePricesValue,
    cfgCell,
  ) as Dictionary<bigint, StoragePricesEntry>;

  let bestKey: bigint | undefined;
  let bestVal: StoragePricesEntry | undefined;

  for (const [k, v] of dict) {
    if (k <= now && (bestKey === undefined || k > bestKey)) {
      bestKey = k;
      bestVal = v;
    }
  }

  if (!bestVal) return null;

  return beginCell()
    .storeUint(0xcc, 8)
    .storeUint(Number(bestVal.validSince), 32)
    .storeUint(bestVal.bitPrice, 64)
    .storeUint(bestVal.cellPrice, 64)
    .storeUint(bestVal.mcBitPrice, 64)
    .storeUint(bestVal.mcCellPrice, 64)
    .endCell()
    .toBoc()
    .toString("base64");
}

function parseGlobalVersionFromConfigRoot(configRootBoc: string | undefined): bigint {
  if (!configRootBoc || configRootBoc.length === 0) return 0n;
  try {
    const root = decodeBocToCell(configRootBoc);
    const params = root
      .beginParse()
      .loadDictDirect(Dictionary.Keys.Int(32), Dictionary.Values.Cell()) as Dictionary<number, Cell>;
    const p8 = params.get(8);
    if (!p8) return 0n;
    const s = p8.beginParse();
    const tag = s.loadUint(8);
    if (tag !== 0xc4) return 0n;
    const version = s.loadUint(32);
    return BigInt(version);
  } catch {
    return 0n;
  }
}

function defaultInMsgParams(msgBalance: bigint): FiftValue {
  const addrNone = addrNoneSliceBoc();
  return {
    kind: "tuple",
    items: [
      { kind: "int", value: 0n },
      { kind: "int", value: 0n },
      { kind: "slice", boc: addrNone },
      { kind: "int", value: 0n },
      { kind: "int", value: 0n },
      { kind: "int", value: 0n },
      { kind: "int", value: 0n },
      { kind: "int", value: msgBalance },
      { kind: "null" },
      { kind: "null" },
    ],
  };
}

function inMsgParamsFromInfo(info: CommonMessageInfo, msgBalance: bigint): FiftValue {
  const addrNone = addrNoneSliceBoc();
  if (info.type === "internal") {
    return {
      kind: "tuple",
      items: [
        { kind: "int", value: info.bounce ? -1n : 0n },
        { kind: "int", value: info.bounced ? -1n : 0n },
        { kind: "slice", boc: addrToSliceBoc(info.src) },
        { kind: "int", value: info.forwardFee },
        { kind: "int", value: info.createdLt },
        { kind: "int", value: BigInt(info.createdAt) },
        { kind: "int", value: info.value.coins },
        { kind: "int", value: msgBalance },
        { kind: "null" },
        { kind: "null" },
      ],
    };
  }
  if (info.type === "external-in") {
    return {
      kind: "tuple",
      items: [
        { kind: "int", value: 0n },
        { kind: "int", value: 0n },
        { kind: "slice", boc: addrToSliceBoc(info.src ?? null) },
        { kind: "int", value: 0n },
        { kind: "int", value: 0n },
        { kind: "int", value: 0n },
        { kind: "int", value: 0n },
        { kind: "int", value: msgBalance },
        { kind: "null" },
        { kind: "null" },
      ],
    };
  }
  return {
    kind: "tuple",
    items: [
      { kind: "int", value: 0n },
      { kind: "int", value: 0n },
      { kind: "slice", boc: addrNone },
      { kind: "int", value: 0n },
      { kind: "int", value: 0n },
      { kind: "int", value: 0n },
      { kind: "int", value: 0n },
      { kind: "int", value: 0n },
      { kind: "null" },
      { kind: "null" },
    ],
  };
}

function buildInitialC7(fx: FixtureForFift): FiftValue {
  const si = fx.stack_init;

  const balance = parseIntDec(si.balance_grams, 0n);
  const msgBalance = parseIntDec(si.msg_balance_grams, 0n);
  const now = parseIntDec(si.now, 0n);
  const lt = parseIntDec(si.lt, 0n);
  const randSeedRaw = parseIntDec(si.rand_seed, 0n);
  const storageFees = parseIntDec(si.storage_fees, 0n);
  const duePayment = parseIntDec(si.due_payment, 0n);

  let myAddr: Address | ExternalAddress | null = null;
  let inMsgParams: FiftValue = defaultInMsgParams(msgBalance);

  try {
    const inMsg = loadMessage(decodeBocToCell(si.in_msg_boc).beginParse());
    if (inMsg.info.type === "internal") {
      myAddr = inMsg.info.dest;
    } else if (inMsg.info.type === "external-in") {
      myAddr = inMsg.info.dest;
    } else {
      myAddr = inMsg.info.src;
    }
    inMsgParams = inMsgParamsFromInfo(inMsg.info, msgBalance);
  } catch {
    // Keep conservative defaults.
  }

  const myAddrSlice = myAddr ? addrToSliceBoc(myAddr) : addrNoneSliceBoc();

  const randSeedFinal: bigint =
    randSeedRaw >= 0n && randSeedRaw < (1n << 256n)
      ? bytesToBigIntBE(
          createHash("sha256")
            .update(
              Buffer.concat([
                toU256BytesBE(randSeedRaw),
                Address.isAddress(myAddr) ? myAddr.hash : Buffer.alloc(32),
              ]),
            )
            .digest(),
        )
      : 0n;

  const blockLt = lt < 0n ? 0n : lt - (lt % 1_000_000n);
  const myCodeBoc = normalizeBocBase64(fx.mycode_boc ?? fx.code_boc);
  const precompiledGasUsage = lookupPrecompiledGasUsage(si.config_precompiled_contracts_boc, myCodeBoc);
  const storagePricesSliceBoc = selectCurrentStoragePricesSliceBoc(si.config_storage_prices_boc, now);

  const unpackedConfig: FiftValue = {
    kind: "tuple",
    items: [
      storagePricesSliceBoc ? { kind: "slice", boc: storagePricesSliceBoc } : { kind: "null" },
      maybeSliceVal(si.config_global_id_boc),
      maybeSliceVal(si.config_mc_gas_prices_boc),
      maybeSliceVal(si.config_gas_prices_boc),
      maybeSliceVal(si.config_mc_fwd_prices_boc),
      maybeSliceVal(si.config_fwd_prices_boc),
      maybeSliceVal(si.config_size_limits_boc),
    ],
  };

  const env: FiftValue = {
    kind: "tuple",
    items: [
      { kind: "int", value: 0x076ef1ean },
      { kind: "int", value: 0n },
      { kind: "int", value: 0n },
      { kind: "int", value: now },
      { kind: "int", value: blockLt },
      { kind: "int", value: lt },
      { kind: "int", value: randSeedFinal },
      { kind: "tuple", items: [{ kind: "int", value: balance }, { kind: "null" }] },
      { kind: "slice", boc: myAddrSlice },
      maybeCellVal(si.config_root_boc),
      { kind: "cell", boc: myCodeBoc },
      { kind: "tuple", items: [{ kind: "int", value: msgBalance }, { kind: "null" }] },
      { kind: "int", value: storageFees },
      { kind: "null" },
      unpackedConfig,
      { kind: "int", value: duePayment },
      precompiledGasUsage,
      inMsgParams,
    ],
  };

  return { kind: "tuple", items: [env] };
}

function emitFiftValue(v: FiftValue): string {
  switch (v.kind) {
    case "null":
      return "null";
    case "int":
      return v.value.toString(10);
    case "cell":
      return `${q(v.boc)} base64>B B>boc`;
    case "slice":
      return `${q(v.boc)} base64>B B>boc <s`;
    case "tuple": {
      const items = v.items.map((it) => emitFiftValue(it));
      const body = items.join("\n");
      return body.length > 0 ? `${body}\n${v.items.length} tuple` : "0 tuple";
    }
  }
}

function parseOracleOutput(stdout: string): FiftExpectedState {
  const lines = stdout
    .split(/\r?\n/g)
    .map((l) => l.trim())
    .filter((l) => l.length > 0);

  let exitRaw: number | undefined;
  let gasUsed: bigint | undefined;
  let c4: string | undefined;
  let c5: string | undefined;

  for (const ln of lines) {
    const cols = ln.split("\t");
    if (cols.length !== 2) continue;
    const [k, v] = cols;
    if (k === "EXIT") {
      const n = Number(v);
      if (!Number.isInteger(n)) throw new Error(`bad EXIT '${v}'`);
      exitRaw = n;
    } else if (k === "GAS") {
      gasUsed = BigInt(v);
    } else if (k === "C4_BOC") {
      c4 = v;
    } else if (k === "C5_BOC") {
      c5 = v;
    }
  }

  if (exitRaw === undefined) throw new Error("missing EXIT");
  if (gasUsed === undefined) throw new Error("missing GAS");
  if (!c4) throw new Error("missing C4_BOC");
  if (!c5) throw new Error("missing C5_BOC");

  return { exitRaw, gasUsed, c4_boc: c4, c5_boc: c5 };
}

async function runProcess(
  cmd: string,
  args: string[],
  env: Record<string, string>,
): Promise<{ code: number; stdout: string; stderr: string }> {
  return await new Promise((resolve, reject) => {
    const p = spawn(cmd, args, {
      env: { ...process.env, ...env },
      stdio: ["ignore", "pipe", "pipe"],
    });

    let stdout = "";
    let stderr = "";

    p.stdout.setEncoding("utf8");
    p.stderr.setEncoding("utf8");

    p.stdout.on("data", (chunk: string) => {
      stdout += chunk;
    });
    p.stderr.on("data", (chunk: string) => {
      stderr += chunk;
    });

    p.on("error", reject);
    p.on("close", (code) => {
      resolve({ code: code ?? -1, stdout, stderr });
    });
  });
}

export async function computeExpectedStateWithFift(fx: FixtureForFift): Promise<FiftExpectedState> {
  const tonFift = process.env["TON_FIFT_BIN"] ?? "fift";
  const tonLib = process.env["TON_FIFT_LIB"];

  const balance = parseIntDec(fx.stack_init.balance_grams, 0n);
  const msgBalance = parseIntDec(fx.stack_init.msg_balance_grams, 0n);
  const inMsgCell = normalizeBocBase64(fx.stack_init.in_msg_boc);
  const inMsgBody = normalizeBocBase64(fx.stack_init.in_msg_body_boc);
  const codeBoc = normalizeBocBase64(fx.code_boc);
  const dataBoc = normalizeBocBase64(fx.data_boc);
  const myCodeBoc = normalizeBocBase64(fx.mycode_boc ?? fx.code_boc);
  const precompiledGasUsage = lookupPrecompiledGasUsage(fx.stack_init.config_precompiled_contracts_boc, myCodeBoc);
  if (precompiledGasUsage.kind === "int") {
    throw new Error(
      `precompiled contract detected (config_param_45 gas=${precompiledGasUsage.value.toString(10)}); runvm oracle unsupported`,
    );
  }
  const c7 = buildInitialC7(fx);

  const gasLimit = parseIntDec(fx.expected.gas_limit, 1_000_000n);
  const gasCredit = parseIntDec(fx.expected.gas_credit, 0n);
  const gasMax0 = parseIntDec(fx.expected.gas_max, gasLimit);
  const gasMax = gasMax0 < gasLimit ? gasLimit : gasMax0;
  // `runvmx` cannot set `gas_credit` separately. TON VM starts with `gas_remaining = gas_limit + gas_credit`,
  // so we emulate this by folding credit into the passed gas limit.
  const gasLimitForVm = gasLimit + gasCredit;
  const globalVersion = parseGlobalVersionFromConfigRoot(fx.stack_init.config_root_boc);
  const inMsgExternFlag = fx.stack_init.in_msg_extern ? -1n : 0n;

  // mode bits:
  // +1 same_c3, +4 c4 in/out, +8 gas in/out, +16 c7 in, +32 c5 out,
  // +128 gas_max in, +1024 global_version in.
  const mode = 1 + 4 + 8 + 16 + 32 + 128 + 1024;

  const script = `${q("Fift.fif")} include

{ swap type 9 emit type cr } : print-kv
{ boc>B B>base64 } : cell>boc64$
{ dup null? { drop <b b> } { dup (dump) "C{null}" $= { drop <b b> } { } cond } cond cell>boc64$ } : maybe-cell>boc64$

${balance.toString(10)}
${msgBalance.toString(10)}
${q(inMsgCell)} base64>B B>boc
${q(inMsgBody)} base64>B B>boc <s
${inMsgExternFlag.toString(10)}
${q(codeBoc)} base64>B B>boc <s
${q(dataBoc)} base64>B B>boc
${emitFiftValue(c7)}
${gasLimitForVm.toString(10)}
${gasMax.toString(10)}
${globalVersion.toString(10)}
${mode}
runvmx

variable _gas
variable _act
variable _data
variable _exit
_gas !
_act !
_data !
_exit !

"EXIT" _exit @ (.) print-kv
"GAS" _gas @ (.) print-kv
"C4_BOC" _data @ maybe-cell>boc64$ print-kv
"C5_BOC" _act @ maybe-cell>boc64$ print-kv

bye
`;

  const tmpPath = path.join(
    os.tmpdir(),
    `tvmlean_collect_${process.pid}_${Date.now()}_${Math.random().toString(16).slice(2)}.fif`,
  );

  await writeFile(tmpPath, script, "utf8");
  try {
    const args = tonLib ? [`-I${tonLib}`, "-s", tmpPath] : ["-s", tmpPath];
    let res: { code: number; stdout: string; stderr: string };
    try {
      res = await runProcess(tonFift, args, { GLOG_minloglevel: "2" });
    } catch (e: any) {
      throw new Error(
        `failed to execute TON fift binary '${tonFift}' (set TON_FIFT_BIN and TON_FIFT_LIB): ${e?.message ?? String(e)}`,
      );
    }
    if (res.code !== 0) {
      throw new Error(`fift exited with code ${res.code}\n${res.stderr}\n${res.stdout}`);
    }
    return parseOracleOutput(res.stdout);
  } finally {
    await rm(tmpPath, { force: true });
  }
}
