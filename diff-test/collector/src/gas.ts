import { Address, Cell, Dictionary, Slice } from "@ton/core";

export type GasLimitsPrices = {
  gasPrice: bigint;
  gasLimit: bigint;
  gasCredit: bigint;
  specialGasLimit: bigint;
  flatGasLimit: bigint;
  flatGasPrice: bigint;
};

export type ParsedGlobalConfig = {
  globalVersion: number;
  configAddr: bigint;
  fundamentalSmc: Dictionary<bigint, boolean>;
  mcGas: GasLimitsPrices;
  baseGas: GasLimitsPrices;
};

function bytesToBigIntBE(buf: Buffer): bigint {
  let x = 0n;
  for (const b of buf) x = (x << 8n) + BigInt(b);
  return x;
}

function parseGlobalVersion(param8?: Cell | null): number {
  if (!param8) return 0;
  const s = param8.beginParse();
  const tag = s.loadUint(8);
  if (tag !== 0xc4) {
    throw new Error(`ConfigParam(8) GlobalVersion: unexpected tag 0x${tag.toString(16)}`);
  }
  const version = s.loadUint(32);
  // capabilities:uint64
  s.loadUintBig(64);
  return version;
}

function parseGasLimitsPricesFromSlice(s: Slice): GasLimitsPrices {
  const tag = s.loadUint(8);

  // gas_flat_pfx#d1 flat_gas_limit:uint64 flat_gas_price:uint64 other:GasLimitsPrices
  if (tag === 0xd1) {
    const flatGasLimit = s.loadUintBig(64);
    const flatGasPrice = s.loadUintBig(64);
    const inner = parseGasLimitsPricesFromSlice(s);
    return { ...inner, flatGasLimit, flatGasPrice };
  }

  // gas_prices#dd gas_price:uint64 gas_limit:uint64 gas_credit:uint64 ...
  if (tag === 0xdd) {
    const gasPrice = s.loadUintBig(64);
    const gasLimit = s.loadUintBig(64);
    const gasCredit = s.loadUintBig(64);
    // block_gas_limit:uint64 freeze_due_limit:uint64 delete_due_limit:uint64
    s.loadUintBig(64);
    s.loadUintBig(64);
    s.loadUintBig(64);
    return {
      gasPrice,
      gasLimit,
      gasCredit,
      specialGasLimit: gasLimit,
      flatGasLimit: 0n,
      flatGasPrice: 0n,
    };
  }

  // gas_prices_ext#de gas_price:uint64 gas_limit:uint64 special_gas_limit:uint64 gas_credit:uint64 ...
  if (tag === 0xde) {
    const gasPrice = s.loadUintBig(64);
    const gasLimit = s.loadUintBig(64);
    const specialGasLimit = s.loadUintBig(64);
    const gasCredit = s.loadUintBig(64);
    // block_gas_limit:uint64 freeze_due_limit:uint64 delete_due_limit:uint64
    s.loadUintBig(64);
    s.loadUintBig(64);
    s.loadUintBig(64);
    return {
      gasPrice,
      gasLimit,
      gasCredit,
      specialGasLimit,
      flatGasLimit: 0n,
      flatGasPrice: 0n,
    };
  }

  throw new Error(`GasLimitsPrices: unexpected tag 0x${tag.toString(16)}`);
}

function parseGasLimitsPrices(cell: Cell): GasLimitsPrices {
  return parseGasLimitsPricesFromSlice(cell.beginParse());
}

export function parseGlobalConfig(configCellB64: string): ParsedGlobalConfig {
  // TonClient4.getConfig().config.cell is a dict of config params keyed by int32.
  const params = Cell.fromBase64(configCellB64)
    .beginParse()
    .loadDictDirect(Dictionary.Keys.Int(32), Dictionary.Values.Cell());

  const configAddrCell = params.get(0);
  if (!configAddrCell) throw new Error("ConfigParam(0) missing (config addr)");
  const configAddr = configAddrCell.beginParse().loadUintBig(256);

  const globalVersion = parseGlobalVersion(params.get(8));

  const mcGasCell = params.get(20);
  const baseGasCell = params.get(21);
  if (!mcGasCell) throw new Error("ConfigParam(20) missing (mc gas prices)");
  if (!baseGasCell) throw new Error("ConfigParam(21) missing (base gas prices)");

  const mcGas = parseGasLimitsPrices(mcGasCell);
  const baseGas = parseGasLimitsPrices(baseGasCell);

  // ConfigParam(31): _ fundamental_smc_addr:(HashmapE 256 True)
  const fundamentalCell = params.get(31);
  const TrueValue: any = {
    serialize: (_src: boolean, _builder: any) => {
      // `True` has no fields.
    },
    parse: (src: Slice) => {
      src.endParse();
      return true;
    },
  };
  const fundamentalSmc: Dictionary<bigint, boolean> = fundamentalCell
    ? (fundamentalCell.beginParse().loadDict(Dictionary.Keys.BigUint(256), TrueValue) as any)
    : (Dictionary.empty(Dictionary.Keys.BigUint(256), TrueValue) as any);

  return { globalVersion, configAddr, fundamentalSmc, mcGas, baseGas };
}

type OverrideEntry = {
  address: Address;
  newLimit: bigint;
  fromVersion: number;
  until: number; // unix time
};

const OVERRIDES: OverrideEntry[] = [
  {
    address: Address.parse("0:FFBFD8F5AE5B2E1C7C3614885CB02145483DFAEE575F0DD08A72C366369211CD"),
    newLimit: 70_000_000n,
    fromVersion: 5,
    until: 1709164800, // 2024-02-29 00:00:00 UTC
  },
  {
    address: Address.parse("UQBeSl-dumOHieZ3DJkNKVkjeso7wZ0VpzR4LCbLGTQ8xr57"),
    newLimit: 70_000_000n,
    fromVersion: 9,
    until: 1740787200, // 2025-03-01 00:00:00 UTC
  },
  {
    address: Address.parse("EQC3VcQ-43klww9UfimR58TBjBzk7GPupXQ3CNuthoNp-uTR"),
    newLimit: 70_000_000n,
    fromVersion: 9,
    until: 1740787200,
  },
  {
    address: Address.parse("EQBhwBb8jvokGvfreHRRoeVxI237PrOJgyrsAhLA-4rBC_H5"),
    newLimit: 70_000_000n,
    fromVersion: 9,
    until: 1740787200,
  },
  {
    address: Address.parse("EQCkoRp4OE-SFUoMEnYfL3vF43T3AzNfW8jyTC4yzk8cJqMS"),
    newLimit: 70_000_000n,
    fromVersion: 9,
    until: 1740787200,
  },
  {
    address: Address.parse("UQBN5ICras79U8FYEm71ws34n-ZNIQ0LRNpckOUsIV3OebnC"),
    newLimit: 70_000_000n,
    fromVersion: 9,
    until: 1740787200,
  },
  {
    address: Address.parse("EQBDanbCeUqI4_v-xrnAN0_I2wRvEIaLg1Qg2ZN5c6Zl1KOh"),
    newLimit: 225_000_000n,
    fromVersion: 9,
    until: 1740787200,
  },
];

function overrideGasLimit(globalVersion: number, now: number, address: Address): bigint | undefined {
  for (const e of OVERRIDES) {
    if (globalVersion >= e.fromVersion && now < e.until && address.equals(e.address)) {
      return e.newLimit;
    }
  }
  return undefined;
}

function computeMaxGasThreshold(cfg: GasLimitsPrices, gasLimitOverride?: bigint): bigint {
  const gasLimit = gasLimitOverride ?? cfg.gasLimit;
  if (gasLimit > cfg.flatGasLimit) {
    return ((cfg.gasPrice * (gasLimit - cfg.flatGasLimit)) >> 16n) + cfg.flatGasPrice;
  }
  return cfg.flatGasPrice;
}

function gasBoughtFor(cfg: GasLimitsPrices, nanograms: bigint, gasLimitOverride?: bigint): bigint {
  if (nanograms < 0n) return 0n;
  const gasLimit = gasLimitOverride ?? cfg.gasLimit;
  const maxGasThreshold = computeMaxGasThreshold(cfg, gasLimitOverride);
  if (nanograms >= maxGasThreshold) return gasLimit;
  if (nanograms < cfg.flatGasPrice) return 0n;
  const res = ((nanograms - cfg.flatGasPrice) << 16n) / cfg.gasPrice;
  return res + cfg.flatGasLimit;
}

function addrBits256(addr: Address): bigint {
  return bytesToBigIntBE(addr.hash);
}

export function computeGasInit(cfg: ParsedGlobalConfig, args: {
  workchain: number;
  address: Address;
  now: number;
  balanceGrams: bigint;
  msgBalanceGrams: bigint;
  inMsgExtern: boolean;
}): { gasMax: bigint; gasLimit: bigint; gasCredit: bigint } {
  const gasCfg = args.workchain === -1 ? cfg.mcGas : cfg.baseGas;
  const addrKey = addrBits256(args.address);
  const isSpecial =
    args.workchain === -1 && (addrKey === cfg.configAddr || cfg.fundamentalSmc.get(addrKey) === true);

  const limitOverride = overrideGasLimit(cfg.globalVersion, args.now, args.address);

  const gasMax = isSpecial ? gasCfg.specialGasLimit : gasBoughtFor(gasCfg, args.balanceGrams, limitOverride);
  const specialGasFull = cfg.globalVersion >= 5;
  const msgGas = gasBoughtFor(gasCfg, args.msgBalanceGrams, limitOverride);
  const gasLimit = isSpecial && specialGasFull ? gasMax : (msgGas < gasMax ? msgGas : gasMax);

  const gasCredit = args.inMsgExtern ? (gasCfg.gasCredit < gasMax ? gasCfg.gasCredit : gasMax) : 0n;

  return { gasMax, gasLimit, gasCredit };
}
