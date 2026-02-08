# Dependency Graph

The repository enforces strict import direction:

- `Model` imports only `Model`
- `Semantics` imports `Model` and `Semantics`
- `Native` imports `Model` (and its own namespace)
- `Validation` imports `Model`, `Semantics`, and `Native`
- `Tests` imports harness + validation/model/semantics/native as needed

## Layered view

```text
Tests / Apps
    |
Validation
   / \
Semantics Native
    |
   Model
```

## Hard rules

- No file under `TvmLean/Model/` may import `TvmLean/Semantics/`, `TvmLean/Native/`,
  or `TvmLean/Validation/`.
- No file under `TvmLean/Semantics/` may import `TvmLean/Native/` or
  `TvmLean/Validation/`.
- All `@[extern]` declarations live only in `TvmLean/Native/Extern/`.

## Enforcement

Lake targets encode the same structure:

- `TvmLeanModel`
- `TvmLeanSemantics`
- `TvmLeanNative`
- `TvmLeanValidation`
- `TvmLeanTests`

A fresh `lake build` defaults to Model + Semantics only, so proof workflows do not
require native linkage.
