# PrimeNumberTheoremAnd source provenance

The 9 Lean modules in this directory are taken from
[AlexKontorovich/PrimeNumberTheoremAnd](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd)
at commit `c39a751132c88b6e8080b74c74023fd95b3d8be0` (2026-09-30), by Alex
Kontorovich, Terence Tao, and the other contributors recorded upstream. They
are distributed under the Apache License 2.0, whose full text is in
[LICENSE](LICENSE).

They keep their upstream module names (`PrimeNumberTheoremAnd.*`) and fall into
two groups:

- `Wiener`, `Fourier`, `SmoothExistence`, and `Sobolev` are the import closure
  of `PrimeNumberTheoremAnd.Wiener`, which the vendored OAI library imports.
  They are taken with the compatibility patch
  `lean/patches/PrimeNumberTheoremAnd-lean4341.patch` from
  [openai/math](https://github.com/openai/math) at commit
  `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` applied, as the OAI library builds
  them, and are otherwise unchanged.
- `PerronFormula`, `ResidueCalcOnRectangles`, `Rectangle`, and
  `Mathlib/Analysis/Asymptotics/{Asymptotics,Uniformly}` supply the smoothed
  Perron formula and rectangle residue calculus used by `Erdos420/Analytic/`.
  The same patch applies to `PerronFormula`.

The upstream source pins Lean `v4.34.0`, and this project pins Lean and
Mathlib `v4.35.0-rc4`. Three modules were changed to build here without
LeanArchitect:

- `PerronFormula`, `ResidueCalcOnRectangles`, and `Rectangle` no longer import
  `Architect`. Their `blueprint_comment` blocks and `@[blueprint …]`
  attributes, which carry only blueprint metadata, are removed.
- `PerronFormula` uses LeanArchitect's docstrings inside tactic blocks. These
  are now ordinary comments.
- Mathlib deleted `Mathlib.Tactic.LinearCombinationPrime`, which upstream's
  `PrimeNumberTheoremAnd.Tactic.AdditiveCombination` needs. That module is
  dropped, and its single use in `ResidueCalcOnRectangles` became
  `linear_combination (norm := module)` with the same hypotheses.
