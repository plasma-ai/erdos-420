# OAI source provenance

The 2,924 Lean modules in this directory are taken from the `lean/` directory
of [openai/math](https://github.com/openai/math) at commit
`fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` (2026-10-07). As recorded upstream,
they were produced by an internal OpenAI model. They are distributed under the
Apache License 2.0, whose full text is in [LICENSE](LICENSE).

They are the import closure of `OAI.NumberTheory.DirichletL.Nonvanishing`, not
the whole upstream library, and keep their upstream module names. That module
proves `OAI.DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re`: every
Dirichlet L-function is zero-free in `re s > 7/8`, apart from the principal
character's pole at `s = 1`. This is Theorem 1.1 of
[*The Quasi-Riemann Hypothesis*](https://github.com/openai/math/blob/main/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf),
and upstream checks it with Comparator against
`lean/ComparatorChallenges/DirichletSevenEighths.lean`.
`Erdos420/Analytic/QuasiRH.lean` restates it for this project.

The closure also imports `PrimeNumberTheoremAnd.Wiener` and
`RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.Rellich`, which
are vendored alongside it in `vendor/PrimeNumberTheoremAnd/` and
`vendor/RellichKondrachov/`.

Upstream pins Lean `v4.34.1` and Mathlib commit `d13f23b`. This project pins
Lean and Mathlib `v4.35.0-rc4`, and 33 of the modules were changed to build
here. The changes follow Lean and Mathlib changes and keep every statement:

- A singleton set literal whose element spans several lines is now parsed as
  the start of set-builder notation. In 21 modules under `CubicSieve/`,
  `Descent/`, `Eisenstein/`, `Energy/`, `Fourier/`, `GaussSum/`, `Moments/`,
  and `RowCompletion/`, the element of such an `Ideal.span {…}` is
  parenthesized.
- `MemLp.indicator` takes a `NullMeasurableSet`, so
  `Eisenstein/CompactEnergyFamilies.lean` passes `hK.nullMeasurableSet`.
- `Measure.QuasiMeasurePreserving` is now `QuasiMeasurePreserving`, and field
  notation no longer resolves through the deprecated alias. Eight modules under
  `Eisenstein/` and `Reciprocity/` use the new name.
- Core's `ULift.ext` takes `x` and `y` implicitly, so
  `Reflection/SectorData.lean` passes them by name.
- `congr 1` now closes two goals outright, so the tactics that followed it in
  `Moments/FirstSectors.lean` and `Moments/CommonAllocationSum.lean` are
  removed.

No `sorry`, `axiom`, or heartbeat option was added.
