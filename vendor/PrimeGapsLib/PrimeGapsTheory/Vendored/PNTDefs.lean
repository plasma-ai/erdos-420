module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
public import Mathlib.Analysis.Fourier.FourierTransformDeriv
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.Order.Filter.ZeroAndBoundedAtFilter
public import Mathlib.Topology.ContinuousMap.Bounded.Basic

/-!
# Stand-in for `PrimeNumberTheoremAnd.Defs`

Upstream imports `PrimeNumberTheoremAnd.Defs` from AxiomMath's fork of `PrimeNumberTheoremAnd`,
whose module names clash with the upstream `PrimeNumberTheoremAnd` vendored alongside. This module
replaces that import with the Mathlib modules it brought in; see `vendor/PrimeGapsLib/README.md`.
-/

@[expose] public section

open Real

/-- `π(x)` is the number of primes less than or equal to `x`. -/
noncomputable def pi (x : ℝ) : ℝ :=
  Nat.primeCounting ⌊x⌋₊
