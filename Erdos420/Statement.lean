module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.NumberTheory.Divisors

/-!
# Statement of Erdős Problem 420: divisor counts of shifted factorials

The definitions here repeat those of `Challenge.lean` for the proof
development; Comparator requires them to agree exactly.
-/

@[expose] public section

namespace Erdos420

/-- `F f n = τ((n + ⌊f n⌋)!) / τ(n!)`, where `τ` counts divisors. -/
noncomputable def F (f : ℕ → ℝ) (n : ℕ) : ℝ :=
  ((n + ⌊f n⌋₊).factorial.divisors.card : ℝ) / (n.factorial.divisors.card : ℝ)

end Erdos420
