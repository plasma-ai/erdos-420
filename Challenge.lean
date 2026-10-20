module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.NumberTheory.Divisors

/-!
# Erdős Problem 420: divisor counts of shifted factorials

Let `τ(n)` count the divisors of `n`, and let
`F(f, n) = τ((n + ⌊f(n)⌋)!) / τ(n!)`. Erdős and Graham asked whether
`F((log n)^C, n) → ∞` for large `C`, whether `F(log n, n)` is dense in
`(1, ∞)`, and more generally whether `F(f, n)` is dense for every monotone
`f(n) ≤ log n` with `f(n) → ∞`.

**Claim.** Let `f` be monotone with `f(n) → ∞` and `f(n) ≤ log n` for all
large `n`. Then for every `N`, the values `F(f, n)` with `n ≥ N` are dense in
`(1, ∞)`. In particular `F(log n, n)` is dense in `(1, ∞)`. This answers the
second and third questions of Erdős Problem 420 in the affirmative. The first
question is not addressed.

The proof rests on the zero-free half-plane `re s > 7/8` for every Dirichlet
L-function, which the Lean proof imports rather than assumes. It is
Theorem 1.1 of OpenAI's manuscript *The Quasi-Riemann Hypothesis*
(30 September 2026).

Thomas F. Bloom catalogs the questions as
[Erdős Problem 420](https://www.erdosproblems.com/420). No formal statement
was available, so `F` and the two theorems below are written here. Density in
`(1, ∞)` is stated as `Set.Ioi 1 ⊆ closure _`; every value of `F` is at
least `1`, since `n!` divides `(n + k)!`.

The two theorems below have deliberate proof holes. `Solution.lean` supplies
their proofs, and Comparator checks them against these statements.
-/

@[expose] public section

open Filter

namespace Erdos420

/-- `F f n = τ((n + ⌊f n⌋)!) / τ(n!)`, where `τ` counts divisors. -/
noncomputable def F (f : ℕ → ℝ) (n : ℕ) : ℝ :=
  ((n + ⌊f n⌋₊).factorial.divisors.card : ℝ) / (n.factorial.divisors.card : ℝ)

/-- If `f` is monotone, tends to infinity, and is eventually at most `log n`,
then for every `N` the values `F f n` with `n ≥ N` are dense in `(1, ∞)`. -/
theorem erdos_420.parts.iii (f : ℕ → ℝ) (hf : Monotone f)
    (hf_top : Tendsto f atTop atTop) (hf_log : ∀ᶠ n in atTop, f n ≤ Real.log n)
    (N : ℕ) : Set.Ioi 1 ⊆ closure (F f '' Set.Ici N) := by
  sorry

/-- `F(log n, n)` is dense in `(1, ∞)`. -/
theorem erdos_420.parts.ii :
    Set.Ioi 1 ⊆ closure (Set.range (F fun n ↦ Real.log n)) := by
  sorry

end Erdos420
