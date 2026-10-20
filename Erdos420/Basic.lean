module

public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Positivity.Basic

/-!
# Prime holes and large-prime ratios

`IsPrimeHole k x` says `x = k p` for a prime `p > k`. Such an `x` raises
`log τ` of a factorial by exactly `log (1 + 1/k)` when it enters the window.

`bigPrimeRatio Y x` is `p / x` for the prime `p ∣ x` with `p² > Y`, if there
is one, and `0` otherwise. It bounds the contribution of `x` to
`log τ((n + h)!) − log τ(n!)` for every window `(n, n + h]` with
`n + h ≥ Y`.

`slabTail k B A H` sums `bigPrimeRatio A x` over the slab `(A − H, A + B]`,
leaving out the prime holes in `(A, A + B]`. It is nonnegative and grows
with `H`.
-/

@[expose] public section

namespace Erdos420

/-- `x = k p` for a prime `p > k`. -/
def IsPrimeHole (k x : ℕ) : Prop := ∃ p, p.Prime ∧ k < p ∧ x = k * p

/-- `∑_{p ∣ x, Y < p²} p / x`, which has at most one term when `x ≤ Y`. -/
noncomputable def bigPrimeRatio (Y x : ℕ) : ℝ :=
  ∑ p ∈ x.primeFactors with Y < p ^ 2, (p : ℝ) / x

open scoped Classical in
/-- The large-prime ratios of the slab `(A − H, A + B]`, leaving out the prime
holes in `(A, A + B]`. -/
noncomputable def slabTail (k B A H : ℕ) : ℝ :=
  ∑ x ∈ (Finset.Ioc (A - H) (A + B)).filter (fun x ↦ ¬ (A < x ∧ IsPrimeHole k x)),
    bigPrimeRatio A x

/-- Large-prime ratios are nonnegative. -/
lemma bigPrimeRatio_nonneg (Y x : ℕ) : 0 ≤ bigPrimeRatio Y x :=
  Finset.sum_nonneg fun _ _ ↦ by positivity

/-- Slab tails are nonnegative. -/
lemma slabTail_nonneg (k B A H : ℕ) : 0 ≤ slabTail k B A H :=
  Finset.sum_nonneg fun _ _ ↦ bigPrimeRatio_nonneg _ _

open scoped Classical in
/-- The slab tail grows with the depth `H` of the slab. -/
lemma slabTail_mono (k B A : ℕ) {H H' : ℕ} (hH : H ≤ H') :
    slabTail k B A H ≤ slabTail k B A H' :=
  Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.filter_subset_filter _ (Finset.Ioc_subset_Ioc (by omega) le_rfl))
    fun _ _ _ ↦ bigPrimeRatio_nonneg _ _

end Erdos420
