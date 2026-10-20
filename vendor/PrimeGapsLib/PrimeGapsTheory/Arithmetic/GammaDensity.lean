/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsTheory.Arithmetic.ConvergentSums
public import PrimeGapsTheory.Arithmetic.SingularSeries

import PrimeGapsTheory.Tactic.PaperTag

/-!
# Prime density bounds

Primewise density bounds for the Maynard sieve datum of a modulus `Q`.

## Main definitions

* `SatisfiesH3`: The third density hypothesis for a family of sieve data.

## Main results

* `maynardSieveDatum_γ_prime_div_le_half`: The prime density ratio is at most one half.
* `gammaPrime_satisfiesH3`: The `W`-tricked prime density satisfies the third density hypothesis.
-/

@[expose] public section

open Filter Topology
open scoped BigOperators ArithmeticFunction ArithmeticFunction.Moebius ArithmeticFunction.detotient

namespace PrimeGaps

/-- Per-prime two-sided bound for Maynard's `γ_g`.  Assuming `2 ∣ Q`, for every prime `p` we have `0 ≤ γ_g(p)/p ≤ 1 - A₁ = 1/2`.

Here `γ_g = (maynardSieveDatum Q h2 hQ).γ`.  The lower bound is the `γ_nonneg`
axiom of the sieve datum; the upper bound is the `γ_density` axiom
(`γ(p)/p ≤ 1 - A₁ = 1/2`). -/
@[pg_tag "bg246" "slem_gg_growth"]
theorem maynardSieveDatum_γ_prime_div_le_half
    (Q : ℕ) (h2 : 2 ∣ Q) (hQ : Squarefree Q) (p : ℕ) (hp : p.Prime) :
    0 ≤ (maynardSieveDatum Q h2 hQ).γ p / p ∧
      (maynardSieveDatum Q h2 hQ).γ p / p ≤ 1 - (1 / 2 : ℝ) := by
  refine ⟨div_nonneg ((maynardSieveDatum Q h2 hQ).γ_nonneg p) (Nat.cast_nonneg _), ?_⟩
  simpa using (maynardSieveDatum Q h2 hQ).γ_density p hp

/-- Hypothesis `(H3)`: the per-prime sieve density bound with exceptional modulus `V` and
constant `A_3`. For every prime `p`: `0 <= gamma p`, and `gamma p / p` is bounded by `0` when
`p | V` and by `1 - 1/A_3` otherwise. -/
def SatisfiesH3 (γ : ℕ → ℝ) (V : ℕ) (A₃ : ℝ) : Prop :=
  ∀ p : ℕ, p.Prime → 0 ≤ γ p ∧ γ p / p ≤ (if p ∣ V then 0 else 1 - 1 / A₃)

/-- If `2 ∣ W`, the local density `gamma_g(W, ·)` satisfies hypothesis `(H3)` with exceptional
modulus `W` and constant `A₃ = 2`. -/
@[pg_tag "bg246" "slem_gg_H3"]
theorem gammaPrime_satisfiesH3 (W : ℕ) (h2dvd : 2 ∣ W) :
    SatisfiesH3 (PrimeGaps.S2mSingularSeries.gammaPrime W) W 2 := by
  intro p hp
  simp only [PrimeGaps.S2mSingularSeries.gammaPrime]
  by_cases hpW : p ∣ W
  · simp [hpW]
  · simp only [hpW, if_false]
    have hp3 : 3 ≤ p := by
      have := hp.two_le
      rcases hp.eq_two_or_odd with h2 | hodd
      · exact absurd (h2 ▸ h2dvd) hpW
      · omega
    have hpR : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3
    have hden_pos : (0 : ℝ) < (p : ℝ) ^ 3 - (p : ℝ) ^ 2 - 2 * (p : ℝ) + 1 := by nlinarith
    refine ⟨div_nonneg (by positivity) (by linarith), ?_⟩
    rw [div_div, div_le_iff₀ (by positivity)]
    nlinarith [hden_pos, sq_nonneg ((p : ℝ) - 1), hpR]

/-- If `r` is squarefree and `gcd(r, Q) = 1`, then
`S.gStar(r) = mu(r)^2 / g(r)`, where `S := maynardSieveDatum Q h2 hQ` bundles Maynard's `γ_g`
and modulus `Q` into a `SieveDatum`.

Both sides equal `1/g(r)` since `mu(r)^2 = 1` and `g(r) ≥ 1` for
squarefree `r` coprime to `Q`. -/
@[pg_tag "bg246" "slem_gg_identification"]
theorem maynardSieveDatum_gStar_squarefree_coprime (Q : ℕ) (h2 : 2 ∣ Q) (hQ : Squarefree Q)
    (r : ℕ) (hr : Squarefree r) (hcop : Nat.Coprime r Q) :
    (maynardSieveDatum Q h2 hQ).gStar r = ((μ r : ℤ) : ℝ) ^ 2 / (g r : ℝ) := by
  set S := maynardSieveDatum Q h2 hQ with hSdef
  rw [S.gStar_squarefree_eq_prod r hr]
  have hfac : ∀ p ∈ r.primeFactors, S.gStar p = 1 / ((p : ℝ) - 2) := by
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpW : ¬ p ∣ Q := fun hdvd ↦ hpp.one_lt.ne'
      (Nat.eq_one_of_dvd_one (hcop ▸ Nat.dvd_gcd (Nat.dvd_of_mem_primeFactors hp) hdvd))
    have hγv : S.γ p = (p : ℝ) / ((p : ℝ) - 1) := by
      rw [hSdef, maynardSieveDatum_γ_prime Q h2 hQ p hpp, if_neg hpW]
    have hp3n : (3 : ℕ) ≤ p := by
      have := hpp.two_le
      rcases hpp.eq_two_or_odd with h | h
      · exact absurd (h ▸ h2) hpW
      · omega
    have hpR : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3n
    have h1 : (p : ℝ) - 1 ≠ 0 := by linarith
    have hpne : (p : ℝ) ≠ 0 := by linarith
    rw [S.gStar_prime p hpp, hγv, show (p : ℝ) - (p : ℝ) / ((p : ℝ) - 1) =
        (p : ℝ) * ((p : ℝ) - 2) / ((p : ℝ) - 1) by field_simp; ring,
      div_div_div_cancel_right₀ h1, div_mul_eq_div_div, div_self hpne]
  have hprod : (∏ p ∈ r.primeFactors, (1 / ((p : ℝ) - 2))) = 1 / (g r : ℝ) := by
    rw [Finset.prod_div_distrib, Finset.prod_const_one,
      ArithmeticFunction.detotient_squarefree_eq_prod hr]
    push_cast
    refine congrArg (fun x : ℝ ↦ 1 / x) (Finset.prod_congr rfl fun p hp ↦ ?_)
    rw [Nat.cast_sub (Nat.prime_of_mem_primeFactors hp).two_le]
    norm_num
  rw [Finset.prod_congr rfl hfac, hprod, show ((μ r : ℤ) : ℝ) ^ 2 = 1 from
    mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hr, one_div]

/-- If `r` is squarefree and `gcd(r, Q) ≠ 1`, then `S.gStar(r) = 0`, where
`S := maynardSieveDatum Q h2 hQ`.  A common prime `p ∣ gcd(r,
  Q)` divides `S.V = Q`,
so `S.gStar p = 0` by `SieveDatum.gStar_prime_zero`, and the squarefree product
vanishes at that factor. -/
@[pg_tag "bg246" "slem_gg_identification"]
theorem maynardSieveDatum_gStar_not_coprime (Q : ℕ) (h2 : 2 ∣ Q) (hQ : Squarefree Q)
    (r : ℕ) (hr : Squarefree r) (hcop : ¬ Nat.Coprime r Q) :
    (maynardSieveDatum Q h2 hQ).gStar r = 0 := by
  set S := maynardSieveDatum Q h2 hQ with hSdef
  rw [S.gStar_squarefree_eq_prod r hr]
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (hcop : Nat.gcd r Q ≠ 1)
  refine Finset.prod_eq_zero
    (Nat.mem_primeFactors.mpr ⟨hp, hpd.trans (Nat.gcd_dvd_left r Q), hr.ne_zero⟩) ?_
  exact S.gStar_prime_zero p hp (by rw [hSdef]; exact hpd.trans (Nat.gcd_dvd_right r Q))

end PrimeGaps

end
