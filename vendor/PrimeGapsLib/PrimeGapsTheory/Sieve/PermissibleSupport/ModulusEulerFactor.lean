/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsTheory.Arithmetic.Mertens.DivisorPowerSum
public import PrimeGapsTheory.Sieve.PermissibleSupport.FunctionW
public import PrimeGapsTheory.Sieve.SieveTruncation

/-!
# The Euler-product error at the sieve modulus

At `σ = 1 / log log N`, the residual `P_σ(Q) / (σ² log R)` of the partial summation with an
Euler-product error (`sieveDatum_kfold_partial_sum_rpow`), where `P_σ(Q) = ∑_{d ∣ Q} d^{σ-1}`, is
at most `(φ(Q)/Q) · log log N` for every modulus `Q` with `ModulusHyp CQ η N Q`: every prime factor
of `Q` is at most `log N`, so `P_σ(Q) ≤ (Q/φ(Q))³ ≤ (CQ log log N)³`. These replace the
`τ(W N)` bounds of the primorial modulus, which fail for a general `Q`.

## Main results

* `PrimeGaps.ModulusHyp.one_add_ellV_le`: `1 + ℓ_Q ≤ (1 + |CQ|) log log N`.
* `PrimeGaps.ModulusHyp.eventually_sum_divisors_rpow_div_le`: the residual bound.
* `PrimeGaps.ModulusHyp.exists_euler_regime`: both bounds at `R = N ^ (θ / 2 - δ)`, for all
  large integers `N`.
-/

@[expose] public section

open Real Filter

namespace PrimeGaps.ModulusHyp

variable {CQ η : ℝ}

/-- `1 + ℓ_Q ≤ (1 + |CQ|) log log N` once `log log N ≥ 1`. -/
theorem one_add_ellV_le {N : ℝ} {Q : ℕ} (hQ : ModulusHyp CQ η N Q)
    (hLL : 1 ≤ Real.log (Real.log N)) : 1 + ellV Q ≤ (1 + |CQ|) * Real.log (Real.log N) := by
  have h := hQ.sum_log_div_le
  have hCQ : CQ * Real.log (Real.log N) ≤ |CQ| * Real.log (Real.log N) :=
    mul_le_mul_of_nonneg_right (le_abs_self CQ) (by linarith)
  unfold ellV
  linarith

/-- **The Euler-product residual at the sieve modulus.** For `κ > 0`, eventually
`log log N ≥ 4` and, at `σ = 1 / log log N`, every modulus `Q` with `ModulusHyp CQ η N Q` has
`P_σ(Q) / (σ² κ log N) ≤ (φ(Q)/Q) log log N`, where `P_σ(Q) = ∑_{d ∣ Q} d^{σ-1}`. Since every
prime factor of `Q` is at most `log N`, `P_σ(Q) ≤ (Q/φ(Q))³` (`sum_divisors_rpow_le_cube`), and
`(Q/φ(Q))⁴ log log N ≤ (CQ log log N)⁴ log log N = o(log N)`. -/
theorem eventually_sum_divisors_rpow_div_le {κ : ℝ} (hκ : 0 < κ) :
    ∀ᶠ N : ℝ in atTop, 4 ≤ Real.log (Real.log N) ∧ ∀ Q : ℕ, ModulusHyp CQ η N Q →
      (∑ d ∈ Q.divisors, (d : ℝ) ^ (1 / Real.log (Real.log N) - 1)) /
          ((1 / Real.log (Real.log N)) ^ 2 * (κ * Real.log N)) ≤
        (Q.totient : ℝ) / Q * Real.log (Real.log N) := by
  set c : ℝ := |CQ| + 1 with hc
  have hc1 : 1 ≤ c := by rw [hc]; linarith [abs_nonneg CQ]
  have hkey : ∀ᶠ x : ℝ in atTop, c ^ 4 * Real.log x ^ 5 ≤ κ * x := by
    filter_upwards [Real.eventually_log_pow_le_const_mul 5 (by positivity : 0 < κ / c ^ 4)]
      with x hx
    calc c ^ 4 * Real.log x ^ 5 ≤ c ^ 4 * (κ / c ^ 4 * x) := by gcongr
      _ = κ * x := by field_simp
  filter_upwards [Real.tendsto_log_atTop.eventually hkey,
    Real.tendsto_log_atTop.eventually (Real.tendsto_log_atTop.eventually_ge_atTop 4),
    Real.tendsto_log_atTop.eventually_gt_atTop 1]
    with N hN hLL4 hL1
  refine ⟨hLL4, fun Q hQ ↦ ?_⟩
  set L : ℝ := Real.log N with hL
  set LL : ℝ := Real.log L with hLL
  have hLL0 : 0 < LL := by linarith
  have hQ1 : 1 ≤ Q := hQ.pos
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast hQ.pos
  have hφ0 := hQ.totient_pos
  set a : ℝ := (Q : ℝ) / Q.totient with ha
  have ha0 : 0 < a := by positivity
  have haLL : a ≤ c * LL := by
    rw [ha, div_le_iff₀ hφ0]
    calc (Q : ℝ) ≤ CQ * LL * Q.totient := hQ.le_totient
      _ ≤ c * LL * Q.totient := by gcongr; rw [hc]; linarith [le_abs_self CQ]
  have hP : ∑ d ∈ Q.divisors, (d : ℝ) ^ (1 / LL - 1) ≤ a ^ 3 :=
    sum_divisors_rpow_le_cube Q hQ1 hQ.squarefree hL1 hQ.primeFactors_le
  have ha4 : a ^ 4 * LL ≤ κ * L :=
    calc a ^ 4 * LL ≤ (c * LL) ^ 4 * LL := by gcongr
      _ = c ^ 4 * LL ^ 5 := by ring
      _ ≤ κ * L := hN
  rw [show (Q.totient : ℝ) / Q = a⁻¹ by rw [ha, inv_div],
    div_le_iff₀ (by positivity : (0 : ℝ) < (1 / LL) ^ 2 * (κ * L))]
  calc ∑ d ∈ Q.divisors, (d : ℝ) ^ (1 / LL - 1) ≤ a ^ 3 := hP
    _ = (a ^ 4 * LL) * (a⁻¹ * LL * (1 / LL) ^ 2) := by field_simp
    _ ≤ (κ * L) * (a⁻¹ * LL * (1 / LL) ^ 2) := by gcongr
    _ = a⁻¹ * LL * ((1 / LL) ^ 2 * (κ * L)) := by ring

open scoped PrimeGaps.sieveTruncation in
/-- **The Euler-product regime at the sieve truncation.** For `δ < θ / 2` there is `N₀` such that
for every integer `N ≥ N₀`, `σ = 1 / log log N` lies in `(0, 1/4]`, `log log N ≥ 1`, and every
modulus `Q` with `ModulusHyp CQ η N Q` has `1 + ℓ_Q ≤ (1 + |CQ|) log log N` and
`P_σ(Q) / (σ² log R) ≤ (φ(Q)/Q) log log N`, where `P_σ(Q) = ∑_{d ∣ Q} d^{σ-1}`. -/
theorem exists_euler_regime (δ θ : ℝ) (hδ : δ < θ / 2) (CQ η : ℝ) :
    ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ N → 0 < 1 / Real.log (Real.log N) ∧
      1 / Real.log (Real.log N) ≤ 1 / 4 ∧ 1 ≤ Real.log (Real.log N) ∧
      ∀ Q : ℕ, ModulusHyp CQ η N Q → 1 + ellV Q ≤ (1 + |CQ|) * Real.log (Real.log N) ∧
        (∑ d ∈ Q.divisors, (d : ℝ) ^ (1 / Real.log (Real.log N) - 1)) /
            ((1 / Real.log (Real.log N)) ^ 2 * Real.log R) ≤
          (Q.totient : ℝ) / Q * Real.log (Real.log N) := by
  have hκ : 0 < θ / 2 - δ := by linarith
  obtain ⟨a, ha⟩ := Filter.eventually_atTop.mp
    (eventually_sum_divisors_rpow_div_le (CQ := CQ) (η := η) hκ)
  refine ⟨max a 1, fun N hN ↦ ?_⟩
  obtain ⟨hLL4, hP⟩ := ha N ((le_max_left _ _).trans hN)
  have hN0 : (0 : ℝ) < N := one_pos.trans_le ((le_max_right _ _).trans hN)
  refine ⟨by positivity, by rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith,
    by linarith, fun Q hQ ↦ ⟨hQ.one_add_ellV_le (by linarith), ?_⟩⟩
  rw [PrimeGaps.sieveTruncation, Real.log_rpow hN0]
  exact hP Q hQ

end PrimeGaps.ModulusHyp
