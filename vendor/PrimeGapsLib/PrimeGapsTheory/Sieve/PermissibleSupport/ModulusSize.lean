/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsTheory.Foundations.SieveDatum

/-!
# Size consequences of the modulus hypotheses

Eventual bounds, uniform over all moduli `Q` satisfying `ModulusHyp CQ η N Q`, that replace the
size bound `W N ≤ (log log N) ^ 2` of the primorial modulus.

## Main results

* `PrimeGaps.ModulusHyp.eventually_primeFactors_le_rpow`: every prime factor of `Q` is at most
  `N ^ a`.
* `PrimeGaps.ModulusHyp.eventually_one_le_totient_div_mul_log`: `1 ≤ (φ(Q)/Q) · c log N`.
-/

@[expose] public section

open Real Filter

namespace PrimeGaps.ModulusHyp

variable {CQ η : ℝ}

/-- For `a > 0`, eventually every prime factor of every admissible modulus `Q` is at most `N ^ a`,
since it is at most `log N`. -/
theorem eventually_primeFactors_le_rpow {a : ℝ} (ha : 0 < a) :
    ∀ᶠ N : ℝ in atTop, ∀ Q : ℕ, ModulusHyp CQ η N Q → ∀ p ∈ Q.primeFactors, (p : ℝ) ≤ N ^ a := by
  filter_upwards [Real.eventually_log_pow_le_rpow 1 ha] with N hN Q hQ p hp
  exact (hQ.primeFactors_le p hp).trans (by simpa using hN)

/-- For `c > 0`, eventually `1 ≤ (φ(Q)/Q) · (c log N)` for every admissible modulus `Q`, since
`Q / φ(Q) ≤ CQ log log N = o(log N)`. -/
theorem eventually_one_le_totient_div_mul_log {c : ℝ} (hc : 0 < c) :
    ∀ᶠ N : ℝ in atTop, ∀ Q : ℕ, ModulusHyp CQ η N Q →
      1 ≤ (Q.totient : ℝ) / Q * (c * Real.log N) := by
  have hκ : 0 < c / (|CQ| + 1) := by positivity
  filter_upwards [Real.tendsto_log_atTop.eventually (Real.eventually_log_pow_le_const_mul 1 hκ),
    Real.tendsto_log_atTop.eventually (Real.tendsto_log_atTop.eventually_ge_atTop 0)]
    with N hLL hLL0 Q hQ
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast hQ.pos
  have hφ0 := hQ.totient_pos
  rw [pow_one] at hLL
  rw [div_mul_eq_mul_div, le_div_iff₀ hQ0, one_mul]
  calc (Q : ℝ) ≤ CQ * Real.log (Real.log N) * Q.totient := hQ.le_totient
    _ ≤ (|CQ| + 1) * Real.log (Real.log N) * Q.totient := by
        gcongr; linarith [le_abs_self CQ]
    _ ≤ (|CQ| + 1) * (c / (|CQ| + 1) * Real.log N) * Q.totient := by gcongr
    _ = Q.totient * (c * Real.log N) := by field_simp

end PrimeGaps.ModulusHyp
