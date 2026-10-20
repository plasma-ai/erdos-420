module

public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import Mathlib.NumberTheory.Harmonic.ZetaAsymp

/-!
# A lower bound for Dirichlet L-functions to the right of one

For `1 < re s`, the Dirichlet series of `μ χ` inverts `L(s, χ)` and is
bounded by `ζ(re s) ≤ re s / (re s - 1)`.
-/

@[expose] public section

namespace Erdos420

open DirichletCharacter

open scoped ArithmeticFunction.Moebius LSeries.notation

/-- A Dirichlet L-function is bounded below by `(re s - 1) / re s` to the right
of one. -/
theorem le_norm_LFunction {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {s : ℂ}
    (hs : 1 < s.re) : (s.re - 1) / s.re ≤ ‖LFunction χ s‖ := by
  have hσ₀ : 0 < s.re := by linarith
  have hσ₁ : 0 < s.re - 1 := by linarith
  -- the L-series of `μ χ` inverts `L(s, χ)`
  have hmul : LFunction χ s * LSeries (↗χ * ↗μ) s = 1 := by
    rw [LFunction_eq_LSeries χ hs]
    exact LSeries.mul_mu_eq_one χ hs
  have hsum : LSeriesSummable (↗χ * ↗μ) s :=
    LSeriesSummable_mul χ (ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs)
  -- the zeta series `∑ (n + 1) ^ (-σ)` is bounded by `σ / (σ - 1)`
  have hζsum : Summable fun n : ℕ ↦ 1 / ((n : ℝ) + 1) ^ s.re := by
    exact_mod_cast (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_rpow.mpr hs)
  have hζ : ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ s.re ≤ s.re / (s.re - 1) := by
    have h₀ : 0 ≤ ZetaAsymptotics.termTSum s.re :=
      tsum_nonneg fun n ↦ ZetaAsymptotics.term_nonneg (n + 1) s.re
    rw [ZetaAsymptotics.termTSum_of_lt hs] at h₀
    rw [le_div_iff₀ hσ₁]
    have h₁ := mul_le_mul_of_nonneg_left (sub_nonneg.mp h₀) (mul_nonneg hσ₀.le hσ₁.le)
    field_simp at h₁
    linarith
  -- each term of the `μ χ` series is bounded by the corresponding zeta term
  have hterm (n : ℕ) :
      ‖LSeries.term (↗χ * ↗μ) s (n + 1)‖ ≤ 1 / ((n : ℝ) + 1) ^ s.re := by
    simp only [LSeries.norm_term_eq, Nat.add_one_ne_zero, ↓reduceIte, Pi.mul_apply, norm_mul]
    push_cast
    gcongr
    calc ‖χ (n + 1)‖ * ‖(μ (n + 1) : ℂ)‖
      _ ≤ 1 * 1 := by
        gcongr
        · exact χ.norm_le_one _
        · exact_mod_cast ArithmeticFunction.abs_moebius_le_one
      _ = 1 := one_mul 1
  have hM : ‖LSeries (↗χ * ↗μ) s‖ ≤ s.re / (s.re - 1) := by
    have hshift : Summable fun n : ℕ ↦ ‖LSeries.term (↗χ * ↗μ) s (n + 1)‖ :=
      (summable_nat_add_iff 1).mpr hsum.norm
    rw [LSeries, hsum.tsum_eq_zero_add, LSeries.term_zero, zero_add]
    calc ‖∑' n : ℕ, LSeries.term (↗χ * ↗μ) s (n + 1)‖
      _ ≤ ∑' n : ℕ, ‖LSeries.term (↗χ * ↗μ) s (n + 1)‖ :=
        norm_tsum_le_tsum_norm hshift
      _ ≤ ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ s.re := hshift.tsum_le_tsum hterm hζsum
      _ ≤ s.re / (s.re - 1) := hζ
  -- invert the bound
  have hnorm : ‖LFunction χ s‖ * ‖LSeries (↗χ * ↗μ) s‖ = 1 := by
    rw [← norm_mul, hmul, norm_one]
  have hMpos : 0 < ‖LSeries (↗χ * ↗μ) s‖ := by
    refine norm_pos_iff.mpr fun h ↦ ?_
    simp [h] at hmul
  rw [eq_comm, ← div_eq_iff hMpos.ne'] at hnorm
  rw [← hnorm, ← one_div_div]
  exact one_div_le_one_div_of_le hMpos hM

end Erdos420
