import Erdos420.Analytic.CenterLowerBound
import Erdos420.Analytic.Growth
import Erdos420.Analytic.LineBounds
import Erdos420.Analytic.ZeroFree
import Erdos420.Analytic.ZetaGrowth

/-!
# Admissible L-functions

A nontrivial primitive Dirichlet L-function of modulus `q ≥ 3` is admissible with
conductor `q`, and the entire function `(s - 1) ζ(s)` is admissible with conductor
`3`. Their zeros in `re s > 0` lie in `1/8 ≤ re s ≤ 7/8` by the seven-eighths
theorem and the functional equation. Their growth on the disks centered at
`9/8 + iT` comes from partial summation, relative to the lower bound at the center.
-/

namespace Erdos420

open Complex Metric DirichletCharacter

/-- A point of `closedBall (9/8 + iT) (109/100)` has `re s ≥ 7/200` and `‖s‖ ≤ |T| + 3`. -/
lemma re_and_norm_le_of_mem_closedBall {T : ℝ} {z : ℂ}
    (hz : z ∈ closedBall (9 / 8 + T * I) (109 / 100)) : 7 / 200 ≤ z.re ∧ ‖z‖ ≤ |T| + 3 := by
  have hdist : ‖z - (9 / 8 + T * I)‖ ≤ 109 / 100 := by rwa [mem_closedBall, dist_eq_norm] at hz
  -- the disk stays to the right of `re s = 7/200`
  have hre : 7 / 200 ≤ z.re := by
    have h := abs_le.mp ((abs_re_le_norm _).trans hdist)
    simp only [sub_re, add_re, mul_re, I_re, I_im, ofReal_re, ofReal_im] at h
    norm_num at h
    linarith
  -- and has `‖s‖ ≤ |T| + 3`
  have hc : ‖(9 / 8 + T * I : ℂ)‖ ≤ 9 / 8 + |T| := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_I, mul_one, norm_real, Real.norm_eq_abs]
    norm_num
  refine ⟨hre, ?_⟩
  calc ‖z‖ = ‖z - (9 / 8 + T * I) + (9 / 8 + T * I)‖ := by rw [sub_add_cancel]
    _ ≤ ‖z - (9 / 8 + T * I)‖ + ‖(9 / 8 + T * I : ℂ)‖ := norm_add_le _ _
    _ ≤ |T| + 3 := by linarith

/-- The norm of `L(s, χ)` at the center `9/8 + iT` is at least `1/9`. -/
lemma one_ninth_le_norm_LFunction {r : ℕ} [NeZero r] (χ : DirichletCharacter ℂ r) (T : ℝ) :
    1 / 9 ≤ ‖LFunction χ (9 / 8 + T * I)‖ := by
  have hre : (9 / 8 + T * I).re = 9 / 8 := by simp
  have h := le_norm_LFunction χ (s := 9 / 8 + T * I) (by rw [hre]; norm_num)
  rw [hre] at h
  norm_num at h
  linarith

/-- A nontrivial primitive Dirichlet L-function of modulus `q ≥ 3` is admissible with
conductor `q`. -/
theorem admissible_LFunction {q : ℕ} [NeZero q] (hq : 3 ≤ q) {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (hχ₁ : χ ≠ 1) : Admissible (LFunction χ) q where
  three_le := by exact_mod_cast hq
  differentiable := differentiable_LFunction hχ₁
  re_mem_Icc ρ hρ h₀ := by
    constructor
    · by_contra h
      exact LFunction_ne_zero_of_re_lt_one_eighth hχ h₀ (not_le.mp h) hρ
    · by_contra h
      exact LFunction_ne_zero_of_seven_eighths_lt_re χ (not_le.mp h) (fun h' ↦ hχ₁ h'.1) hρ
  norm_le T z hz := by
    obtain ⟨hre, hnorm⟩ := re_and_norm_le_of_mem_closedBall hz
    have hq' : (3 : ℝ) ≤ q := by exact_mod_cast hq
    set y : ℝ := q * (|T| + 3) with hy
    have hy₉ : 9 ≤ y := by nlinarith [abs_nonneg T]
    have hup : ‖LFunction χ z‖ ≤ y / (7 / 200) := by
      refine (norm_LFunction_le hχ₁ (by linarith)).trans ?_
      rw [hy]
      gcongr
    have hpow : (9 : ℝ) ^ 5 ≤ y ^ 5 := pow_le_pow_left₀ (by norm_num) hy₉ 5
    calc ‖LFunction χ z‖ ≤ y / (7 / 200) := hup
      _ ≤ y ^ 6 * (1 / 9) := by
        rw [show y ^ 6 = y * y ^ 5 by ring]
        nlinarith
      _ ≤ y ^ 6 * ‖LFunction χ (9 / 8 + T * I)‖ := by
        gcongr
        exact one_ninth_le_norm_LFunction χ T

/-- `LFunctionTrivChar₁ 1 s = (s - 1) ζ(s)` away from `s = 1`. -/
lemma LFunctionTrivChar₁_of_ne_one {s : ℂ} (hs : s ≠ 1) :
    LFunctionTrivChar₁ 1 s = (s - 1) * LFunctionTrivChar 1 s :=
  Function.update_of_ne hs _ _

/-- The entire function `(s - 1) ζ(s)` is admissible with conductor `3`. -/
theorem admissible_LFunctionTrivChar₁ : Admissible (LFunctionTrivChar₁ 1) 3 where
  three_le := le_rfl
  differentiable := differentiable_LFunctionTrivChar₁ 1
  re_mem_Icc ρ hρ h₀ := by
    have hρ₁ : ρ ≠ 1 := by
      rintro rfl
      exact LFunctionTrivChar₁_apply_one_ne_zero 1 hρ
    have hζ : LFunctionTrivChar 1 ρ = 0 := by
      rw [LFunctionTrivChar₁_of_ne_one hρ₁] at hρ
      exact (mul_eq_zero.mp hρ).resolve_left (sub_ne_zero.mpr hρ₁)
    constructor
    · by_contra h
      exact LFunction_ne_zero_of_re_lt_one_eighth isPrimitive_one_level_one h₀ (not_le.mp h) hζ
    · by_contra h
      exact LFunction_ne_zero_of_seven_eighths_lt_re _ (not_le.mp h) (fun h' ↦ hρ₁ h'.2) hζ
  norm_le T z hz := by
    obtain ⟨hre, hnorm⟩ := re_and_norm_le_of_mem_closedBall hz
    set y : ℝ := |T| + 3 with hy
    have hy₃ : 3 ≤ y := by linarith [abs_nonneg T]
    have hz₁ : ‖z - 1‖ ≤ 2 * y := (norm_sub_le _ _).trans (by simp; linarith)
    -- the center is bounded below
    have hc₁ : (9 / 8 + T * I : ℂ) ≠ 1 := fun h ↦ by
      have h' := congrArg re h
      norm_num at h'
    have hc : 1 / 72 ≤ ‖LFunctionTrivChar₁ 1 (9 / 8 + T * I)‖ := by
      rw [LFunctionTrivChar₁_of_ne_one hc₁, norm_mul]
      have h₁ : 1 / 8 ≤ ‖(9 / 8 + T * I : ℂ) - 1‖ := by
        refine le_trans ?_ (abs_re_le_norm _)
        norm_num
      have h₂ := one_ninth_le_norm_LFunction (1 : DirichletCharacter ℂ 1) T
      calc (1 / 72 : ℝ) = 1 / 8 * (1 / 9) := by norm_num
        _ ≤ _ := mul_le_mul h₁ h₂ (by norm_num) (norm_nonneg _)
    -- partial summation bounds `(s - 1) ζ(s)` by `59 y²`
    have hup : ‖LFunctionTrivChar₁ 1 z‖ ≤ 59 * y ^ 2 := by
      refine (norm_LFunctionTrivChar₁_le (by linarith)).trans ?_
      have h₁ : ‖z‖ * ‖z - 1‖ / z.re ≤ y * (2 * y) / (7 / 200) := by
        gcongr
      nlinarith
    have hpow : (3 : ℝ) ^ 4 ≤ y ^ 4 := pow_le_pow_left₀ (by norm_num) hy₃ 4
    calc ‖LFunctionTrivChar₁ 1 z‖ ≤ 59 * y ^ 2 := hup
      _ ≤ (3 * y) ^ 6 * (1 / 72) := by
        rw [show (3 * y) ^ 6 = 729 * y ^ 2 * y ^ 4 by ring]
        nlinarith [sq_nonneg y]
      _ ≤ (3 * y) ^ 6 * ‖LFunctionTrivChar₁ 1 (9 / 8 + T * I)‖ := by gcongr

end Erdos420
