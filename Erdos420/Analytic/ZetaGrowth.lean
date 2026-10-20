module

public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import Mathlib.NumberTheory.LSeries.SumCoeff
public import Mathlib.MeasureTheory.Function.Floor

/-!
# Growth of the Riemann zeta function to the right of zero

Partial summation against `⌊t⌋ = t - {t}` gives
`(s - 1) ζ(s) = s - s (s - 1) ∫_1^∞ {t} t^{-s-1} dt` for `1 < re s`. Both sides
are analytic on `0 < re s`, so the entire function `(s - 1) ζ(s)` is bounded by
`‖s‖ + ‖s‖ ‖s - 1‖ / re s` there.
-/

@[expose] public section

namespace Erdos420

open DirichletCharacter Asymptotics Filter MeasureTheory

open scoped LSeries.notation Topology

/-- The entire function `(s - 1) ζ(s)` grows at most quadratically in `‖s‖` to the
right of zero. -/
theorem norm_LFunctionTrivChar₁_le {s : ℂ} (hs : 0 < s.re) :
    ‖LFunctionTrivChar₁ 1 s‖ ≤ ‖s‖ + ‖s‖ * ‖s - 1‖ / s.re := by
  -- the partial sums of `1` are `⌊t⌋`
  let A : ℝ → ℂ := fun t ↦ ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, (1 : DirichletCharacter ℂ 1) k
  have hA (t : ℝ) : A t = ⌊t⌋₊ := by
    simp [A, MulChar.one_apply (isUnit_of_subsingleton _)]
  -- the fractional part, cut off below one
  let F : ℝ → ℂ := (Set.Ioi (1 : ℝ)).indicator fun t ↦ (t : ℂ) - ⌊t⌋₊
  have hF (t : ℝ) : ‖F t‖ ≤ 1 := by
    by_cases ht : t ∈ Set.Ioi (1 : ℝ)
    · have h₁ := Nat.floor_le (zero_le_one.trans (le_of_lt ht))
      have h₂ := Nat.lt_floor_add_one t
      simp only [F, Set.indicator_of_mem ht]
      rw [show (t : ℂ) - ⌊t⌋₊ = ((t - ⌊t⌋₊ : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
        Real.norm_eq_abs, abs_le]
      constructor <;> linarith
    · simp [F, ht]
  have hFmeas : Measurable F :=
    (Complex.measurable_ofReal.sub
      ((measurable_from_nat (f := fun n : ℕ ↦ (n : ℂ))).comp Nat.measurable_floor)).indicator
      measurableSet_Ioi
  let J : ℂ → ℂ := fun z ↦ ∫ t in Set.Ioi (1 : ℝ), F t * (t : ℂ) ^ (-(z + 1))
  have hJmellin : J = fun z ↦ mellin F (-z) := by
    funext z
    have hint : (fun t : ℝ ↦ (t : ℂ) ^ (-z - 1) • F t) =
        (Set.Ioi (1 : ℝ)).indicator (fun t ↦ F t * (t : ℂ) ^ (-(z + 1))) := by
      funext t
      rw [show -z - 1 = -(z + 1) by ring]
      by_cases ht : t ∈ Set.Ioi (1 : ℝ) <;> simp [F, ht, mul_comm]
    rw [mellin, hint, setIntegral_indicator measurableSet_Ioi, Set.Ioi_inter_Ioi,
      sup_eq_right.mpr zero_le_one]
  let G : ℂ → ℂ := fun z ↦ z - z * (z - 1) * J z
  -- the integral representation holds to the right of one
  have hO : (fun n ↦ ∑ k ∈ Finset.Icc 1 n, ↗(1 : DirichletCharacter ℂ 1) k) =O[atTop]
      fun n ↦ (n : ℝ) ^ (1 : ℝ) :=
    IsBigO.of_bound 1 (Eventually.of_forall fun n ↦ by
      simp [MulChar.one_apply (isUnit_of_subsingleton _)])
  have hL₁ {z : ℂ} (hz : 1 < z.re) : LFunctionTrivChar₁ 1 z = G z := by
    have hz₁ : z ≠ 1 := by
      rintro rfl
      simp at hz
    have hz₀ : z - 1 ≠ 0 := sub_ne_zero.mpr hz₁
    rw [show LFunctionTrivChar₁ 1 z = (z - 1) * LFunctionTrivChar 1 z from
      Function.update_of_ne hz₁ _ _, LFunctionTrivChar, LFunction_eq_LSeries _ hz,
      LSeries_eq_mul_integral _ zero_le_one hz (LSeriesSummable_of_one_lt_re _ hz) hO]
    -- split `⌊t⌋ = t - {t}`
    have hpow : (-z).re < -1 := by simp; linarith
    have hint₁ : IntegrableOn (fun t : ℝ ↦ (t : ℂ) ^ (-z)) (Set.Ioi 1) :=
      integrableOn_Ioi_cpow_of_lt hpow zero_lt_one
    have hint₂ : IntegrableOn (fun t : ℝ ↦ F t * (t : ℂ) ^ (-(z + 1))) (Set.Ioi 1) := by
      have hpow' : (-(z + 1)).re < -1 := by simp; linarith
      refine (integrableOn_Ioi_cpow_of_lt hpow' zero_lt_one).bdd_mul
        (hFmeas.aestronglyMeasurable.restrict) (Eventually.of_forall fun t ↦ hF t) |>.congr ?_
      exact Eventually.of_forall fun t ↦ by simp [mul_comm]
    have hsplit : ∫ t in Set.Ioi (1 : ℝ), A t * (t : ℂ) ^ (-(z + 1)) =
        (∫ t in Set.Ioi (1 : ℝ), (t : ℂ) ^ (-z)) - J z := by
      rw [← integral_sub hint₁ hint₂]
      refine setIntegral_congr_fun measurableSet_Ioi fun t ht ↦ ?_
      have ht₀ : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (zero_lt_one.trans ht).ne'
      simp only [F, Set.indicator_of_mem ht, hA]
      rw [show -(z + 1) = -z - 1 by ring, Complex.cpow_sub _ _ ht₀, Complex.cpow_one]
      field_simp
      ring
    have hI : ∫ t in Set.Ioi (1 : ℝ), (t : ℂ) ^ (-z) = 1 / (z - 1) := by
      rw [integral_Ioi_cpow_of_lt hpow zero_lt_one, Complex.ofReal_one, Complex.one_cpow]
      have : -z + 1 ≠ 0 := by
        intro h
        exact hz₀ (by linear_combination -h)
      field_simp
      ring
    change (z - 1) * (z * ∫ t in Set.Ioi (1 : ℝ), A t * (t : ℂ) ^ (-(z + 1))) = G z
    rw [hsplit, hI]
    simp only [G]
    field_simp
  -- both sides are analytic on the right half-plane
  let U : Set ℂ := {z | 0 < z.re}
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hGdiff : DifferentiableOn ℂ G U := by
    intro z hz
    have hmellin : DifferentiableAt ℂ (mellin F) (-z) := by
      refine mellin_differentiableAt_of_isBigO_rpow (a := 0) (b := -z.re - 1) ?_ ?_
        (by simpa using (show 0 < z.re from hz)) ?_ (by simp)
      · exact ((locallyIntegrable_const (1 : ℂ)).mono hFmeas.aestronglyMeasurable
          (ae_of_all _ fun t ↦ by simpa using hF t)).locallyIntegrableOn _
      · exact IsBigO.of_bound 1 (Eventually.of_forall fun t ↦ by simpa using hF t)
      · refine EventuallyEq.trans_isBigO ?_ (isBigO_zero _ _)
        filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds zero_lt_one)] with t ht
        simp [F, not_lt.mpr (Set.mem_Iio.mp ht).le]
    have hJd : DifferentiableAt ℂ J z := by
      rw [hJmellin]
      exact hmellin.comp z differentiableAt_id.neg
    exact (differentiableAt_id.sub ((differentiableAt_id.mul
      (differentiableAt_id.sub_const 1)).mul hJd)).differentiableWithinAt
  have hEq : Set.EqOn (LFunctionTrivChar₁ 1) G U := by
    have hLan := (differentiable_LFunctionTrivChar₁ 1).differentiableOn.analyticOnNhd hU
    refine hLan.eqOn_of_preconnected_of_eventuallyEq (hGdiff.analyticOnNhd hU)
      (convex_halfSpace_re_gt 0).isPreconnected (z₀ := 2) (by simp [U]) ?_
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show (1 : ℝ) < (2 : ℂ).re by norm_num)] with z hz
    exact hL₁ hz
  -- bound the integral representation
  have hint : ‖J s‖ ≤ 1 / s.re := by
    have hrpow : IntegrableOn (fun t : ℝ ↦ t ^ (-s.re - 1)) (Set.Ioi 1) :=
      integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one
    calc ‖J s‖
      _ ≤ ∫ t in Set.Ioi (1 : ℝ), 1 * t ^ (-s.re - 1) := by
        refine norm_integral_le_of_norm_le (hrpow.const_mul _) ?_
        refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht ↦ ?_
        have ht₀ : 0 < t := zero_lt_one.trans ht
        rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht₀]
        have hre : (-(s + 1)).re = -s.re - 1 := by simp; ring
        rw [hre]
        gcongr
        exact hF t
      _ = 1 / s.re := by
        rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) zero_lt_one,
          show -s.re - 1 + 1 = -s.re by ring, Real.one_rpow]
        field_simp
  calc ‖LFunctionTrivChar₁ 1 s‖
    _ = ‖s - s * (s - 1) * J s‖ := by rw [hEq hs]
    _ ≤ ‖s‖ + ‖s‖ * ‖s - 1‖ * ‖J s‖ := by
      refine (norm_sub_le _ _).trans ?_
      rw [norm_mul, norm_mul]
    _ ≤ ‖s‖ + ‖s‖ * ‖s - 1‖ * (1 / s.re) := by gcongr
    _ = ‖s‖ + ‖s‖ * ‖s - 1‖ / s.re := by ring

end Erdos420
