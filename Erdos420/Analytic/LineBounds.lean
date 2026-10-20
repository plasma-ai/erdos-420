module

public import Erdos420.Analytic.LocalFormula
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.PSeries

/-!
# Zeros and logarithmic derivatives of L-functions

An entire function `f` is *admissible* with conductor `Q ≥ 3` if its zeros in
`re s > 0` lie in the strip `1/8 ≤ re s ≤ 7/8` and it grows at most like
`(Q (|T| + 3))⁶` on the disks of radius `109/100` centered at `9/8 + iT`, relative
to its value at the center. Primitive Dirichlet L-functions and `(s - 1) ζ(s)`
are admissible.

* Jensen's formula bounds the zeros in `closedBall (9/8 + iT) (43/40)` by
  `O(log (Q (|T| + 3)))`.
* On the line `re s = 1/16` every zero is at distance at least `1/16`, so
  `f'/f = O(log (Q (|t| + 3)))` there.
* Some height `T` in each interval `[T₀, T₀ + 1]` keeps the zeros away from the
  horizontal lines `im s = ±T`, so `f'/f = O(log² (Q (T + 3)))` on them.
* The zeros in the rectangle `[1/16, 2] × [-T, T]`, weighted by
  `(1 + |im ρ|)⁻²`, have total mass `O(log Q)`.
-/

@[expose] public section

namespace Erdos420

open Complex Metric MeromorphicOn

/-- An entire function with the zeros and growth of an L-function of conductor `Q`. -/
structure Admissible (f : ℂ → ℂ) (Q : ℝ) : Prop where
  three_le : 3 ≤ Q
  differentiable : Differentiable ℂ f
  re_mem_Icc : ∀ ρ : ℂ, f ρ = 0 → 0 < ρ.re → ρ.re ∈ Set.Icc (1 / 8 : ℝ) (7 / 8)
  norm_le : ∀ T : ℝ, ∀ z ∈ closedBall (9 / 8 + T * I) (109 / 100),
    ‖f z‖ ≤ (Q * (|T| + 3)) ^ 6 * ‖f (9 / 8 + T * I)‖

/-! ### Zeros of admissible functions -/

namespace Admissible

variable {f : ℂ → ℂ} {Q : ℝ}

/-- An admissible function is analytic on every set. -/
lemma analyticOnNhd (hf : Admissible f Q) (U : Set ℂ) : AnalyticOnNhd ℂ f U :=
  fun z _ ↦ hf.differentiable.analyticAt z

/-- An admissible function does not vanish to the right of `7/8`. -/
lemma ne_zero_of_seven_eighths_lt_re (hf : Admissible f Q) {s : ℂ} (hs : 7 / 8 < s.re) :
    f s ≠ 0 :=
  fun h ↦ by linarith [(hf.re_mem_Icc s h (by linarith)).2]

/-- The divisor of an admissible function is nonnegative. -/
lemma divisor_nonneg (hf : Admissible f Q) (U : Set ℂ) (z : ℂ) : 0 ≤ divisor f U z :=
  (hf.analyticOnNhd U).divisor_nonneg z

/-- A point where the divisor of `f` on `U` is nonzero is a zero of `f` in `U`. -/
lemma mem_and_eq_zero_of_divisor_ne_zero (hf : Admissible f Q) {U : Set ℂ} {z : ℂ}
    (h : divisor f U z ≠ 0) : z ∈ U ∧ f z = 0 := by
  have hz : z ∈ U := (divisor f U).supportWithinDomain h
  refine ⟨hz, apply_eq_zero_of_analyticOrderAt_ne_zero fun h₀ ↦ h ?_⟩
  rw [(hf.analyticOnNhd U).divisor_apply hz, h₀]
  rfl

/-- The divisor of `f` at a point does not depend on the domain. -/
lemma divisor_eq (hf : Admissible f Q) {U V : Set ℂ} {z : ℂ} (hU : z ∈ U) (hV : z ∈ V) :
    divisor f U z = divisor f V z := by
  rw [(hf.analyticOnNhd U).divisor_apply hU, (hf.analyticOnNhd V).divisor_apply hV]

/-- The divisor of `f` on `U` is nonzero at each zero in `U`. -/
lemma divisor_ne_zero_of_eq_zero (hf : Admissible f Q) {U : Set ℂ} {z : ℂ} (hz : z ∈ U)
    (h : f z = 0) : divisor f U z ≠ 0 := by
  have hA := hf.analyticOnNhd Set.univ
  -- `f` does not vanish at `2`, so its order is finite everywhere
  have h₂ : f 2 ≠ 0 := hf.ne_zero_of_seven_eighths_lt_re (by norm_num)
  have htop : analyticOrderAt f z ≠ ⊤ := by
    refine hA.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ (Set.mem_univ 2)
      (Set.mem_univ z) ?_
    rw [((hA 2 trivial).analyticOrderAt_eq_zero).mpr h₂]
    exact ENat.zero_ne_top
  have h₀ : analyticOrderAt f z ≠ 0 := (hA z trivial).analyticOrderAt_ne_zero.mpr h
  rw [(hf.analyticOnNhd U).divisor_apply hz]
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp htop
  rw [← hn] at h₀ ⊢
  simpa using h₀

/-- An admissible function does not vanish at the center `9/8 + iT`. -/
lemma center_ne_zero (hf : Admissible f Q) (T : ℝ) : f (9 / 8 + T * I) ≠ 0 :=
  hf.ne_zero_of_seven_eighths_lt_re (by simp; norm_num)

end Admissible

/-! ### Bounds on the disks -/

/-- For `Q ≥ 3`, `1 ≤ log (Q (|T| + 3))`. -/
lemma one_le_log_mul {Q : ℝ} (hQ : 3 ≤ Q) (T : ℝ) : 1 ≤ Real.log (Q * (|T| + 3)) := by
  have h₉ : 9 ≤ Q * (|T| + 3) := by nlinarith [abs_nonneg T]
  rw [Real.le_log_iff_exp_le (by linarith)]
  linarith [Real.exp_one_lt_three]

/-- `log ((Q (|T| + 3))⁶) = 6 log (Q (|T| + 3))`. -/
lemma log_pow_six (Q T : ℝ) :
    Real.log ((Q * (|T| + 3)) ^ 6) = 6 * Real.log (Q * (|T| + 3)) := by
  rw [Real.log_pow]
  norm_num

/-- A point of the strip `1/8 ≤ re s ≤ 7/8` within `1/4` of height `h` lies in
`closedBall (9/8 + ih) (43/40)`. -/
lemma mem_closedBall_of_re_mem_Icc {ρ : ℂ} {h : ℝ} (hρ : ρ.re ∈ Set.Icc (1 / 8 : ℝ) (7 / 8))
    (hh : |ρ.im - h| ≤ 1 / 4) : ρ ∈ closedBall (9 / 8 + h * I) (43 / 40) := by
  rw [mem_closedBall, dist_eq_norm]
  have h₂ : ‖ρ - (9 / 8 + h * I)‖ ^ 2 ≤ (43 / 40) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [sub_re, add_re, mul_re, I_re, I_im, ofReal_re, ofReal_im, sub_im, add_im, mul_im]
    norm_num
    have := abs_le.mp hh
    nlinarith [hρ.1, hρ.2]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by norm_num) two_ne_zero).mp h₂

/-- A point of `closedBall (9/8 + ih) (43/40)` has `re > 0` and is within `43/40` of height
`h`. -/
lemma re_pos_of_mem_closedBall {ρ : ℂ} {h : ℝ} (hρ : ρ ∈ closedBall (9 / 8 + h * I) (43 / 40)) :
    0 < ρ.re ∧ |ρ.im - h| ≤ 43 / 40 := by
  rw [mem_closedBall, dist_eq_norm] at hρ
  have hre := abs_le.mp ((abs_re_le_norm _).trans hρ)
  have him := (abs_im_le_norm _).trans hρ
  simp only [sub_re, add_re, mul_re, I_re, I_im, ofReal_re, ofReal_im, sub_im, add_im,
    mul_im] at hre him
  norm_num at hre him
  exact ⟨by linarith, him⟩

/-! ### Weights on the rectangle -/

/-- For `Q ≥ 3`, `1 ≤ log Q`. -/
lemma one_le_log_of_three_le {Q : ℝ} (hQ : 3 ≤ Q) : 1 ≤ Real.log Q := by
  rw [Real.le_log_iff_exp_le (by linarith)]
  linarith [Real.exp_one_lt_three]

/-- For `Q ≥ 3` and `a ≥ 1`, `log (Q a) ≤ log Q (1 + log a)`. -/
lemma log_mul_le_log_mul {Q : ℝ} (hQ : 3 ≤ Q) {a : ℝ} (ha : 1 ≤ a) :
    Real.log (Q * a) ≤ Real.log Q * (1 + Real.log a) := by
  have h₁ := one_le_log_of_three_le hQ
  have h₂ := Real.log_nonneg ha
  rw [Real.log_mul (by positivity) (by positivity)]
  nlinarith

/-- For `y > 0`, `(1 + log (y + 3)) / (7/8 + y)² ≤ 36 / y ^ (3/2)`. -/
lemma weight_le_rpow {y : ℝ} (hy : 0 < y) :
    (1 + Real.log (y + 3)) / (7 / 8 + y) ^ 2 ≤ 36 * (1 / y ^ (3 / 2 : ℝ)) := by
  -- `log (y + 3) ≤ 2 √(y + 3)`
  have hlog : Real.log (y + 3) ≤ 2 * √(y + 3) := by
    have h := Real.log_le_rpow_div (x := y + 3) (by linarith) (ε := 1 / 2) (by norm_num)
    rw [← Real.sqrt_eq_rpow] at h
    linarith
  have h₁ : 1 ≤ √(y + 3) := Real.one_le_sqrt.mpr (by linarith)
  have hsq : √(y + 3) * √(y + 3) = y + 3 := Real.mul_self_sqrt (by linarith)
  have hy₃ : √y ≤ √(y + 3) := Real.sqrt_le_sqrt (by linarith)
  have hpow : y ^ (3 / 2 : ℝ) = y * √y := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hy, Real.rpow_one,
      ← Real.sqrt_eq_rpow]
  rw [hpow, mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
  calc (1 + Real.log (y + 3)) * (y * √y) ≤ (3 * √(y + 3)) * (y * √(y + 3)) :=
        mul_le_mul (by linarith) (mul_le_mul_of_nonneg_left hy₃ hy.le) (by positivity)
          (by positivity)
    _ = 3 * y * (√(y + 3) * √(y + 3)) := by ring
    _ = 3 * y * (y + 3) := by rw [hsq]
    _ ≤ 36 * (7 / 8 + y) ^ 2 := by nlinarith

/-- The weights `(1 + log (|h| + 3)) / (7/8 + |h|)²` at the heights `h = (k + 1/2)/4` are
summable over `k ∈ ℤ`. -/
lemma summable_weight :
    Summable fun k : ℤ ↦ (1 + Real.log (|((k : ℝ) + 1 / 2) / 4| + 3)) /
      (7 / 8 + |((k : ℝ) + 1 / 2) / 4|) ^ 2 := by
  have hpos : ∀ k : ℤ, 0 < |(k : ℝ) + 1 / 2| := fun k ↦ by
    have h : (k : ℝ) + 1 / 2 = ((2 * k + 1 : ℤ) : ℝ) / 2 := by
      push_cast
      ring
    rw [h]
    exact abs_pos.mpr (div_ne_zero (Int.cast_ne_zero.mpr (by omega)) two_ne_zero)
  have hsum : Summable fun k : ℤ ↦
      36 * ((4 : ℝ) ^ (3 / 2 : ℝ) * (1 / |(k : ℝ) + 1 / 2| ^ (3 / 2 : ℝ))) :=
    (((Real.summable_one_div_int_add_rpow (1 / 2) (3 / 2)).mpr (by norm_num)).mul_left _).mul_left _
  refine Summable.of_nonneg_of_le (fun k ↦ ?_) (fun k ↦ ?_) hsum
  · have h := Real.log_nonneg (show (1 : ℝ) ≤ |((k : ℝ) + 1 / 2) / 4| + 3 by
      linarith [abs_nonneg (((k : ℝ) + 1 / 2) / 4)])
    positivity
  · rw [abs_div, abs_of_pos (four_pos : (0 : ℝ) < 4)]
    refine (weight_le_rpow (div_pos (hpos k) four_pos)).trans (le_of_eq ?_)
    rw [Real.div_rpow (abs_nonneg _) (by norm_num)]
    field_simp

/-! ### Sums over divisors -/

/-- If a nonnegative `D : ℂ → ℤ` with finite support is supported at distance at least `δ`
from `z`, then `‖∑ᶠ ρ, D ρ / (z - ρ)‖ ≤ (∑ᶠ ρ, D ρ) / δ`. -/
lemma norm_finsum_div_sub_le {D : ℂ → ℤ} (hD : D.support.Finite) (hD₀ : ∀ ρ, 0 ≤ D ρ)
    {z : ℂ} {δ : ℝ} (hδ : 0 < δ) (hz : ∀ ρ, D ρ ≠ 0 → δ ≤ ‖z - ρ‖) :
    ‖∑ᶠ ρ, (D ρ : ℂ) / (z - ρ)‖ ≤ ((∑ᶠ ρ, D ρ : ℤ) : ℝ) / δ := by
  have hsub : (Function.support fun ρ ↦ (D ρ : ℂ) / (z - ρ)) ⊆ hD.toFinset := by
    intro ρ hρ
    rw [Set.Finite.coe_toFinset, Function.mem_support]
    intro h
    exact hρ (by simp [h])
  rw [finsum_eq_sum_of_support_subset _ hsub,
    finsum_eq_sum_of_support_subset D hD.coe_toFinset.ge, Int.cast_sum, Finset.sum_div]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun ρ hρ ↦ ?_)
  have hρ' : D ρ ≠ 0 := by simpa using hρ
  have hD₀' : (0 : ℝ) ≤ D ρ := by exact_mod_cast hD₀ ρ
  rw [norm_div, Complex.norm_intCast, abs_of_nonneg hD₀']
  exact div_le_div_of_nonneg_left hD₀' hδ (hz ρ hρ')

/-- A nonnegative `D : ℂ → ℤ` with finite support has at least as much total mass as any
sub-sum. -/
lemma sum_le_finsum_of_nonneg {D : ℂ → ℤ} (hD : D.support.Finite) (hD₀ : ∀ ρ, 0 ≤ D ρ)
    (s : Finset ℂ) : ∑ ρ ∈ s, (D ρ : ℝ) ≤ ((∑ᶠ ρ, D ρ : ℤ) : ℝ) := by
  rw [finsum_eq_sum_of_support_subset D (s := s ∪ hD.toFinset) (by simp), Int.cast_sum]
  exact Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
    fun ρ _ _ ↦ by exact_mod_cast hD₀ ρ

/-- The support of a nonnegative `D : ℂ → ℤ` with finite support has at most `∑ᶠ D` points. -/
lemma card_le_finsum_of_nonneg {D : ℂ → ℤ} (hD : D.support.Finite) (hD₀ : ∀ ρ, 0 ≤ D ρ) :
    (hD.toFinset.card : ℝ) ≤ ((∑ᶠ ρ, D ρ : ℤ) : ℝ) := by
  refine le_trans ?_ (sum_le_finsum_of_nonneg hD hD₀ hD.toFinset)
  rw [Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
  refine Finset.sum_le_sum fun ρ hρ ↦ ?_
  have hρ' : D ρ ≠ 0 := by simpa using hρ
  have : 1 ≤ D ρ := by have := hD₀ ρ; omega
  exact_mod_cast this

/-- The zeros of `f` near `9/8 + iT` number `O(log (Q (|T| + 3)))`. -/
theorem exists_sum_divisor_closedBall_le :
    ∃ A : ℝ, ∀ {f : ℂ → ℂ} {Q : ℝ}, Admissible f Q → ∀ T : ℝ,
      ((∑ᶠ ρ, divisor f (closedBall (9 / 8 + T * I) (43 / 40)) ρ : ℤ) : ℝ) ≤
        A * Real.log (Q * (|T| + 3)) := by
  have hq : 0 < Real.log ((109 / 100) / (43 / 40) : ℝ) := Real.log_pos (by norm_num)
  refine ⟨6 / Real.log ((109 / 100) / (43 / 40)), fun {f Q} hf T ↦ ?_⟩
  have hc₀ := hf.center_ne_zero T
  -- the bound on the outer circle is at least one
  have hM : 1 ≤ (Q * (|T| + 3)) ^ 6 :=
    one_le_pow₀ (by nlinarith [abs_nonneg T, hf.three_le])
  have h₁ : |(43 / 40 : ℝ)| = 43 / 40 := abs_of_pos (by norm_num)
  have h₂ : |(109 / 100 : ℝ)| = 109 / 100 := abs_of_pos (by norm_num)
  -- Jensen's inequality for `f / f (9/8 + iT)`
  have hF : AnalyticOnNhd ℂ ((f (9 / 8 + T * I))⁻¹ • f)
      (closedBall (9 / 8 + T * I) |109 / 100|) := (hf.analyticOnNhd _).const_smul
  have hJ := hF.sum_divisor_le (r := 43 / 40) (by norm_num) (by rw [h₁, h₂]; norm_num) hM
    (by simp [hc₀]) fun z hz ↦ ?_
  · rw [h₁, divisor_const_smul (inv_ne_zero hc₀), Pi.smul_apply, smul_eq_mul,
      inv_mul_cancel₀ hc₀, norm_one, div_one] at hJ
    calc _ ≤ Real.log ((Q * (|T| + 3)) ^ 6) / Real.log ((109 / 100) / (43 / 40)) := hJ
      _ = _ := by rw [log_pow_six]; ring
  · rw [h₂] at hz
    rw [Pi.smul_apply, smul_eq_mul, norm_mul, norm_inv, inv_mul_le_iff₀ (norm_pos_iff.mpr hc₀),
      mul_comm]
    exact hf.norm_le T z (sphere_subset_closedBall hz)

/-- On the line `re s = 1/16`, `f'/f = O(log (Q (|t| + 3)))`. -/
theorem exists_norm_logDeriv_le_of_re_eq :
    ∃ K : ℝ, ∀ {f : ℂ → ℂ} {Q : ℝ}, Admissible f Q → ∀ t : ℝ,
      ‖deriv f (1 / 16 + t * I) / f (1 / 16 + t * I)‖ ≤ K * Real.log (Q * (|t| + 3)) := by
  obtain ⟨A, hA⟩ := exists_sum_divisor_closedBall_le
  obtain ⟨K₀, hK₀, hL⟩ := exists_norm_logDeriv_sub_sum_le (r₁ := 17 / 16) (r₂ := 43 / 40)
    (R := 109 / 100) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨16 * A + 6 * K₀, fun {f Q} hf t ↦ ?_⟩
  set D := divisor f (closedBall (9 / 8 + t * I) (43 / 40))
  have hc₀ := hf.center_ne_zero t
  have hM : 1 ≤ (Q * (|t| + 3)) ^ 6 :=
    one_le_pow₀ (by nlinarith [abs_nonneg t, hf.three_le])
  -- the point `1/16 + it` is on the circle of radius `17/16` and is not a zero
  have hz : (1 / 16 + t * I : ℂ) ∈ closedBall (9 / 8 + t * I) (17 / 16) := by
    rw [mem_closedBall, dist_eq_norm, show (1 / 16 + t * I : ℂ) - (9 / 8 + t * I) = -(17 / 16) by
      ring]
    norm_num
  have hz₀ : f (1 / 16 + t * I) ≠ 0 := fun h ↦ by
    have h' := (hf.re_mem_Icc _ h (by simp)).1
    norm_num at h'
  have hloc := hL f _ _ (hf.analyticOnNhd _) hc₀ hM (fun w hw ↦ hf.norm_le t w hw) _ hz hz₀
  -- every zero in the disk has `re ρ ≥ 1/8`, so it is at distance at least `1/16`
  have hsum : ‖∑ᶠ ρ, (D ρ : ℂ) / (1 / 16 + t * I - ρ)‖ ≤ ((∑ᶠ ρ, D ρ : ℤ) : ℝ) / (1 / 16) := by
    refine norm_finsum_div_sub_le (D.finiteSupport (isCompact_closedBall _ _))
      (hf.divisor_nonneg _) (by norm_num) fun ρ hρ ↦ ?_
    obtain ⟨hmem, hzero⟩ := hf.mem_and_eq_zero_of_divisor_ne_zero hρ
    have hre := hf.re_mem_Icc ρ hzero (re_pos_of_mem_closedBall hmem).1
    refine le_trans ?_ (abs_re_le_norm _)
    simp only [sub_re, add_re, mul_re, I_re, I_im, ofReal_re, ofReal_im]
    norm_num
    exact le_abs.mpr (Or.inr (by linarith [hre.1]))
  have hlog : K₀ * Real.log ((Q * (|t| + 3)) ^ 6) = 6 * K₀ * Real.log (Q * (|t| + 3)) := by
    rw [log_pow_six]
    ring
  have hD := hA hf t
  calc _ = ‖(deriv f (1 / 16 + t * I) / f (1 / 16 + t * I) -
          ∑ᶠ ρ, (D ρ : ℂ) / (1 / 16 + t * I - ρ)) + ∑ᶠ ρ, (D ρ : ℂ) / (1 / 16 + t * I - ρ)‖ := by
        rw [sub_add_cancel]
    _ ≤ K₀ * Real.log ((Q * (|t| + 3)) ^ 6) + ((∑ᶠ ρ, D ρ : ℤ) : ℝ) / (1 / 16) :=
        (norm_add_le _ _).trans (add_le_add hloc hsum)
    _ ≤ _ := by linarith

/-- Every interval `[T₀, T₀ + 1]` contains a height `T` such that `f` has
no zeros on the segments `[1/16, 2] × {±T}` and `f'/f = O(log² (Q (T + 3)))`
there. -/
theorem exists_good_height :
    ∃ K : ℝ, ∀ {f : ℂ → ℂ} {Q : ℝ}, Admissible f Q →
      ∀ T₀ : ℝ, 1 ≤ T₀ → ∃ T ∈ Set.Icc T₀ (T₀ + 1), ∀ σ ∈ Set.Icc (1 / 16 : ℝ) 2,
        ∀ τ ∈ ({T, -T} : Set ℝ), f (σ + τ * I) ≠ 0 ∧
          ‖deriv f (σ + τ * I) / f (σ + τ * I)‖ ≤ K * Real.log (Q * (T + 3)) ^ 2 := by
  obtain ⟨A, hA⟩ := exists_sum_divisor_closedBall_le
  obtain ⟨K₀, hK₀, hL⟩ := exists_norm_logDeriv_sub_sum_le (r₁ := 17 / 16) (r₂ := 43 / 40)
    (R := 109 / 100) (by norm_num) (by norm_num) (by norm_num)
  set A' := max A 0
  have hA' : 0 ≤ A' := le_max_right A 0
  refine ⟨112 * A' ^ 2 + 4 * A' + 6 * K₀, fun {f Q} hf T₀ hT₀ ↦ ?_⟩
  have hQ := hf.three_le
  have hfinB : ∀ h : ℝ,
      (divisor f (closedBall (9 / 8 + h * I) (43 / 40))).support.Finite :=
    fun h ↦ (divisor _ _).finiteSupport (isCompact_closedBall _ _)
  -- the windows centered at `±(T₀ - 1 + k/2)` for `k < 7` cover the zeros near `±[T₀, T₀ + 1]`
  set H : Finset ℝ := (Finset.range 7 ×ˢ ({1, -1} : Finset ℝ)).image
    fun p ↦ p.2 * (T₀ - 1 + (p.1 : ℝ) / 2)
  set Z : Finset ℂ := H.biUnion fun h ↦ (hfinB h).toFinset
  set ℓ₀ := Real.log (Q * (T₀ + 3))
  -- the windows hold `O(log (Q T₀))` zeros
  have hZ : (Z.card : ℝ) ≤ 28 * A' * ℓ₀ := by
    have hH : H.card ≤ 14 := by
      refine Finset.card_image_le.trans ?_
      rw [Finset.card_product, Finset.card_range]
      have := Finset.card_le_two (a := (1 : ℝ)) (b := -1)
      omega
    have hwin : ∀ h ∈ H, ((hfinB h).toFinset.card : ℝ) ≤ 2 * A' * ℓ₀ := by
      intro h hh
      obtain ⟨⟨k, ε⟩, hp, rfl⟩ := Finset.mem_image.mp hh
      rw [Finset.mem_product, Finset.mem_range] at hp
      dsimp only at hp
      have hk : (k : ℝ) ≤ 6 := by exact_mod_cast Nat.lt_succ_iff.mp hp.1
      have habs : |ε * (T₀ - 1 + (k : ℝ) / 2)| ≤ T₀ + 2 := by
        have hε : |ε| = 1 := by
          rcases Finset.mem_insert.mp hp.2 with h | h
          · simp [h]
          · simp [Finset.mem_singleton.mp h]
        rw [abs_mul, hε, one_mul, abs_of_nonneg (by positivity)]
        linarith
      have hlog : Real.log (Q * (|ε * (T₀ - 1 + (k : ℝ) / 2)| + 3)) ≤ 2 * ℓ₀ := by
        have h₁ : (12 : ℝ) ≤ Q * (T₀ + 3) := by nlinarith
        rw [show 2 * ℓ₀ = Real.log ((Q * (T₀ + 3)) ^ 2) by rw [Real.log_pow]; norm_num [ℓ₀]]
        refine Real.log_le_log (by positivity) ?_
        nlinarith [abs_nonneg (ε * (T₀ - 1 + (k : ℝ) / 2))]
      have hlog₀ : 0 ≤ Real.log (Q * (|ε * (T₀ - 1 + (k : ℝ) / 2)| + 3)) :=
        le_trans (by norm_num) (one_le_log_mul hQ _)
      calc _ ≤ _ := card_le_finsum_of_nonneg _ (hf.divisor_nonneg _)
        _ ≤ A * Real.log (Q * (|ε * (T₀ - 1 + (k : ℝ) / 2)| + 3)) := hA hf _
        _ ≤ A' * Real.log (Q * (|ε * (T₀ - 1 + (k : ℝ) / 2)| + 3)) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hlog₀
        _ ≤ A' * (2 * ℓ₀) := mul_le_mul_of_nonneg_left hlog hA'
        _ = 2 * A' * ℓ₀ := by ring
    have hℓ₀ : 0 ≤ ℓ₀ := Real.log_nonneg (by nlinarith)
    calc (Z.card : ℝ) ≤ ∑ h ∈ H, ((hfinB h).toFinset.card : ℝ) := by
          exact_mod_cast Finset.card_biUnion_le
      _ ≤ H.card • (2 * A' * ℓ₀) := Finset.sum_le_card_nsmul _ _ _ hwin
      _ ≤ 14 * (2 * A' * ℓ₀) := by
          rw [nsmul_eq_mul]
          gcongr
          exact_mod_cast hH
      _ = 28 * A' * ℓ₀ := by ring
  -- some height `T` stays `δ` away from the heights `|im ρ|` of these zeros
  set δ : ℝ := 1 / (4 * Z.card + 4) with hδ
  have hδ₀ : 0 < δ := by positivity
  have hgood : ∃ T ∈ Set.Icc T₀ (T₀ + 1), ∀ ρ ∈ Z, δ ≤ |T - (|ρ.im|)| := by
    by_contra hcon
    push Not at hcon
    have hsub : Set.Icc T₀ (T₀ + 1) ⊆ ⋃ ρ ∈ Z, Set.Ioo (|ρ.im| - δ) (|ρ.im| + δ) := by
      intro T hT
      obtain ⟨ρ, hρ, hlt⟩ := hcon T hT
      have := abs_lt.mp hlt
      exact Set.mem_biUnion hρ ⟨by linarith, by linarith⟩
    have hvol : ∀ ρ ∈ Z, MeasureTheory.volume (Set.Ioo (|ρ.im| - δ) (|ρ.im| + δ)) =
        ENNReal.ofReal (2 * δ) := fun ρ _ ↦ by
      rw [Real.volume_Ioo]
      ring_nf
    have h := (MeasureTheory.measure_mono (μ := MeasureTheory.volume) hsub).trans
      (MeasureTheory.measure_biUnion_finset_le Z _)
    rw [Real.volume_Icc, Finset.sum_congr rfl hvol, Finset.sum_const, nsmul_eq_mul,
      ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_le_ofReal_iff (by positivity)] at h
    have hlt : (Z.card : ℝ) * (2 * δ) < 1 := by
      rw [hδ, mul_one_div, mul_div_assoc', div_lt_one (by positivity)]
      linarith
    linarith
  obtain ⟨T, hT, hfar⟩ := hgood
  -- every zero near the height `εT` lies in one of the windows
  have hmemZ : ∀ ε ∈ ({1, -1} : Finset ℝ), ∀ ρ : ℂ, f ρ = 0 → 0 < ρ.re →
      |ρ.im - ε * T| ≤ 43 / 40 → ρ ∈ Z := by
    intro ε hε ρ hρ hre him
    have hε₁ : ε * ε = 1 ∧ |ε| = 1 := by
      rcases Finset.mem_insert.mp hε with h | h
      · simp [h]
      · simp [Finset.mem_singleton.mp h]
    -- the height of `ρ` relative to `T₀`, up to sign
    set u := ε * ρ.im
    have hεu : ∀ x : ℝ, |ρ.im - ε * x| = |u - x| := fun x ↦ by
      rw [show u - x = ε * (ρ.im - ε * x) by linear_combination x * hε₁.1, abs_mul, hε₁.2,
        one_mul]
    have hu := abs_le.mp ((hεu T).symm ▸ him)
    set k := ⌊2 * (u - T₀ + 1) + 1 / 2⌋₊
    have hk₁ := Nat.floor_le (show 0 ≤ 2 * (u - T₀ + 1) + 1 / 2 by linarith [hT.1])
    have hk₂ := Nat.lt_floor_add_one (2 * (u - T₀ + 1) + 1 / 2)
    have hk₇ : k < 7 := by
      have h : (k : ℝ) < 7 := by linarith [hT.2]
      exact_mod_cast h
    have hH : ε * (T₀ - 1 + (k : ℝ) / 2) ∈ H :=
      Finset.mem_image.mpr ⟨(k, ε), Finset.mem_product.mpr ⟨Finset.mem_range.mpr hk₇, hε⟩, rfl⟩
    have hwin : |ρ.im - ε * (T₀ - 1 + (k : ℝ) / 2)| ≤ 1 / 4 := by
      rw [hεu]
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    have hball := mem_closedBall_of_re_mem_Icc (hf.re_mem_Icc ρ hρ hre) hwin
    exact Finset.mem_biUnion.mpr ⟨_, hH, (Set.Finite.mem_toFinset _).mpr
      (hf.divisor_ne_zero_of_eq_zero hball hρ)⟩
  refine ⟨T, hT, fun σ hσ τ hτ ↦ ?_⟩
  obtain ⟨ε, hε, rfl⟩ : ∃ ε ∈ ({1, -1} : Finset ℝ), τ = ε * T := by
    rcases hτ with rfl | rfl
    · exact ⟨1, by simp, by ring⟩
    · exact ⟨-1, by simp, by ring⟩
  have hεT : |ε * T| = T := by
    have hε₁ : |ε| = 1 := by
      rcases Finset.mem_insert.mp hε with h | h
      · simp [h]
      · simp [Finset.mem_singleton.mp h]
    rw [abs_mul, hε₁, one_mul, abs_of_nonneg (by linarith [hT.1])]
  -- the zeros of `Z` are at vertical distance at least `δ` from the line `im s = εT`
  have hdist : ∀ ρ ∈ Z, δ ≤ |ε * T - ρ.im| := fun ρ hρ ↦ calc
    δ ≤ |T - (|ρ.im|)| := hfar ρ hρ
    _ = |(|ε * T|) - (|ρ.im|)| := by rw [hεT]
    _ ≤ |ε * T - ρ.im| := abs_abs_sub_abs_le_abs_sub _ _
  have hz₀ : f (σ + (ε * T : ℝ) * I) ≠ 0 := by
    intro h₀
    have h := hdist _ (hmemZ ε hε _ h₀ (by simp; linarith [hσ.1]) (by norm_num))
    simp at h
    linarith
  refine ⟨hz₀, ?_⟩
  set D := divisor f (closedBall (9 / 8 + (ε * T : ℝ) * I) (43 / 40))
  set ℓ := Real.log (Q * (T + 3))
  have hℓ : 1 ≤ ℓ := by
    have h := one_le_log_mul hQ (ε * T)
    rwa [hεT] at h
  have hc₀ := hf.center_ne_zero (ε * T)
  have hM : 1 ≤ (Q * (|ε * T| + 3)) ^ 6 :=
    one_le_pow₀ (by nlinarith [abs_nonneg (ε * T)])
  -- the point `σ + iεT` is within `17/16` of the center
  have hz : (σ + (ε * T : ℝ) * I : ℂ) ∈ closedBall (9 / 8 + (ε * T : ℝ) * I) (17 / 16) := by
    rw [mem_closedBall, dist_eq_norm,
      show (σ + (ε * T : ℝ) * I : ℂ) - (9 / 8 + (ε * T : ℝ) * I) = ((σ - 9 / 8 : ℝ) : ℂ) by
        push_cast
        ring, norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith [hσ.1, hσ.2]
  have hloc := hL f _ _ (hf.analyticOnNhd _) hc₀ hM (fun w hw ↦ hf.norm_le (ε * T) w hw) _ hz
    hz₀
  -- every zero in the disk lies in `Z`, so it is at distance at least `δ`
  have hsum : ‖∑ᶠ ρ, (D ρ : ℂ) / (σ + (ε * T : ℝ) * I - ρ)‖ ≤ ((∑ᶠ ρ, D ρ : ℤ) : ℝ) / δ := by
    refine norm_finsum_div_sub_le (D.finiteSupport (isCompact_closedBall _ _))
      (hf.divisor_nonneg _) hδ₀ fun ρ hρ ↦ ?_
    obtain ⟨hmem, hzero⟩ := hf.mem_and_eq_zero_of_divisor_ne_zero hρ
    obtain ⟨hre, him⟩ := re_pos_of_mem_closedBall hmem
    calc δ ≤ |ε * T - ρ.im| := hdist ρ (hmemZ ε hε ρ hzero hre him)
      _ = |(σ + (ε * T : ℝ) * I - ρ).im| := by simp
      _ ≤ ‖σ + (ε * T : ℝ) * I - ρ‖ := abs_im_le_norm _
  -- the zero count and the separation are both `O(log (Q (T + 3)))`
  have hD : ((∑ᶠ ρ, D ρ : ℤ) : ℝ) ≤ A' * ℓ := by
    have h := hA hf (ε * T)
    rw [hεT] at h
    refine h.trans ?_
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith)
  have hδ' : 1 / δ ≤ 4 * (28 * A' * ℓ) + 4 := by
    have hℓ₀ : ℓ₀ ≤ ℓ := Real.log_le_log (by positivity) (by nlinarith [hT.1])
    rw [hδ, one_div_one_div]
    nlinarith
  have hS : ((∑ᶠ ρ, D ρ : ℤ) : ℝ) / δ ≤ A' * ℓ * (4 * (28 * A' * ℓ) + 4) := by
    rw [div_eq_mul_one_div]
    exact mul_le_mul hD hδ' (by positivity) (by positivity)
  have hlog : K₀ * Real.log ((Q * (|ε * T| + 3)) ^ 6) = K₀ * (6 * ℓ) := by
    rw [log_pow_six, hεT]
  have hℓ₂ : ℓ ≤ ℓ ^ 2 := by nlinarith
  have h₁ := mul_le_mul_of_nonneg_left hℓ₂ hK₀
  have h₂ := mul_le_mul_of_nonneg_left hℓ₂ hA'
  calc _ = ‖(deriv f (σ + (ε * T : ℝ) * I) / f (σ + (ε * T : ℝ) * I) -
          ∑ᶠ ρ, (D ρ : ℂ) / (σ + (ε * T : ℝ) * I - ρ)) +
          ∑ᶠ ρ, (D ρ : ℂ) / (σ + (ε * T : ℝ) * I - ρ)‖ := by
        rw [sub_add_cancel]
    _ ≤ K₀ * Real.log ((Q * (|ε * T| + 3)) ^ 6) + ((∑ᶠ ρ, D ρ : ℤ) : ℝ) / δ :=
        (norm_add_le _ _).trans (add_le_add hloc hsum)
    _ ≤ K₀ * (6 * ℓ) + A' * ℓ * (4 * (28 * A' * ℓ) + 4) := by rw [hlog]; linarith
    _ ≤ _ := by nlinarith

/-- The zeros of `f` in the rectangle `[1/16, 2] × [-T, T]` lie in the strip
`1/8 ≤ re s ≤ 7/8`. -/
theorem Admissible.re_mem_Icc_of_divisor_ne_zero {f : ℂ → ℂ} {Q : ℝ} (hf : Admissible f Q)
    {T : ℝ} {ρ : ℂ}
    (hρ : divisor f (Rectangle (1 / 16 - T * I) (2 + T * I)) ρ ≠ 0) :
    ρ.re ∈ Set.Icc (1 / 8 : ℝ) (7 / 8) := by
  obtain ⟨hmem, hzero⟩ := hf.mem_and_eq_zero_of_divisor_ne_zero hρ
  have hre : ρ.re ∈ Set.uIcc (1 / 16 : ℝ) 2 := by
    simpa [Rectangle] using (mem_reProdIm.mp hmem).1
  rw [Set.uIcc_of_le (by norm_num)] at hre
  exact hf.re_mem_Icc ρ hzero (by linarith [hre.1])

/-- The zeros of `f` in `[1/16, 2] × [-T, T]`, weighted by
`(1 + |im ρ|)⁻²`, have total mass `O(log Q)`. -/
theorem exists_sum_divisor_rectangle_le :
    ∃ K : ℝ, ∀ {f : ℂ → ℂ} {Q : ℝ}, Admissible f Q →
      ∀ T : ℝ, ∑ᶠ ρ, (divisor f (Rectangle (1 / 16 - T * I) (2 + T * I)) ρ : ℝ) /
        (1 + |ρ.im|) ^ 2 ≤ K * Real.log Q := by
  obtain ⟨A, hA⟩ := exists_sum_divisor_closedBall_le
  -- the window `⌊4 im ρ⌋ = k` is centered at height `h k`
  set h : ℤ → ℝ := fun k ↦ ((k : ℝ) + 1 / 2) / 4 with hh
  set φ : ℤ → ℝ := fun k ↦ (1 + Real.log (|h k| + 3)) / (7 / 8 + |h k|) ^ 2 with hφ
  have hφ₀ : ∀ k, 0 ≤ φ k := fun k ↦ by
    have h := Real.log_nonneg (show (1 : ℝ) ≤ |h k| + 3 by linarith [abs_nonneg (h k)])
    positivity
  refine ⟨max A 0 * ∑' k, φ k, fun {f Q} hf T ↦ ?_⟩
  have hQ := hf.three_le
  set Dr := divisor f (Rectangle (1 / 16 - T * I) (2 + T * I))
  have hfin : Dr.support.Finite := Dr.finiteSupport (isCompact_uIcc.reProdIm isCompact_uIcc)
  have hlogQ := one_le_log_of_three_le hQ
  -- the zeros with `⌊4 im ρ⌋ = k` contribute at most `A log Q φ k`
  have hwin : ∀ k : ℤ, ∑ ρ ∈ hfin.toFinset with ⌊4 * ρ.im⌋ = k,
      (Dr ρ : ℝ) / (1 + |ρ.im|) ^ 2 ≤ max A 0 * Real.log Q * φ k := by
    intro k
    set D := divisor f (closedBall (9 / 8 + h k * I) (43 / 40))
    have hfinD : D.support.Finite := D.finiteSupport (isCompact_closedBall _ _)
    have hterm : ∀ ρ ∈ hfin.toFinset.filter (fun ρ ↦ ⌊4 * ρ.im⌋ = k),
        (Dr ρ : ℝ) / (1 + |ρ.im|) ^ 2 ≤ (D ρ : ℝ) / (7 / 8 + |h k|) ^ 2 := by
      intro ρ hρ
      rw [Finset.mem_filter] at hρ
      have hρ' : Dr ρ ≠ 0 := by simpa using hρ.1
      have hmem := (hf.mem_and_eq_zero_of_divisor_ne_zero hρ').1
      have hre := hf.re_mem_Icc_of_divisor_ne_zero hρ'
      -- `ρ` is within `1/8` of the height `h k`
      have hk : |ρ.im - h k| ≤ 1 / 8 := by
        have h₁ := Int.floor_le (4 * ρ.im)
        have h₂ := Int.lt_floor_add_one (4 * ρ.im)
        rw [hρ.2] at h₁ h₂
        simp only [hh]
        exact abs_le.mpr ⟨by linarith, by linarith⟩
      have hball := mem_closedBall_of_re_mem_Icc hre (hk.trans (by norm_num))
      have heq : Dr ρ = D ρ := hf.divisor_eq hmem hball
      have hD₀ : (0 : ℝ) ≤ D ρ := by exact_mod_cast hf.divisor_nonneg _ ρ
      have hle : 7 / 8 + |h k| ≤ 1 + |ρ.im| := by
        linarith [abs_sub_abs_le_abs_sub (h k) ρ.im, abs_sub_comm (h k) ρ.im]
      rw [heq]
      exact div_le_div_of_nonneg_left hD₀ (by positivity) (pow_le_pow_left₀ (by positivity) hle 2)
    have hlog : A * Real.log (Q * (|h k| + 3)) ≤
        max A 0 * (Real.log Q * (1 + Real.log (|h k| + 3))) := by
      have h₁ : 1 ≤ |h k| + 3 := by linarith [abs_nonneg (h k)]
      have h₂ : 0 ≤ Real.log (Q * (|h k| + 3)) := le_trans (by norm_num) (one_le_log_mul hQ _)
      exact (mul_le_mul_of_nonneg_right (le_max_left _ _) h₂).trans
        (mul_le_mul_of_nonneg_left (log_mul_le_log_mul hQ h₁) (le_max_right _ _))
    calc _ ≤ ∑ ρ ∈ hfin.toFinset with ⌊4 * ρ.im⌋ = k, (D ρ : ℝ) / (7 / 8 + |h k|) ^ 2 :=
          Finset.sum_le_sum hterm
      _ = (∑ ρ ∈ hfin.toFinset with ⌊4 * ρ.im⌋ = k, (D ρ : ℝ)) / (7 / 8 + |h k|) ^ 2 :=
          (Finset.sum_div _ _ _).symm
      _ ≤ ((∑ᶠ ρ, D ρ : ℤ) : ℝ) / (7 / 8 + |h k|) ^ 2 := by
          gcongr
          exact sum_le_finsum_of_nonneg hfinD (hf.divisor_nonneg _) _
      _ ≤ A * Real.log (Q * (|h k| + 3)) / (7 / 8 + |h k|) ^ 2 := by
          gcongr
          exact hA hf (h k)
      _ ≤ max A 0 * (Real.log Q * (1 + Real.log (|h k| + 3))) / (7 / 8 + |h k|) ^ 2 := by
          gcongr
      _ = max A 0 * Real.log Q * φ k := by
          simp only [hφ]
          ring
  have hsupp : (Function.support fun ρ ↦ (Dr ρ : ℝ) / (1 + |ρ.im|) ^ 2) ⊆ hfin.toFinset := by
    intro ρ hρ
    rw [Set.Finite.coe_toFinset, Function.mem_support]
    intro h₀
    exact hρ (by simp [h₀])
  rw [finsum_eq_sum_of_support_subset _ hsupp, ← Finset.sum_fiberwise_of_maps_to
    (fun ρ hρ ↦ Finset.mem_image_of_mem (fun ρ : ℂ ↦ ⌊4 * ρ.im⌋) hρ)]
  have hAr : 0 ≤ max A 0 * Real.log Q := by
    have := le_max_right A 0
    positivity
  calc _ ≤ ∑ k ∈ hfin.toFinset.image (fun ρ ↦ ⌊4 * ρ.im⌋), max A 0 * Real.log Q * φ k :=
        Finset.sum_le_sum fun k _ ↦ hwin k
    _ = max A 0 * Real.log Q * ∑ k ∈ hfin.toFinset.image (fun ρ ↦ ⌊4 * ρ.im⌋), φ k :=
        (Finset.mul_sum _ _ _).symm
    _ ≤ max A 0 * Real.log Q * ∑' k, φ k :=
        mul_le_mul_of_nonneg_left (summable_weight.sum_le_tsum _ fun k _ ↦ hφ₀ k) hAr
    _ = _ := by ring

end Erdos420
