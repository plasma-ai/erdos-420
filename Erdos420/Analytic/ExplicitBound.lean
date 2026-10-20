import Erdos420.Analytic.Admissible
import Erdos420.Analytic.Perron
import Erdos420.Analytic.Rectangle
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The smoothed twisted prime sum

For a nontrivial primitive character `χ` mod `q`,
`∑_{m ≤ x} Λ(m) χ(m) (1 - m / x) = O(x^{7/8} log q)`.

For an admissible `f` of conductor `Q`, shift the line integral of
`f'/f · x^s / (s (s + 1))` from `re s = 2` to `re s = 1/16` across a rectangle of
height `T ≈ Q x²` chosen by `exists_good_height`. Each zero `ρ` contributes
`x^ρ / (ρ (ρ + 1))`, and `re ρ ≤ 7/8`. The left edge is `O(x^{1/16} log Q)`,
and the horizontal edges are `O(1)`. For `f = L(s, χ)`, the Perron formula and
its `O(1)` truncation error finish the proof.
-/

namespace Erdos420

open Complex ArithmeticFunction DirichletCharacter MeromorphicOn

/-- To the right of `1/16`, `‖s (s + 1)‖` is at least `(1 + |im s|)² / 64`. -/
lemma one_add_abs_im_sq_le_norm_mul {s : ℂ} (hs : 1 / 16 ≤ s.re) :
    (1 + |s.im|) ^ 2 ≤ 64 * ‖s * (s + 1)‖ := by
  have h₁ : |s.im| ≤ ‖s‖ := abs_im_le_norm s
  have h₂ : s.re ≤ ‖s‖ := re_le_norm s
  have h₃ : |(s + 1).im| ≤ ‖s + 1‖ := abs_im_le_norm _
  have h₄ : (s + 1).re ≤ ‖s + 1‖ := re_le_norm _
  simp only [add_im, one_im, add_zero, add_re, one_re] at h₃ h₄
  have h₅ : 1 + |s.im| ≤ 32 * ‖s‖ := by linarith
  have h₆ : 1 + |s.im| ≤ 2 * ‖s + 1‖ := by linarith
  calc (1 + |s.im|) ^ 2 ≤ (32 * ‖s‖) * (2 * ‖s + 1‖) := by
        rw [sq]; exact mul_le_mul h₅ h₆ (by positivity) (by positivity)
    _ = 64 * ‖s * (s + 1)‖ := by rw [norm_mul]; ring

/-- To the right of `1/16`, `‖x^s / (s (s + 1))‖ ≤ 64 x^{re s} / (1 + |im s|)²`. -/
lemma norm_cpow_div_le {x : ℝ} (hx : 0 < x) {s : ℂ} (hs : 1 / 16 ≤ s.re) :
    ‖(x : ℂ) ^ s / (s * (s + 1))‖ ≤ 64 * x ^ s.re / (1 + |s.im|) ^ 2 := by
  have h := one_add_abs_im_sq_le_norm_mul hs
  have hpos : 0 < ‖s * (s + 1)‖ := by
    have : 0 < (1 + |s.im|) ^ 2 := by positivity
    linarith
  rw [norm_div, norm_cpow_eq_rpow_re_of_pos hx, div_le_div_iff₀ hpos (by positivity)]
  have := mul_le_mul_of_nonneg_left h (Real.rpow_nonneg hx.le s.re)
  linarith

/-- Off the real axis, `‖x^s / (s (s + 1))‖ ≤ x^{re s} / (im s)²`. -/
lemma norm_cpow_div_le_of_im_ne_zero {x : ℝ} (hx : 0 < x) {s : ℂ} (hs : s.im ≠ 0) :
    ‖(x : ℂ) ^ s / (s * (s + 1))‖ ≤ x ^ s.re / s.im ^ 2 := by
  have h₁ : |s.im| ≤ ‖s‖ := abs_im_le_norm s
  have h₃ : |(s + 1).im| ≤ ‖s + 1‖ := abs_im_le_norm _
  simp only [add_im, one_im, add_zero] at h₃
  have h : s.im ^ 2 ≤ ‖s * (s + 1)‖ := by
    rw [norm_mul, ← sq_abs, sq]
    exact mul_le_mul h₁ h₃ (abs_nonneg _) (norm_nonneg _)
  have hpos : 0 < s.im ^ 2 := by positivity
  rw [norm_div, norm_cpow_eq_rpow_re_of_pos hx]
  exact div_le_div_of_nonneg_left (Real.rpow_nonneg hx.le _) hpos h

/-- `x^s / (s (s + 1))` is holomorphic to the right of zero. -/
lemma differentiableOn_cpow_div {x : ℝ} (hx : 0 < x) :
    DifferentiableOn ℂ (fun s : ℂ ↦ (x : ℂ) ^ s / (s * (s + 1))) {s : ℂ | 0 < s.re} := by
  intro s hs
  have hs₀ : s ≠ 0 := fun h ↦ by simp [h] at hs
  have hs₁ : s + 1 ≠ 0 := fun h ↦ by
    have := congrArg re h
    simp at this hs
    linarith
  have h₁ : DifferentiableAt ℂ (fun s : ℂ ↦ (x : ℂ) ^ s) s :=
    DifferentiableAt.const_cpow differentiableAt_id (Or.inl (ofReal_ne_zero.mpr hx.ne'))
  have h₂ : DifferentiableAt ℂ (fun s : ℂ ↦ s * (s + 1)) s := by fun_prop
  exact (h₁.div h₂ (mul_ne_zero hs₀ hs₁)).differentiableWithinAt

/-- `log (r a) ≤ log r (1 + log a)` when `log r ≥ 1` and `a ≥ 1`. -/
lemma log_mul_le_log_mul_one_add {r a : ℝ} (hr : 1 ≤ Real.log r) (ha : 1 ≤ a) :
    Real.log (r * a) ≤ Real.log r * (1 + Real.log a) := by
  have hr₀ : r ≠ 0 := by
    rintro rfl
    norm_num at hr
  have ha₀ : 0 ≤ Real.log a := Real.log_nonneg ha
  rw [Real.log_mul hr₀ (by linarith)]
  nlinarith

/-- `1 + log (|t| + 3) ≤ 5 (1 + |t|)^{1/2}`. -/
lemma one_add_log_le_rpow (t : ℝ) :
    1 + Real.log (|t| + 3) ≤ 5 * (1 + |t|) ^ (1 / 2 : ℝ) := by
  have hu : 1 ≤ 1 + |t| := by linarith [abs_nonneg t]
  have h₁ : Real.log (|t| + 3) ≤ Real.log 3 + Real.log (1 + |t|) := by
    rw [← Real.log_mul (by norm_num) (by linarith)]
    exact Real.log_le_log (by positivity) (by linarith [abs_nonneg t])
  have h₂ : Real.log 3 ≤ 2 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
    linarith
  have h₃ : Real.log (1 + |t|) ≤ (1 + |t|) ^ (1 / 2 : ℝ) / (1 / 2) :=
    Real.log_le_rpow_div (by linarith) (by norm_num)
  have h₄ : 1 ≤ (1 + |t|) ^ (1 / 2 : ℝ) := Real.one_le_rpow hu (by norm_num)
  linarith

/-- The left-edge weight: `log (r (|t| + 3)) · 64 / (1 + |t|)² ≤ 320 log r (1 + |t|)^{-3/2}`. -/
lemma log_mul_div_sq_le {r : ℝ} (hr : 1 ≤ Real.log r) (t : ℝ) :
    Real.log (r * (|t| + 3)) * (64 / (1 + |t|) ^ 2) ≤
      320 * Real.log r * (1 + |t|) ^ (-(3 / 2) : ℝ) := by
  have hu : 0 < 1 + |t| := by positivity
  have h₁ := log_mul_le_log_mul_one_add hr (a := |t| + 3) (by linarith [abs_nonneg t])
  have h₂ := one_add_log_le_rpow t
  have h₃ : (1 + |t|) ^ (-(3 / 2) : ℝ) = (1 + |t|) ^ (1 / 2 : ℝ) / (1 + |t|) ^ 2 := by
    rw [show (-(3 / 2) : ℝ) = 1 / 2 - (2 : ℕ) by norm_num, Real.rpow_sub hu,
      Real.rpow_natCast]
  rw [h₃]
  have h₄ : 0 ≤ 64 / (1 + |t|) ^ 2 := by positivity
  calc Real.log (r * (|t| + 3)) * (64 / (1 + |t|) ^ 2)
      ≤ Real.log r * (5 * (1 + |t|) ^ (1 / 2 : ℝ)) * (64 / (1 + |t|) ^ 2) := by
        gcongr
        exact h₁.trans (mul_le_mul_of_nonneg_left h₂ (by linarith))
    _ = 320 * Real.log r * ((1 + |t|) ^ (1 / 2 : ℝ) / (1 + |t|) ^ 2) := by ring

/-- For `T ≥ r x²` with `x ≥ 2` and `r ≥ 3`, `log² (r (T + 3)) x² / T² ≤ 16`. -/
lemma log_sq_mul_sq_div_sq_le {r x T : ℝ} (hr : 3 ≤ r) (hx : 2 ≤ x) (hT : r * x ^ 2 ≤ T) :
    Real.log (r * (T + 3)) ^ 2 * x ^ 2 / T ^ 2 ≤ 16 := by
  have hx₂ : 4 ≤ x ^ 2 := by nlinarith
  have hT₁ : 4 * r ≤ T := by nlinarith
  have hT₀ : 0 < T := by linarith
  have hxT : x ^ 2 ≤ T := by nlinarith
  have h₁ : r * (T + 3) ≤ T ^ 2 := by nlinarith
  have h₂ : 0 ≤ Real.log (r * (T + 3)) := Real.log_nonneg (by nlinarith)
  have h₃ : Real.log (r * (T + 3)) ≤ 4 * T ^ (1 / 2 : ℝ) := by
    calc Real.log (r * (T + 3)) ≤ Real.log (T ^ 2) := Real.log_le_log (by positivity) h₁
      _ = 2 * Real.log T := by rw [Real.log_pow]; norm_num
      _ ≤ 2 * (T ^ (1 / 2 : ℝ) / (1 / 2)) := by
        gcongr; exact Real.log_le_rpow_div hT₀.le (by norm_num)
      _ = 4 * T ^ (1 / 2 : ℝ) := by ring
  have h₄ : Real.log (r * (T + 3)) ^ 2 ≤ 16 * T := by
    calc Real.log (r * (T + 3)) ^ 2 ≤ (4 * T ^ (1 / 2 : ℝ)) ^ 2 := by gcongr
      _ = 16 * T := by
        rw [mul_pow, ← Real.sqrt_eq_rpow, Real.sq_sqrt hT₀.le]; norm_num
  rw [div_le_iff₀ (by positivity)]
  calc Real.log (r * (T + 3)) ^ 2 * x ^ 2 ≤ (16 * T) * T := by
        exact mul_le_mul h₄ hxT (by positivity) (by positivity)
    _ = 16 * T ^ 2 := by ring

/-- The zeros in the rectangle contribute at most `64 x^{7/8}` times their weighted
count. -/
lemma norm_finsum_divisor_mul_le {f : ℂ → ℂ} {Q : ℝ} (hf : Admissible f Q) {x : ℝ}
    (hx : 1 ≤ x) (T : ℝ) :
    ‖∑ᶠ ρ, (divisor f (Rectangle (1 / 16 - T * I) (2 + T * I)) ρ : ℂ) *
        ((x : ℂ) ^ ρ / (ρ * (ρ + 1)))‖ ≤
      64 * x ^ (7 / 8 : ℝ) * ∑ᶠ ρ,
        (divisor f (Rectangle (1 / 16 - T * I) (2 + T * I)) ρ : ℝ) / (1 + |ρ.im|) ^ 2 := by
  set D := divisor f (Rectangle (1 / 16 - T * I) (2 + T * I))
  -- the rectangle is compact, so the divisor has finite support
  have hfin : D.support.Finite :=
    D.finiteSupport (isCompact_uIcc.reProdIm isCompact_uIcc)
  -- the divisor of the entire function `f` is nonnegative
  have hD : ∀ ρ, 0 ≤ D ρ := hf.divisor_nonneg _
  -- each zero contributes at most `64 x^{7/8} / (1 + |im ρ|)²`
  have hterm : ∀ ρ, ‖(D ρ : ℂ) * ((x : ℂ) ^ ρ / (ρ * (ρ + 1)))‖ ≤
      64 * x ^ (7 / 8 : ℝ) * ((D ρ : ℝ) / (1 + |ρ.im|) ^ 2) := by
    intro ρ
    by_cases hρ : D ρ = 0
    · simp [hρ]
    have hre := hf.re_mem_Icc_of_divisor_ne_zero hρ
    have hK := norm_cpow_div_le (by linarith : (0 : ℝ) < x) (s := ρ)
      (by linarith [hre.1])
    have hx' : x ^ ρ.re ≤ x ^ (7 / 8 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx hre.2
    rw [norm_mul, Complex.norm_intCast, abs_of_nonneg (by exact_mod_cast hD ρ)]
    calc (D ρ : ℝ) * ‖(x : ℂ) ^ ρ / (ρ * (ρ + 1))‖
        ≤ (D ρ : ℝ) * (64 * x ^ (7 / 8 : ℝ) / (1 + |ρ.im|) ^ 2) := by
          gcongr
          · exact_mod_cast hD ρ
          · exact hK.trans (by gcongr)
      _ = 64 * x ^ (7 / 8 : ℝ) * ((D ρ : ℝ) / (1 + |ρ.im|) ^ 2) := by ring
  rw [finsum_eq_sum_of_support_subset_of_finite _ (s := D.support) ?_ hfin,
    finsum_eq_sum_of_support_subset_of_finite _ (s := D.support) ?_ hfin, Finset.mul_sum]
  · exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun ρ _ ↦ hterm ρ)
  · intro ρ hρ
    contrapose! hρ
    simp [Function.notMem_support.mp hρ]
  · intro ρ hρ
    contrapose! hρ
    simp [Function.notMem_support.mp hρ]


/-- A horizontal segment integral is at most the length times a pointwise bound. -/
lemma norm_hIntegral_le {F : ℂ → ℂ} {a b y C : ℝ} (hab : a ≤ b)
    (hF : ∀ σ ∈ Set.Icc a b, ‖F (σ + y * I)‖ ≤ C) : ‖HIntegral F a b y‖ ≤ C * (b - a) := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (C := C)
    (f := fun σ : ℝ ↦ F (σ + y * I)) fun σ hσ ↦ by
      rw [Set.uIoc_of_le hab] at hσ
      exact hF σ (Set.Ioc_subset_Icc_self hσ)
  rwa [abs_of_nonneg (by linarith)] at h

/-- A vertical segment integral is at most `c ∫ (1 + |t|)^{-3/2} dt` when the integrand is
dominated by `c (1 + |t|)^{-3/2}`. -/
lemma norm_vIntegral_le {F : ℂ → ℂ} {σ T c : ℝ} (hT : 0 ≤ T)
    (hF : ∀ t : ℝ, ‖F (σ + t * I)‖ ≤ c * (1 + |t|) ^ (-(3 / 2) : ℝ)) :
    ‖VIntegral F σ (-T) T‖ ≤ c * ∫ t : ℝ, (1 + |t|) ^ (-(3 / 2) : ℝ) := by
  have hint : MeasureTheory.Integrable fun t : ℝ ↦ c * (1 + |t|) ^ (-(3 / 2) : ℝ) := by
    have h := integrable_one_add_norm (E := ℝ) (μ := MeasureTheory.volume) (r := 3 / 2)
      (by simp; norm_num)
    simpa [Real.norm_eq_abs] using h.const_mul c
  have hc : 0 ≤ c := by simpa using (norm_nonneg _).trans (hF 0)
  rw [VIntegral, norm_smul, norm_I, one_mul, ← MeasureTheory.integral_const_mul]
  calc ‖∫ t in -T..T, F (σ + t * I)‖
      ≤ ∫ t in -T..T, c * (1 + |t|) ^ (-(3 / 2) : ℝ) :=
        intervalIntegral.norm_integral_le_of_norm_le (by linarith)
          (Filter.Eventually.of_forall fun t _ ↦ hF t) hint.intervalIntegrable
    _ ≤ ∫ t, c * (1 + |t|) ^ (-(3 / 2) : ℝ) := by
        rw [intervalIntegral.integral_of_le (by linarith)]
        exact MeasureTheory.setIntegral_le_integral hint
          (Filter.Eventually.of_forall fun t ↦ by positivity)

/-- The rectangle integral recovers the right edge from the other three. -/
lemma vIntegral_eq_rectangleIntegral (F : ℂ → ℂ) (T : ℝ) :
    VIntegral F 2 (-T) T = RectangleIntegral F (1 / 16 - T * I) (2 + T * I) -
      HIntegral F (1 / 16) 2 (-T) + HIntegral F (1 / 16) 2 T +
        VIntegral F (1 / 16) (-T) T := by
  simp only [RectangleIntegral, sub_re, add_re, sub_im, add_im, mul_re, mul_im, ofReal_re,
    ofReal_im, I_re, I_im]
  norm_num
  abel


/-- The truncated line integral of `f'/f · x^s / (s (s + 1))` on `re s = 2` is
`O(x^{7/8} log Q)` at a good height `T ∈ [T₀, T₀ + 1]`, for `T₀ ≥ Q x²`. -/
theorem exists_norm_vIntegral_logDeriv_le :
    ∃ K : ℝ, ∀ {f : ℂ → ℂ} {Q : ℝ}, Admissible f Q → ∀ x : ℝ, 2 ≤ x → ∀ T₀ : ℝ,
      Q * x ^ 2 ≤ T₀ → ∃ T ∈ Set.Icc T₀ (T₀ + 1),
        ‖VIntegral (fun s ↦ deriv f s / f s * ((x : ℂ) ^ s / (s * (s + 1)))) 2 (-T) T‖ ≤
          K * x ^ (7 / 8 : ℝ) * Real.log Q := by
  obtain ⟨K₂, hK₂⟩ := exists_norm_logDeriv_le_of_re_eq
  obtain ⟨K₃, hK₃⟩ := exists_good_height
  obtain ⟨K₄, hK₄⟩ := exists_sum_divisor_rectangle_le
  set I₀ := ∫ t : ℝ, (1 + |t|) ^ (-(3 / 2) : ℝ)
  have hI₀ : 0 ≤ I₀ := MeasureTheory.integral_nonneg fun t ↦ by positivity
  refine ⟨128 * Real.pi * |K₄| + 64 * |K₃| + 320 * |K₂| * I₀, ?_⟩
  intro f Q hf x hx T₀ hT₀
  set Kx : ℂ → ℂ := fun s ↦ (x : ℂ) ^ s / (s * (s + 1))
  set F : ℂ → ℂ := fun s ↦ deriv f s / f s * Kx s
  have hx₀ : 0 < x := by linarith
  have hQ := hf.three_le
  have hlogQ : 1 ≤ Real.log Q := one_le_log_of_three_le hQ
  -- a good height `T ∈ [T₀, T₀ + 1]`
  obtain ⟨T, hT, hTgood⟩ := hK₃ hf T₀ (by nlinarith)
  refine ⟨T, hT, ?_⟩
  have hTQ : Q * x ^ 2 ≤ T := hT₀.trans hT.1
  have hxT : x ^ 2 ≤ T := le_trans (by nlinarith) hTQ
  have hT₁ : 1 ≤ T := by nlinarith
  have hnormF : ∀ s, ‖F s‖ = ‖deriv f s / f s‖ * ‖Kx s‖ := fun s ↦ norm_mul _ _
  -- the zeros inside the rectangle
  have hR : ‖RectangleIntegral F (1 / 16 - T * I) (2 + T * I)‖ ≤
      2 * Real.pi * (64 * x ^ (7 / 8 : ℝ) * (|K₄| * Real.log Q)) := by
    have hU : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const continuous_re
    have hRU : Rectangle (1 / 16 - T * I) (2 + T * I) ⊆ {s : ℂ | 0 < s.re} := by
      intro s hs
      rw [Rectangle, mem_reProdIm] at hs
      have h := hs.1
      simp only [sub_re, add_re, mul_re, ofReal_re, ofReal_im, I_re, I_im] at h
      norm_num [Set.uIcc_of_le] at h
      exact lt_of_lt_of_le (by norm_num) h.1
    have hK : DifferentiableOn ℂ Kx {s : ℂ | 0 < s.re} := differentiableOn_cpow_div hx₀
    have hbd : ∀ s ∈ RectangleBorder (1 / 16 - T * I) (2 + T * I), f s ≠ 0 := by
      intro s hs
      have hs' : s = (s.re : ℂ) + s.im * I := (re_add_im s).symm
      simp only [RectangleBorder, Set.mem_union, mem_reProdIm, Set.mem_singleton_iff, sub_re,
        add_re, mul_re, ofReal_re, ofReal_im, I_re, I_im, sub_im, add_im, mul_im] at hs
      norm_num [Set.uIcc_of_le] at hs
      rcases hs with ((⟨h₁, h₂⟩ | ⟨h₁, h₂⟩) | ⟨h₁, h₂⟩) | ⟨h₁, h₂⟩
      · rw [hs', h₂]
        exact (hTgood s.re h₁ (-T) (by simp)).1
      · intro h₀
        have h := (hf.re_mem_Icc s h₀ (by rw [h₁]; norm_num)).1
        rw [h₁] at h
        norm_num at h
      · rw [hs', h₂]
        exact (hTgood s.re h₁ T (by simp)).1
      · exact hf.ne_zero_of_seven_eighths_lt_re (by rw [h₁]; norm_num)
    have h := rectangleIntegral_logDeriv_mul (z := 1 / 16 - T * I) (w := 2 + T * I)
      (by norm_num) (by simp; linarith) hU hRU hf.differentiable hK hbd
    rw [h]
    simp only [norm_mul, norm_ofNat, norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos,
      norm_I, mul_one]
    gcongr
    refine (norm_finsum_divisor_mul_le hf (by linarith) T).trans ?_
    gcongr
    exact (hK₄ hf T).trans (by gcongr; exact le_abs_self _)
  -- the horizontal edges at height `±T`
  have hH : ∀ τ ∈ ({T, -T} : Set ℝ), ‖HIntegral F (1 / 16) 2 τ‖ ≤ 32 * |K₃| := by
    intro τ hτ
    have hτ₂ : τ ^ 2 = T ^ 2 := by
      rcases hτ with rfl | rfl
      · rfl
      · exact neg_sq T
    have hlog := log_sq_mul_sq_div_sq_le hQ hx hTQ
    have hpt : ∀ σ ∈ Set.Icc (1 / 16 : ℝ) 2, ‖F (σ + τ * I)‖ ≤
        |K₃| * (Real.log (Q * (T + 3)) ^ 2 * x ^ 2 / T ^ 2) := by
      intro σ hσ
      have h₁ := (hTgood σ hσ τ hτ).2
      have h₂ : ‖Kx (σ + τ * I)‖ ≤ x ^ 2 / T ^ 2 := by
        have hre : (σ + τ * I : ℂ).re = σ := by simp
        have him : (σ + τ * I : ℂ).im = τ := by simp
        have h := norm_cpow_div_le_of_im_ne_zero hx₀ (s := σ + τ * I)
          (by rw [him]; rintro rfl; nlinarith)
        rw [hre, him] at h
        have hxσ : x ^ σ ≤ x ^ 2 := by
          have := Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ x) hσ.2
          rwa [Real.rpow_two] at this
        refine h.trans ?_
        rw [hτ₂]
        gcongr
      rw [hnormF]
      calc ‖deriv f (σ + τ * I) / f (σ + τ * I)‖ * ‖Kx (σ + τ * I)‖
          ≤ (|K₃| * Real.log (Q * (T + 3)) ^ 2) * (x ^ 2 / T ^ 2) := by
            refine mul_le_mul (h₁.trans ?_) h₂ (norm_nonneg _) (by positivity)
            gcongr
            exact le_abs_self _
        _ = |K₃| * (Real.log (Q * (T + 3)) ^ 2 * x ^ 2 / T ^ 2) := by ring
    refine (norm_hIntegral_le (by norm_num) hpt).trans ?_
    calc |K₃| * (Real.log (Q * (T + 3)) ^ 2 * x ^ 2 / T ^ 2) * (2 - 1 / 16)
        = |K₃| * (Real.log (Q * (T + 3)) ^ 2 * x ^ 2 / T ^ 2 * (2 - 1 / 16)) := by ring
      _ ≤ |K₃| * 32 := by gcongr; linarith
      _ = 32 * |K₃| := by ring
  -- the left edge `re s = 1/16`
  have hV : ‖VIntegral F (1 / 16) (-T) T‖ ≤
      320 * |K₂| * Real.log Q * x ^ (1 / 16 : ℝ) * I₀ := by
    refine norm_vIntegral_le (by linarith) fun t ↦ ?_
    have hs : (((1 / 16 : ℝ) : ℂ) + t * I) = 1 / 16 + t * I := by push_cast; ring
    have h₁ := hK₂ hf t
    have hre : (1 / 16 + t * I : ℂ).re = 1 / 16 := by simp
    have him : (1 / 16 + t * I : ℂ).im = t := by simp
    have h₂ := norm_cpow_div_le hx₀ (s := 1 / 16 + t * I) hre.ge
    rw [hre, him] at h₂
    have h₃ := log_mul_div_sq_le hlogQ t
    have h₄ : 0 ≤ Real.log (Q * (|t| + 3)) :=
      Real.log_nonneg (by nlinarith [abs_nonneg t])
    rw [hs, hnormF]
    calc ‖deriv f (1 / 16 + t * I) / f (1 / 16 + t * I)‖ * ‖Kx (1 / 16 + t * I)‖
        ≤ (|K₂| * Real.log (Q * (|t| + 3))) * (64 * x ^ (1 / 16 : ℝ) / (1 + |t|) ^ 2) := by
          refine mul_le_mul (h₁.trans ?_) h₂ (norm_nonneg _) (by positivity)
          gcongr
          exact le_abs_self _
      _ = |K₂| * x ^ (1 / 16 : ℝ) * (Real.log (Q * (|t| + 3)) * (64 / (1 + |t|) ^ 2)) := by
          ring
      _ ≤ |K₂| * x ^ (1 / 16 : ℝ) * (320 * Real.log Q * (1 + |t|) ^ (-(3 / 2) : ℝ)) := by
          gcongr
      _ = 320 * |K₂| * Real.log Q * x ^ (1 / 16 : ℝ) * (1 + |t|) ^ (-(3 / 2) : ℝ) := by
          ring
  -- assembling the pieces
  have hsplit : ‖VIntegral F 2 (-T) T‖ ≤
      ‖RectangleIntegral F (1 / 16 - T * I) (2 + T * I)‖ + ‖HIntegral F (1 / 16) 2 (-T)‖ +
        ‖HIntegral F (1 / 16) 2 T‖ + ‖VIntegral F (1 / 16) (-T) T‖ := by
    rw [vIntegral_eq_rectangleIntegral]
    have h₃ := norm_add_le (RectangleIntegral F (1 / 16 - T * I) (2 + T * I) -
      HIntegral F (1 / 16) 2 (-T) + HIntegral F (1 / 16) 2 T) (VIntegral F (1 / 16) (-T) T)
    have h₄ := norm_add_le (RectangleIntegral F (1 / 16 - T * I) (2 + T * I) -
      HIntegral F (1 / 16) 2 (-T)) (HIntegral F (1 / 16) 2 T)
    have h₅ := norm_sub_le (RectangleIntegral F (1 / 16 - T * I) (2 + T * I))
      (HIntegral F (1 / 16) 2 (-T))
    linarith
  have hP : 1 ≤ x ^ (7 / 8 : ℝ) * Real.log Q :=
    one_le_mul_of_one_le_of_one_le (Real.one_le_rpow (by linarith) (by norm_num)) hlogQ
  have hx₁₆ : x ^ (1 / 16 : ℝ) ≤ x ^ (7 / 8 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have h₂ : 64 * |K₃| ≤ 64 * |K₃| * (x ^ (7 / 8 : ℝ) * Real.log Q) :=
    le_mul_of_one_le_right (by positivity) hP
  have h₃ : 320 * |K₂| * Real.log Q * x ^ (1 / 16 : ℝ) * I₀ ≤
      320 * |K₂| * I₀ * (x ^ (7 / 8 : ℝ) * Real.log Q) := by
    have : 320 * |K₂| * Real.log Q * x ^ (1 / 16 : ℝ) * I₀ =
        320 * |K₂| * I₀ * (x ^ (1 / 16 : ℝ) * Real.log Q) := by ring
    rw [this]
    gcongr
  have hHT := hH T (by simp)
  have hHT' := hH (-T) (by simp)
  nlinarith

/-- The smoothed twisted prime sum is `O(x^{7/8} log q)` for a nontrivial primitive
character `χ` mod `q`. -/
theorem exists_norm_sum_vonMangoldt_le :
    ∃ K : ℝ, ∀ {q : ℕ} [NeZero q], 3 ≤ q → ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive →
      χ ≠ 1 → ∀ x : ℝ, 2 ≤ x → (∀ m : ℕ, (m : ℝ) ≠ x) →
        ‖∑ m ∈ Finset.Icc 1 ⌊x⌋₊, (Λ m : ℂ) * χ m * (1 - m / x)‖ ≤
          K * x ^ (7 / 8 : ℝ) * Real.log q := by
  obtain ⟨C₁, hC₁⟩ := exists_norm_verticalIntegral_sub_le
  obtain ⟨K, hK⟩ := exists_norm_vIntegral_logDeriv_le
  refine ⟨|C₁| + |K|, ?_⟩
  intro q _ hq χ hχ hχ₁ x hx hxN
  have hf := admissible_LFunction hq hχ hχ₁
  have hq₀ : (3 : ℝ) ≤ q := hf.three_le
  have hlogq : 1 ≤ Real.log q := one_le_log_of_three_le hq₀
  obtain ⟨T, hT, hbound⟩ := hK hf x hx (q * x ^ 2) le_rfl
  have hxT : x ^ 2 ≤ T := le_trans (by nlinarith) hT.1
  have hT₁ : 1 ≤ T := by nlinarith
  set P := perronIntegrand χ x
  -- the Perron integrand is `-(L'/L) · x^s / (s (s + 1))`
  have hP : VIntegral P 2 (-T) T = -VIntegral (fun s ↦ deriv (LFunction χ) s /
      LFunction χ s * ((x : ℂ) ^ s / (s * (s + 1)))) 2 (-T) T := by
    simp only [P, VIntegral, perronIntegrand, neg_mul, intervalIntegral.integral_neg, smul_neg]
  -- truncating the line integral at height `T`
  have hC : ‖VerticalIntegral P 2 - VIntegral P 2 (-T) T‖ ≤ |C₁| := by
    refine (hC₁ χ (by linarith) hT₁).trans ?_
    rw [mul_div_assoc]
    calc C₁ * (x ^ 2 / T) ≤ |C₁| * (x ^ 2 / T) := by gcongr; exact le_abs_self _
      _ ≤ |C₁| * 1 := by gcongr; exact div_le_one_of_le₀ hxT (by positivity)
      _ = |C₁| := mul_one _
  have hS : 2 * Real.pi * ‖∑ m ∈ Finset.Icc 1 ⌊x⌋₊, (Λ m : ℂ) * χ m * (1 - m / x)‖ =
      ‖VerticalIntegral P 2‖ := by
    rw [verticalIntegral_perronIntegrand χ (by linarith) hxN]
    simp [abs_of_pos Real.pi_pos]
  have hV : ‖VerticalIntegral P 2‖ ≤ |C₁| + |K| * x ^ (7 / 8 : ℝ) * Real.log q := by
    have h₁ := norm_sub_norm_le (VerticalIntegral P 2) (VIntegral P 2 (-T) T)
    have h₂ : ‖VIntegral P 2 (-T) T‖ ≤ |K| * x ^ (7 / 8 : ℝ) * Real.log q := by
      rw [hP, norm_neg]
      refine hbound.trans ?_
      gcongr
      exact le_abs_self _
    linarith
  have hpos : 1 ≤ x ^ (7 / 8 : ℝ) * Real.log q :=
    one_le_mul_of_one_le_of_one_le (Real.one_le_rpow (by linarith) (by norm_num)) hlogq
  have h₁ : |C₁| ≤ |C₁| * (x ^ (7 / 8 : ℝ) * Real.log q) :=
    le_mul_of_one_le_right (abs_nonneg _) hpos
  have h₄ : ‖∑ m ∈ Finset.Icc 1 ⌊x⌋₊, (Λ m : ℂ) * χ m * (1 - m / x)‖ ≤
      2 * Real.pi * ‖∑ m ∈ Finset.Icc 1 ⌊x⌋₊, (Λ m : ℂ) * χ m * (1 - m / x)‖ :=
    le_mul_of_one_le_left (norm_nonneg _) (by linarith [Real.two_le_pi])
  nlinarith

end Erdos420
