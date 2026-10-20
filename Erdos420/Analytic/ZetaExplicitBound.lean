import Erdos420.Analytic.ExplicitBound

/-!
# The smoothed prime sum

`∑_{m ≤ x} Λ(m) (1 - m / x) = x / 2 + O(x^{7/8})`.

Write `-ζ'/ζ = -f'/f + 1 / (s - 1)` with the admissible entire function
`f(s) = (s - 1) ζ(s)`. The `f'/f` part of the Perron integral is
`O(x^{7/8})` by `exists_norm_vIntegral_logDeriv_le`. The pole part
`x^s / (s (s + 1) (s - 1))` has residue `x / 2` at `s = 1` inside the rectangle
`[1/16, 2] × [-T, T]`, its horizontal edges are `O(1)`, and its left edge is
`O(x^{1/16})`. Truncating the Perron integral at height `T` costs `O(1)`.
-/

namespace Erdos420

open Complex ArithmeticFunction DirichletCharacter

/-- Away from `s = 1` and the zeros of `ζ`, `f'/f = ζ'/ζ + 1 / (s - 1)` for
`f(s) = (s - 1) ζ(s)`. -/
lemma logDeriv_LFunctionTrivChar₁ {s : ℂ} (hs : s ≠ 1) (hζ : LFunctionTrivChar 1 s ≠ 0) :
    deriv (LFunctionTrivChar₁ 1) s / LFunctionTrivChar₁ 1 s =
      deriv (LFunctionTrivChar 1) s / LFunctionTrivChar 1 s + 1 / (s - 1) := by
  have hs₁ : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  rw [deriv_LFunctionTrivChar₁_apply_of_ne_one 1 hs, LFunctionTrivChar₁_of_ne_one hs]
  field_simp

/-- A function continuous on the line `re s = σ` is integrable on its segments. -/
private lemma intervalIntegrable_of_continuousOn {F : ℂ → ℂ} {σ a b : ℝ}
    (hF : ∀ t : ℝ, ContinuousAt F (σ + t * I)) :
    IntervalIntegrable (fun t : ℝ ↦ F (σ + t * I)) MeasureTheory.volume a b := by
  have hc : Continuous fun t : ℝ ↦ (σ : ℂ) + t * I := by fun_prop
  exact (continuous_iff_continuousAt.mpr fun t ↦
    ContinuousAt.comp (g := F) (hF t) hc.continuousAt).intervalIntegrable _ _

/-- The smoothed prime sum is `x / 2 + O(x^{7/8})`. -/
theorem exists_norm_sum_vonMangoldt_sub_le :
    ∃ K : ℝ, ∀ x : ℝ, 2 ≤ x → (∀ m : ℕ, (m : ℝ) ≠ x) →
      ‖∑ m ∈ Finset.Icc 1 ⌊x⌋₊, (Λ m : ℂ) * (1 - m / x) - x / 2‖ ≤ K * x ^ (7 / 8 : ℝ) := by
  obtain ⟨C₁, hC₁⟩ := exists_norm_verticalIntegral_sub_le
  obtain ⟨K, hK⟩ := exists_norm_vIntegral_logDeriv_le
  set I₀ := ∫ t : ℝ, (1 + |t|) ^ (-(3 / 2) : ℝ)
  have hI₀ : 0 ≤ I₀ := MeasureTheory.integral_nonneg fun t ↦ by positivity
  refine ⟨|C₁| + |K| * Real.log 3 + 4 + 69 * I₀, ?_⟩
  intro x hx hxN
  have hf := admissible_LFunctionTrivChar₁
  have hx₀ : 0 < x := by linarith
  obtain ⟨T, hT, hbound⟩ := hK hf x hx (3 * x ^ 2) le_rfl
  have hxT : x ^ 2 ≤ T := le_trans (by nlinarith) hT.1
  have hT₁ : 1 ≤ T := by nlinarith
  set Kx : ℂ → ℂ := fun s ↦ (x : ℂ) ^ s / (s * (s + 1))
  set G : ℂ → ℂ := fun s ↦ deriv (LFunctionTrivChar₁ 1) s / LFunctionTrivChar₁ 1 s * Kx s
  set E : ℂ → ℂ := fun s ↦ Kx s / (s - 1)
  set P := perronIntegrand (1 : DirichletCharacter ℂ 1) x
  have hKx := differentiableOn_cpow_div hx₀
  have hU : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const continuous_re
  -- on the line `re s = 2`, the Perron integrand is `-G + E`
  have hline : ∀ t : ℝ, ((2 : ℝ) + t * I : ℂ) ≠ 1 ∧ LFunctionTrivChar 1 ((2 : ℝ) + t * I) ≠ 0 := by
    intro t
    have hre : ((2 : ℝ) + t * I : ℂ).re = 2 := by simp
    refine ⟨fun h ↦ by rw [h] at hre; norm_num at hre, ?_⟩
    exact LFunction_ne_zero_of_one_le_re _ (Or.inr fun h ↦ by rw [h] at hre; norm_num at hre)
      (by rw [hre]; norm_num)
  have hPGE : ∀ t : ℝ, P ((2 : ℝ) + t * I) = -G ((2 : ℝ) + t * I) + E ((2 : ℝ) + t * I) := by
    intro t
    obtain ⟨h₁, h₂⟩ := hline t
    have h := logDeriv_LFunctionTrivChar₁ h₁ h₂
    change -(deriv (LFunctionTrivChar 1) _ / LFunctionTrivChar 1 _) * Kx _ = _
    rw [show deriv (LFunctionTrivChar 1) ((2 : ℝ) + t * I) / LFunctionTrivChar 1 ((2 : ℝ) + t * I) =
      deriv (LFunctionTrivChar₁ 1) ((2 : ℝ) + t * I) / LFunctionTrivChar₁ 1 ((2 : ℝ) + t * I) -
        1 / ((2 : ℝ) + t * I - 1) by rw [h]; ring]
    simp only [G, E]
    ring
  -- `G` and `E` are continuous on the line `re s = 2`
  have hcont : ∀ t : ℝ, ContinuousAt G ((2 : ℝ) + t * I) ∧ ContinuousAt E ((2 : ℝ) + t * I) := by
    intro t
    obtain ⟨h₁, h₂⟩ := hline t
    have hf₀ : LFunctionTrivChar₁ 1 ((2 : ℝ) + t * I) ≠ 0 := by
      rw [LFunctionTrivChar₁_of_ne_one h₁]
      exact mul_ne_zero (sub_ne_zero.mpr h₁) h₂
    have hKc : ContinuousAt Kx ((2 : ℝ) + t * I) :=
      (hKx.differentiableAt (hU.mem_nhds (by simp))).continuousAt
    have hderiv : Continuous (deriv (LFunctionTrivChar₁ 1)) :=
      hf.differentiable.contDiff.continuous_deriv le_rfl
    refine ⟨((hderiv.continuousAt.div hf.differentiable.continuous.continuousAt hf₀).mul hKc),
      hKc.div (continuousAt_id.sub continuousAt_const) (sub_ne_zero.mpr h₁)⟩
  have hsplit : VIntegral P 2 (-T) T = -VIntegral G 2 (-T) T + VIntegral E 2 (-T) T := by
    have hG := intervalIntegrable_of_continuousOn (σ := 2) (a := -T) (b := T) fun t ↦ (hcont t).1
    have hE := intervalIntegrable_of_continuousOn (σ := 2) (a := -T) (b := T) fun t ↦ (hcont t).2
    have h : ∫ t in -T..T, P ((2 : ℝ) + t * I) =
        ∫ t in -T..T, (-G ((2 : ℝ) + t * I) + E ((2 : ℝ) + t * I)) :=
      intervalIntegral.integral_congr fun t _ ↦ hPGE t
    have hG' : IntervalIntegrable (fun t : ℝ ↦ -G ((2 : ℝ) + t * I)) MeasureTheory.volume
        (-T) T := hG.neg
    simp only [VIntegral]
    rw [h, intervalIntegral.integral_add hG' hE, intervalIntegral.integral_neg, smul_add,
      smul_neg]
  -- the pole at `s = 1` has residue `x / 2`
  have hres : RectangleIntegral E (1 / 16 - T * I) (2 + T * I) = 2 * Real.pi * I * (x / 2) := by
    have hRU : Rectangle (1 / 16 - T * I) (2 + T * I) ⊆ {s : ℂ | 0 < s.re} := by
      intro s hs
      rw [Rectangle, mem_reProdIm] at hs
      have h := hs.1
      simp only [sub_re, add_re, mul_re, ofReal_re, ofReal_im, I_re, I_im] at h
      norm_num [Set.uIcc_of_le] at h
      exact lt_of_lt_of_le (by norm_num) h.1
    have hp : Rectangle (1 / 16 - T * I) (2 + T * I) ∈ nhds 1 := by
      rw [rectangle_mem_nhds_iff, mem_reProdIm]
      simp only [sub_re, add_re, mul_re, ofReal_re, ofReal_im, I_re, I_im, sub_im, add_im,
        mul_im, one_re, one_im]
      norm_num [Set.uIoo_of_le, show -T ≤ T by linarith]
      linarith
    rw [rectangleIntegral_div_sub (by norm_num) (by simp; linarith) hU hRU hKx hp]
    simp only [cpow_one]
    ring
  -- the horizontal edges of the pole part
  have hH : ∀ τ ∈ ({T, -T} : Set ℝ), ‖HIntegral E (1 / 16) 2 τ‖ ≤ 2 := by
    intro τ hτ
    have hτ₂ : |τ| = T := by
      rcases hτ with rfl | rfl
      · exact abs_of_pos (by linarith)
      · rw [abs_neg]; exact abs_of_pos (by linarith)
    refine (norm_hIntegral_le (C := 1) (by norm_num) fun σ hσ ↦ ?_).trans (by norm_num)
    have him : (σ + τ * I : ℂ).im = τ := by simp
    have hre : (σ + τ * I : ℂ).re = σ := by simp
    have h₁ := norm_cpow_div_le_of_im_ne_zero hx₀ (s := σ + τ * I)
      (by rw [him]; intro h; rw [h] at hτ₂; simp at hτ₂; linarith)
    rw [hre, him] at h₁
    have h₂ : T ≤ ‖(σ + τ * I : ℂ) - 1‖ := by
      refine le_trans ?_ (abs_im_le_norm _)
      simp [hτ₂]
    have hxσ : x ^ σ ≤ x ^ 2 := by
      have := Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ x) hσ.2
      rwa [Real.rpow_two] at this
    have hτsq : τ ^ 2 = T ^ 2 := by rw [← sq_abs, hτ₂]
    simp only [E, norm_div]
    rw [div_le_one (by linarith)]
    calc ‖Kx (σ + τ * I)‖ ≤ x ^ σ / τ ^ 2 := h₁
      _ ≤ x ^ 2 / T ^ 2 := by rw [hτsq]; gcongr
      _ ≤ 1 := by rw [div_le_one (by positivity)]; nlinarith
      _ ≤ T := hT₁
      _ ≤ _ := h₂
  -- the left edge of the pole part
  have hV : ‖VIntegral E (1 / 16) (-T) T‖ ≤ 69 * x ^ (1 / 16 : ℝ) * I₀ := by
    refine norm_vIntegral_le (by linarith) fun t ↦ ?_
    have hs : (((1 / 16 : ℝ) : ℂ) + t * I) = 1 / 16 + t * I := by push_cast; ring
    have hre : (1 / 16 + t * I : ℂ).re = 1 / 16 := by simp
    have him : (1 / 16 + t * I : ℂ).im = t := by simp
    have h₁ := norm_cpow_div_le hx₀ (s := 1 / 16 + t * I) hre.ge
    rw [hre, him] at h₁
    have h₂ : 15 / 16 ≤ ‖(1 / 16 + t * I : ℂ) - 1‖ := by
      refine le_trans ?_ (abs_re_le_norm _)
      norm_num
    have hu : 1 ≤ 1 + |t| := by linarith [abs_nonneg t]
    have h₃ : (1 + |t|) ^ (-(2 : ℝ)) ≤ (1 + |t|) ^ (-(3 / 2) : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hu (by norm_num)
    have h₄ : 64 * x ^ (1 / 16 : ℝ) / (1 + |t|) ^ 2 =
        64 * x ^ (1 / 16 : ℝ) * (1 + |t|) ^ (-(2 : ℝ)) := by
      rw [Real.rpow_neg (by positivity), Real.rpow_two, div_eq_mul_inv]
    rw [hs]
    simp only [E, norm_div]
    rw [div_le_iff₀ (by linarith)]
    calc ‖Kx (1 / 16 + t * I)‖ ≤ 64 * x ^ (1 / 16 : ℝ) * (1 + |t|) ^ (-(2 : ℝ)) := h₄ ▸ h₁
      _ ≤ 64 * x ^ (1 / 16 : ℝ) * (1 + |t|) ^ (-(3 / 2) : ℝ) := by gcongr
      _ ≤ 69 * x ^ (1 / 16 : ℝ) * (1 + |t|) ^ (-(3 / 2) : ℝ) * (15 / 16) := by
        have : 0 ≤ x ^ (1 / 16 : ℝ) * (1 + |t|) ^ (-(3 / 2) : ℝ) := by positivity
        nlinarith
      _ ≤ _ := by gcongr
  -- truncating the line integral at height `T`
  have hC : ‖VerticalIntegral P 2 - VIntegral P 2 (-T) T‖ ≤ |C₁| := by
    refine (hC₁ _ (by linarith) hT₁).trans ?_
    rw [mul_div_assoc]
    calc C₁ * (x ^ 2 / T) ≤ |C₁| * (x ^ 2 / T) := by gcongr; exact le_abs_self _
      _ ≤ |C₁| * 1 := by gcongr; exact div_le_one_of_le₀ hxT (by positivity)
      _ = |C₁| := mul_one _
  -- assembling the pieces
  have hS : VerticalIntegral P 2 =
      2 * Real.pi * I * ∑ m ∈ Finset.Icc 1 ⌊x⌋₊, (Λ m : ℂ) * (1 - m / x) := by
    rw [verticalIntegral_perronIntegrand _ (by linarith) hxN]
    simp [MulChar.one_apply (isUnit_of_subsingleton _)]
  have hE : VIntegral E 2 (-T) T - 2 * Real.pi * I * (x / 2) =
      -HIntegral E (1 / 16) 2 (-T) + HIntegral E (1 / 16) 2 T + VIntegral E (1 / 16) (-T) T := by
    rw [vIntegral_eq_rectangleIntegral, hres]
    ring
  have hkey : 2 * Real.pi * I * (∑ m ∈ Finset.Icc 1 ⌊x⌋₊, (Λ m : ℂ) * (1 - m / x) - x / 2) =
      (VerticalIntegral P 2 - VIntegral P 2 (-T) T) - VIntegral G 2 (-T) T +
        (-HIntegral E (1 / 16) 2 (-T) + HIntegral E (1 / 16) 2 T +
          VIntegral E (1 / 16) (-T) T) := by
    rw [← hE, mul_sub, ← hS, hsplit]
    ring
  have hnorm : ‖2 * Real.pi * I * (∑ m ∈ Finset.Icc 1 ⌊x⌋₊, (Λ m : ℂ) * (1 - m / x) - x / 2)‖ =
      2 * Real.pi * ‖∑ m ∈ Finset.Icc 1 ⌊x⌋₊, (Λ m : ℂ) * (1 - m / x) - x / 2‖ := by
    simp [abs_of_pos Real.pi_pos]
  have hHT := hH T (by simp)
  have hHT' := hH (-T) (by simp)
  have hbound' : ‖VIntegral G 2 (-T) T‖ ≤ |K| * x ^ (7 / 8 : ℝ) * Real.log 3 := by
    refine hbound.trans ?_
    gcongr
    exact le_abs_self _
  have htot : 2 * Real.pi * ‖∑ m ∈ Finset.Icc 1 ⌊x⌋₊, (Λ m : ℂ) * (1 - m / x) - x / 2‖ ≤
      |C₁| + |K| * x ^ (7 / 8 : ℝ) * Real.log 3 + 4 + 69 * x ^ (1 / 16 : ℝ) * I₀ := by
    rw [← hnorm, hkey]
    have h₁ := norm_add_le ((VerticalIntegral P 2 - VIntegral P 2 (-T) T) - VIntegral G 2 (-T) T)
      (-HIntegral E (1 / 16) 2 (-T) + HIntegral E (1 / 16) 2 T + VIntegral E (1 / 16) (-T) T)
    have h₂ := norm_sub_le (VerticalIntegral P 2 - VIntegral P 2 (-T) T) (VIntegral G 2 (-T) T)
    have h₃ := norm_add_le (-HIntegral E (1 / 16) 2 (-T) + HIntegral E (1 / 16) 2 T)
      (VIntegral E (1 / 16) (-T) T)
    have h₄ := norm_add_le (-HIntegral E (1 / 16) 2 (-T)) (HIntegral E (1 / 16) 2 T)
    rw [norm_neg] at h₄
    linarith
  have hx₇ : 1 ≤ x ^ (7 / 8 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
  have hx₁₆ : x ^ (1 / 16 : ℝ) ≤ x ^ (7 / 8 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have hlog3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have h₁ : ‖∑ m ∈ Finset.Icc 1 ⌊x⌋₊, (Λ m : ℂ) * (1 - m / x) - x / 2‖ ≤
      2 * Real.pi * ‖∑ m ∈ Finset.Icc 1 ⌊x⌋₊, (Λ m : ℂ) * (1 - m / x) - x / 2‖ :=
    le_mul_of_one_le_left (norm_nonneg _) (by linarith [Real.two_le_pi])
  have h₂ : 69 * x ^ (1 / 16 : ℝ) * I₀ ≤ 69 * I₀ * x ^ (7 / 8 : ℝ) := by
    rw [mul_right_comm]
    gcongr
  nlinarith [abs_nonneg C₁, abs_nonneg K]

end Erdos420
