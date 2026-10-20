import Erdos420.Asymptotics
import PrimeGapsTheory.Variational.MkVerified
import PrimeGapsTheory.Variational.M016Asymp.IkTensorUpperBound

/-!
# Growth of Maynard's variational constant `M k`

This is Proposition 4.3 of Maynard, *Small gaps between primes* (Ann. of Math. 181 (2015)),
proved as in its Section 7: for all large `k`,
`M k ≥ log k − 2 log log k − 2`, where `M k = PrimeGaps.M k` is the supremum of
`∑ₘ Jₘ(F) / I(F)` over `L²(𝓡 k)`.

The witness is `F(t) = ∏ᵢ g(k tᵢ)`, with `g(u) = 1 / (1 + A u)` on `[0, T]` and `0`
elsewhere, `A = log k − 2 log log k`, and `T = (eᴬ − 1) / A`, so that `∫₀ᵀ g = 1`.
- `I(F) ≤ (γ / k)ᵏ` with `γ = ∫₀ᵀ g²` (`simplex_integral_bound`).
- Every `Jₘ(F)` is at least `k⁻²` times the integral of `∏_{i < k} g(k tᵢ)²` over
  `∑ tᵢ ≤ 1 − T / k`, since there the inner integral is `∫₀^{T/k} g(k t) dt = 1 / k`.
- Chebyshev's inequality for the sum of `k − 1` independent variables with density
  proportional to `g(k t)²` bounds the complementary mass by a variance, and the variance of
  one variable is at most `T / k` times its mean.

## Main results

* `Erdos420.log_sub_two_log_log_sub_two_le_M`: `log k − 2 log log k − 2 ≤ M k` for large `k`.
* `Erdos420.tendsto_M_atTop`: `M k → ∞`.
-/

namespace Erdos420

open MeasureTheory Filter Finset
open scoped PrimeGaps

section Chebyshev

variable {h : ℝ → ℝ} {b : ℝ}

/-- A continuous function times a bounded measurable function supported in `[0, b]` is
integrable. -/
private lemma integrable_mul_of_support_Icc {p : ℝ → ℝ} (hp : Continuous p) (hmeas : Measurable h)
    (hbdd : ∀ s, |h s| ≤ 1) (hsupp : ∀ s, h s ≠ 0 → s ∈ Set.Icc 0 b) :
    Integrable (fun s ↦ p s * h s) := by
  have hsub : Function.support (fun s ↦ p s * h s) ⊆ Set.Icc 0 b := fun s hs ↦
    hsupp s (right_ne_zero_of_mul hs)
  rw [← integrableOn_iff_integrable_of_support_subset hsub]
  exact (hp.continuousOn.integrableOn_compact isCompact_Icc).mul_bdd hmeas.aestronglyMeasurable
    (c := 1) (ae_of_all _ fun s ↦ by simpa [Real.norm_eq_abs] using hbdd s)

/-- `a(yᵢ) a(yⱼ) ∏ₗ h(yₗ)` as a product of one-variable functions. -/
private lemma mul_mul_prod_eq_prod {n : ℕ} (a : ℝ → ℝ) (i j : Fin n) (y : Fin n → ℝ) :
    a (y i) * a (y j) * ∏ l, h (y l) =
      ∏ l, a (y l) ^ ((if l = i then 1 else 0) + (if l = j then 1 else 0)) * h (y l) := by
  rw [prod_mul_distrib]
  simp_rw [pow_add, prod_mul_distrib, pow_ite, pow_one, pow_zero, prod_ite_eq', mem_univ,
    ite_true]

/-- The second moment of `∑ⱼ (yⱼ − μ)` under the product density `∏ₗ h(yₗ)`, where `μ` is the
mean of `h`, is `n` times the variance of `h` times `(∫ h)ⁿ⁻¹`. -/
private lemma integral_sq_sum_sub_mul_prod (n : ℕ) (hmeas : Measurable h) (hbdd : ∀ s, |h s| ≤ 1)
    (hsupp : ∀ s, h s ≠ 0 → s ∈ Set.Icc 0 b) (μ : ℝ)
    (hμ : ∫ s, (s - μ) * h s = 0) :
    Integrable (fun y : Fin n → ℝ ↦ (∑ j, (y j - μ)) ^ 2 * ∏ l, h (y l)) ∧
      ∫ y : Fin n → ℝ, (∑ j, (y j - μ)) ^ 2 * ∏ l, h (y l) =
        n * (∫ s, (s - μ) ^ 2 * h s) * (∫ s, h s) ^ (n - 1) := by
  have hint : ∀ e : ℕ, Integrable (fun s ↦ (s - μ) ^ e * h s) := fun e ↦
    integrable_mul_of_support_Icc (by fun_prop) hmeas hbdd hsupp
  have hterm : ∀ i j : Fin n, Integrable (fun y : Fin n → ℝ ↦
      (y i - μ) * (y j - μ) * ∏ l, h (y l)) := by
    intro i j
    simp_rw [mul_mul_prod_eq_prod (fun s ↦ s - μ) i j]
    exact Integrable.fintype_prod (f := fun l s ↦
      (s - μ) ^ ((if l = i then 1 else 0) + (if l = j then 1 else 0)) * h s) fun l ↦ hint _
  have hval : ∀ i j : Fin n, ∫ y : Fin n → ℝ, (y i - μ) * (y j - μ) * ∏ l, h (y l) =
      if i = j then (∫ s, (s - μ) ^ 2 * h s) * (∫ s, h s) ^ (n - 1) else 0 := by
    intro i j
    simp_rw [mul_mul_prod_eq_prod (fun s ↦ s - μ) i j]
    rw [integral_fintype_prod_volume_eq_prod (fun l s ↦
      (s - μ) ^ ((if l = i then 1 else 0) + (if l = j then 1 else 0)) * h s)]
    split_ifs with hij
    · subst hij
      rw [← mul_prod_erase _ _ (mem_univ i), prod_congr rfl (g := fun _ ↦ ∫ s, h s) fun l hl ↦ by
        simp only [ne_of_mem_erase hl, ite_false, zero_add, pow_zero, one_mul], prod_const,
        card_erase_of_mem (mem_univ i), card_univ, Fintype.card_fin]
      simp only [ite_true, Nat.reduceAdd]
    · refine prod_eq_zero (mem_univ i) ?_
      simp only [ite_true, hij, ite_false, add_zero, pow_one, hμ]
  have hexpand : (fun y : Fin n → ℝ ↦ (∑ j, (y j - μ)) ^ 2 * ∏ l, h (y l)) =
      fun y ↦ ∑ i, ∑ j, (y i - μ) * (y j - μ) * ∏ l, h (y l) := by
    funext y
    rw [sq, sum_mul_sum, sum_mul]
    simp_rw [sum_mul]
  rw [hexpand]
  refine ⟨integrable_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦ hterm i j, ?_⟩
  rw [integral_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦ hterm i j]
  simp_rw [integral_finsetSum _ fun j _ ↦ hterm _ j, hval, sum_ite_eq, mem_univ, ite_true,
    sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- **Chebyshev bound.** Let `h` be a density with values in `[0, 1]`, supported in `[0, b]`,
with mass `ν = ∫ h > 0`, first moment `m₁ = ∫ s h(s)`, and mean `μ = m₁ / ν`. If
`D = c − n μ > 0`, then the mass of `∏ₗ h(yₗ)` on the simplex `∑ₗ yₗ ≤ c` is at least
`νⁿ − n νⁿ⁻¹ b m₁ / D²`. -/
private lemma sub_le_setIntegral_simplexPi_prod (n : ℕ) (hmeas : Measurable h) (h0 : ∀ s, 0 ≤ h s)
    (h1 : ∀ s, h s ≤ 1) (hsupp : ∀ s, h s ≠ 0 → s ∈ Set.Icc 0 b) (hν : 0 < ∫ s, h s) (c : ℝ)
    (hD : 0 < c - n * ((∫ s, s * h s) / ∫ s, h s)) :
    (∫ s, h s) ^ n - n * (∫ s, h s) ^ (n - 1) * (b * ∫ s, s * h s) /
        (c - n * ((∫ s, s * h s) / ∫ s, h s)) ^ 2 ≤
      ∫ y in PrimeGaps.simplexPi n c, ∏ l, h (y l) := by
  set ν := ∫ s, h s with hν_def
  set m₁ := ∫ s, s * h s with hm₁_def
  set μ := m₁ / ν with hμ_def
  set D := c - n * μ with hD_def
  have hbdd : ∀ s, |h s| ≤ 1 := fun s ↦ by rw [abs_of_nonneg (h0 s)]; exact h1 s
  have hint : ∀ {p : ℝ → ℝ}, Continuous p → Integrable (fun s ↦ p s * h s) := fun hp ↦
    integrable_mul_of_support_Icc hp hmeas hbdd hsupp
  have hint0 : Integrable h := by simpa using hint (p := fun _ ↦ 1) continuous_const
  have hint1 : Integrable (fun s ↦ s * h s) := hint (p := fun s ↦ s) continuous_id
  -- the mean of `h` is `μ`
  have hmean : ∫ s, (s - μ) * h s = 0 := by
    simp_rw [sub_mul]
    rw [integral_sub hint1 (hint0.const_mul μ), integral_const_mul, ← hν_def, ← hm₁_def, hμ_def,
      div_mul_cancel₀ _ hν.ne', sub_self]
  -- the variance of `h` is at most `b m₁`, since `s² ≤ b s` on `[0, b]`
  have hvar : ∫ s, (s - μ) ^ 2 * h s ≤ b * m₁ := by
    calc ∫ s, (s - μ) ^ 2 * h s ≤ ∫ s, (b * (s * h s) - 2 * μ * ((s - μ) * h s)) := by
          refine integral_mono (hint (by fun_prop)) ((hint1.const_mul b).sub
            ((hint (p := fun s ↦ s - μ) (by fun_prop)).const_mul _)) fun s ↦ ?_
          by_cases hs : h s = 0
          · simp [hs]
          obtain ⟨hs0, hsb⟩ := hsupp s hs
          nlinarith [mul_nonneg (mul_nonneg hs0 (sub_nonneg.2 hsb)) (h0 s),
            mul_nonneg (sq_nonneg μ) (h0 s)]
      _ = b * m₁ := by
          rw [integral_sub (hint1.const_mul b)
              ((hint (p := fun s ↦ s - μ) (by fun_prop)).const_mul _),
            integral_const_mul, integral_const_mul, hmean, mul_zero, sub_zero]
  set P : (Fin n → ℝ) → ℝ := fun y ↦ ∏ l, h (y l) with hP_def
  have hP0 : ∀ y, 0 ≤ P y := fun y ↦ prod_nonneg fun l _ ↦ h0 _
  have hPint : Integrable P := Integrable.fintype_prod (f := fun _ ↦ h) fun _ ↦ hint0
  have hPtot : ∫ y, P y = ν ^ n := by
    rw [hP_def, integral_fintype_prod_volume_eq_prod (fun _ ↦ h), prod_const, card_univ,
      Fintype.card_fin]
  set S : Set (Fin n → ℝ) := {y | c < ∑ l, y l} with hS_def
  have hS : MeasurableSet S := measurableSet_lt measurable_const (by fun_prop)
  -- off the simplex, either `∑ yₗ > c` or some `yₗ < 0`, where `P y = 0`
  have hsplit : ∫ y in PrimeGaps.simplexPi n c, P y = ν ^ n - ∫ y, S.indicator P y := by
    rw [← integral_indicator (PrimeGaps.measurableSet_simplexPi n c), ← hPtot,
      ← integral_sub hPint (hPint.indicator hS)]
    refine integral_congr_ae (ae_of_all _ fun y ↦ ?_)
    by_cases hy : y ∈ PrimeGaps.simplexPi n c
    · have hyS : y ∉ S := fun hyS ↦ (not_lt.2 hy.2) hyS
      simp [Set.indicator_of_mem hy, Set.indicator_of_notMem hyS]
    rw [Set.indicator_of_notMem hy]
    by_cases hyS : y ∈ S
    · simp [Set.indicator_of_mem hyS]
    have hy' : ¬((∀ l, 0 ≤ y l) ∧ ∑ l, y l ≤ c) := hy
    have hyS' : ¬(c < ∑ l, y l) := hyS
    obtain ⟨l, hl⟩ : ∃ l, y l < 0 := by
      by_contra! hcon
      exact hy' ⟨hcon, not_lt.1 hyS'⟩
    have hPy : P y = 0 := prod_eq_zero (mem_univ l) <| by
      by_contra hne
      exact not_le.2 hl (hsupp _ hne).1
    simp [Set.indicator_of_notMem hyS, hPy]
  -- Chebyshev: on `S`, `1 ≤ ((∑ⱼ (yⱼ − μ)) / D)²`
  obtain ⟨hQint, hQ⟩ := integral_sq_sum_sub_mul_prod n hmeas hbdd hsupp μ hmean
  have htail : ∫ y, S.indicator P y ≤ ∫ y, (D ^ 2)⁻¹ * ((∑ j, (y j - μ)) ^ 2 * P y) := by
    refine integral_mono (hPint.indicator hS) (hQint.const_mul _) fun y ↦ ?_
    by_cases hyS : y ∈ S
    · rw [Set.indicator_of_mem hyS]
      have hyS' : c < ∑ l, y l := hyS
      have hsum : D ≤ ∑ j, (y j - μ) := by
        rw [sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
        linarith
      have hsq : D ^ 2 ≤ (∑ j, (y j - μ)) ^ 2 := pow_le_pow_left₀ hD.le hsum 2
      rw [← mul_assoc]
      refine le_mul_of_one_le_left (hP0 y) ?_
      rw [inv_mul_eq_div, one_le_div (by positivity)]
      exact hsq
    · rw [Set.indicator_of_notMem hyS]
      exact mul_nonneg (by positivity) (mul_nonneg (sq_nonneg _) (hP0 y))
  rw [integral_const_mul, hQ] at htail
  rw [hsplit]
  have hbound : (D ^ 2)⁻¹ * (n * (∫ s, (s - μ) ^ 2 * h s) * ν ^ (n - 1)) ≤
      n * ν ^ (n - 1) * (b * m₁) / D ^ 2 := by
    rw [inv_mul_eq_div]
    refine div_le_div_of_nonneg_right ?_ (sq_nonneg _)
    rw [mul_right_comm]
    exact mul_le_mul_of_nonneg_left hvar (by positivity)
  linarith

end Chebyshev

section Profile

open PrimeGaps.M016Asymp B1_IkTensorUpperBound

variable {A T : ℝ}

/-- `g A T` vanishes off `[0, T]`. -/
private lemma mem_Icc_of_g_ne_zero {u : ℝ} (hu : SimplexIntegralBound.g A T u ≠ 0) :
    u ∈ Set.Icc 0 T := by
  by_contra hmem
  exact hu (Set.indicator_of_notMem hmem _)

/-- An integral over `ℝ` of a function cut off to `[0, T]` is an interval integral. -/
private lemma integral_indicator_Icc_eq (φ : ℝ → ℝ) (hT : 0 ≤ T) :
    ∫ u, (Set.Icc 0 T).indicator φ u = ∫ u in (0)..T, φ u := by
  rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le hT]

/-- `∫ g = log (1 + A T) / A`. -/
private lemma integral_g (hA : 0 < A) (hT : 0 < T) :
    ∫ u, SimplexIntegralBound.g A T u = Real.log (1 + A * T) / A := by
  change ∫ u, (Set.Icc 0 T).indicator (A0_GPositive.g A) u = _
  rw [integral_indicator_Icc_eq _ hT.le, A1_MuClosedForm.integral_g_aux A T hA hT]

/-- `∫ g² = γ`. -/
private lemma integral_g_sq (hT : 0 < T) :
    ∫ u, SimplexIntegralBound.g A T u ^ 2 = A1_MuClosedForm.gamma A T := by
  simp_rw [SimplexIntegralBound.sq_g_eq_indicator]
  rw [integral_indicator_Icc_eq _ hT.le, A1_MuClosedForm.gamma]

/-- `∫ u g(u)² = γ μ`. -/
private lemma integral_mul_g_sq (hA : 0 < A) (hT : 0 < T) :
    ∫ u, u * SimplexIntegralBound.g A T u ^ 2 =
      A1_MuClosedForm.gamma A T * A1_MuClosedForm.mu A T := by
  have hind : (fun u ↦ u * SimplexIntegralBound.g A T u ^ 2) =
      (Set.Icc 0 T).indicator (fun u ↦ u * A0_GPositive.g A u ^ 2) := by
    funext u
    rw [SimplexIntegralBound.sq_g_eq_indicator]
    by_cases hu : u ∈ Set.Icc (0 : ℝ) T <;> simp [hu]
  rw [hind, integral_indicator_Icc_eq _ hT.le, A1_MuClosedForm.mu,
    mul_inv_cancel_left₀ (A1_MuClosedForm.gamma_pos A T hA hT).ne']

variable {k : ℝ}

/-- `∫ g(k s)² ds = γ / k`. -/
private lemma integral_g_mul_sq (hk : 0 < k) (hT : 0 < T) :
    ∫ s, SimplexIntegralBound.g A T (k * s) ^ 2 = A1_MuClosedForm.gamma A T / k := by
  rw [Measure.integral_comp_mul_left (fun u ↦ SimplexIntegralBound.g A T u ^ 2),
    integral_g_sq hT, abs_of_pos (inv_pos.2 hk), smul_eq_mul, inv_mul_eq_div]

/-- `∫ s g(k s)² ds = γ μ / k²`. -/
private lemma integral_mul_g_mul_sq (hk : 0 < k) (hA : 0 < A) (hT : 0 < T) :
    ∫ s, s * SimplexIntegralBound.g A T (k * s) ^ 2 =
      A1_MuClosedForm.gamma A T * A1_MuClosedForm.mu A T / k ^ 2 := by
  have hfun : (fun s ↦ s * SimplexIntegralBound.g A T (k * s) ^ 2) =
      fun s ↦ k⁻¹ * ((k * s) * SimplexIntegralBound.g A T (k * s) ^ 2) := by
    funext s
    field_simp
  rw [hfun, integral_const_mul,
    Measure.integral_comp_mul_left (fun u ↦ u * SimplexIntegralBound.g A T u ^ 2),
    integral_mul_g_sq hA hT, abs_of_pos (inv_pos.2 hk), smul_eq_mul]
  field_simp

/-- Past `T / k`, the integral of `g(k s)` over `[0, c]` is `1 / k` when `1 + A T = eᴬ`. -/
lemma setIntegral_Icc_g_mul (hk : 0 < k) (hA : 0 < A) (hT : 0 < T)
    (hAT : 1 + A * T = Real.exp A) {c : ℝ} (hc : T / k ≤ c) :
    ∫ s in Set.Icc 0 c, SimplexIntegralBound.g A T (k * s) = 1 / k := by
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun s hs ↦ ?_,
    Measure.integral_comp_mul_left (SimplexIntegralBound.g A T), integral_g hA hT, hAT,
    Real.log_exp, div_self hA.ne', abs_of_pos (inv_pos.2 hk), smul_eq_mul, mul_one, one_div]
  by_contra hne
  obtain ⟨hs0, hsT⟩ := mem_Icc_of_g_ne_zero hne
  refine hs ⟨(mul_nonneg_iff_of_pos_left hk).1 hs0, hc.trans' ?_⟩
  rw [le_div_iff₀ hk, mul_comm]
  exact hsT

end Profile

section Witness

open PrimeGaps.M016Asymp B1_IkTensorUpperBound EuclideanSpace

variable {A T : ℝ}

/-- Maynard's witness `F(t) = ∏ᵢ g(k tᵢ)`. -/
noncomputable def maynardWitness (k : ℕ) (A T : ℝ) : EuclideanSpace ℝ (Fin k) → ℝ :=
  fun x ↦ ∏ i, SimplexIntegralBound.g A T (k * x i)

/-- `g(c s)` vanishes off `[0, T / c]`. -/
private lemma mem_Icc_of_g_mul_ne_zero {c s : ℝ} (hc : 0 < c)
    (hs : SimplexIntegralBound.g A T (c * s) ≠ 0) : s ∈ Set.Icc 0 (T / c) := by
  obtain ⟨hs0, hsT⟩ := mem_Icc_of_g_ne_zero hs
  refine ⟨(mul_nonneg_iff_of_pos_left hc).1 hs0, ?_⟩
  rw [le_div_iff₀ hc, mul_comm]
  exact hsT

/-- `x ↦ ∏ᵢ g(c xᵢ)` is measurable. -/
lemma measurable_prod_g_mul {n : ℕ} (c : ℝ) :
    Measurable (fun x : EuclideanSpace ℝ (Fin n) ↦ ∏ i, SimplexIntegralBound.g A T (c * x i)) :=
  Finset.measurable_prod _ fun i _ ↦ (SimplexIntegralBound.measurable_g A T).comp
    (measurable_const.mul (PiLp.continuous_apply 2 _ i).measurable)

/-- `∏ᵢ g(c xᵢ) ∈ [0, 1]`. -/
lemma prod_g_mul_mem_Icc (hA : 0 < A) {n : ℕ} (c : ℝ) (x : Fin n → ℝ) :
    ∏ i, SimplexIntegralBound.g A T (c * x i) ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨prod_nonneg fun _ _ ↦ (SimplexIntegralBound.g_mem_unitInterval A T hA _).1,
    prod_le_one₀ (fun _ _ ↦ (SimplexIntegralBound.g_mem_unitInterval A T hA _).1)
      fun _ _ ↦ (SimplexIntegralBound.g_mem_unitInterval A T hA _).2⟩

/-- The scaled simplex `𝓡(n, c)` has finite volume. -/
instance {n : ℕ} {c : ℝ} : IsFiniteMeasure (volume.restrict (𝓡(n, c))) :=
  ⟨by rw [Measure.restrict_apply_univ]; exact isCompact_scaledStdSimplex.measure_lt_top⟩

/-- Maynard's witness is in `L²(𝓡 k)`, being bounded by `1`. -/
lemma memLp_maynardWitness (hA : 0 < A) (k : ℕ) :
    MemLp (maynardWitness k A T) 2 (volume.restrict (𝓡 k)) :=
  MemLp.of_bound (measurable_prod_g_mul _).aestronglyMeasurable 1 <| ae_of_all _ fun x ↦ by
    obtain ⟨h0, h1⟩ := prod_g_mul_mem_Icc hA (T := T) (k : ℝ) x.ofLp
    show ‖∏ i, SimplexIntegralBound.g A T (k * x i)‖ ≤ 1
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    exact h1

/-- Integrals over `𝓡(n, c)` are integrals over the simplex in `Fin n → ℝ`. -/
private lemma setIntegral_scaledStdSimplex_eq (n : ℕ) (c : ℝ) (G : (Fin n → ℝ) → ℝ) :
    ∫ t in 𝓡(n, c), G t.ofLp = ∫ y in PrimeGaps.simplexPi n c, G y := by
  have hmp := EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin n)
  exact hmp.setIntegral_preimage_emb (MeasurableEquiv.toLp 2 (Fin n → ℝ)).symm.measurableEmbedding
    G (PrimeGaps.simplexPi n c)

/-- `I(F) ≤ (γ / k)ᵏ`. -/
lemma norm_sq_maynardWitness_le (hA : 0 < A) (hT : 0 < T) {k : ℕ} (hk : 2 ≤ k) :
    ‖(memLp_maynardWitness hA k (T := T)).toLp _‖ ^ 2 ≤
      (A1_MuClosedForm.gamma A T / k) ^ k := by
  rw [PrimeGaps.I_toLp_eq]
  have hI : ∫ x in 𝓡 k, maynardWitness k A T x ^ 2 = SimplexIntegralBound.I k A T := by
    simp_rw [maynardWitness, ← prod_pow]
    exact setIntegral_scaledStdSimplex_eq k 1
      (fun y ↦ ∏ i, SimplexIntegralBound.g A T (k * y i) ^ 2)
  rw [hI, div_pow, div_eq_inv_mul, A1_MuClosedForm.gamma_formula A T hA hT]
  exact SimplexIntegralBound.simplex_integral_bound k A T hk hA hT

/-- Each `Jₘ(F)` is at least `k⁻²` times the mass of `∏_{i < k} g(k tᵢ)²` on
`∑ tᵢ ≤ 1 − T / k`, where the inner integral of `F` is `1 / k`. -/
lemma le_J_maynardWitness (hA : 0 < A) (hT : 0 < T) (hAT : 1 + A * T = Real.exp A) (n : ℕ)
    (m : Fin (n + 1)) :
    (((n + 1 : ℕ) : ℝ)⁻¹) ^ 2 * ∫ y in PrimeGaps.simplexPi n (1 - T / (n + 1 : ℕ)),
        ∏ l, SimplexIntegralBound.g A T ((n + 1 : ℕ) * y l) ^ 2 ≤
      PrimeGaps.J m ((memLp_maynardWitness hA (n + 1) (T := T)).toLp _) := by
  set κ : ℝ := ((n + 1 : ℕ) : ℝ) with hκ
  have hκ1 : 1 ≤ κ := by rw [hκ]; exact_mod_cast Nat.succ_pos n
  have hκ0 : 0 < κ := one_pos.trans_le hκ1
  rw [PrimeGaps.J_toLp_eq_iterated]
  show _ ≤ ∫ t in 𝓡 n, (∫ s in Set.Icc 0 (1 - ∑ i, t i),
    maynardWitness (n + 1) A T (insertLp m s t)) ^ 2
  set φ : ℝ → ℝ := fun c ↦ ∫ s in Set.Icc 0 c, SimplexIntegralBound.g A T (κ * s) with hφ
  have hinner : ∀ t : EuclideanSpace ℝ (Fin n), (∫ s in Set.Icc 0 (1 - ∑ i, t i),
      maynardWitness (n + 1) A T (insertLp m s t)) =
        φ (1 - ∑ i, t i) * ∏ j, SimplexIntegralBound.g A T (κ * t j) := by
    intro t
    simp only [maynardWitness, Fin.prod_univ_succAbove _ m, insertLp_apply_same,
      insertLp_apply_succAbove]
    rw [integral_mul_const]
  simp_rw [hinner]
  have hg0 : ∀ s, 0 ≤ SimplexIntegralBound.g A T (κ * s) := fun s ↦
    (SimplexIntegralBound.g_mem_unitInterval A T hA _).1
  have hgint : Integrable (fun s ↦ SimplexIntegralBound.g A T (κ * s)) := by
    simpa using integrable_mul_of_support_Icc (p := fun _ ↦ 1) continuous_const
      (h := fun s ↦ SimplexIntegralBound.g A T (κ * s)) (b := T / κ)
      ((SimplexIntegralBound.measurable_g A T).comp (measurable_const.mul measurable_id))
      (fun s ↦ by
        rw [abs_of_nonneg (hg0 s)]; exact (SimplexIntegralBound.g_mem_unitInterval A T hA _).2)
      fun s hs ↦ mem_Icc_of_g_mul_ne_zero hκ0 hs
  have hφmono : Monotone φ := fun c c' hcc' ↦
    setIntegral_mono_set hgint.integrableOn (ae_of_all _ hg0)
      (Set.Icc_subset_Icc_right hcc').eventuallyLE
  have hφ0 : ∀ c, 0 ≤ φ c := fun c ↦ setIntegral_nonneg measurableSet_Icc fun s _ ↦ hg0 s
  have hφ1 : ∀ c, φ c ≤ 1 := fun c ↦
    (hφmono (le_max_left c (T / κ))).trans <|
      (setIntegral_Icc_g_mul hκ0 hA hT hAT (le_max_right c (T / κ))).le.trans <|
        (div_le_one hκ0).2 hκ1
  have hint : IntegrableOn (fun t : EuclideanSpace ℝ (Fin n) ↦
      (φ (1 - ∑ i, t i) * ∏ j, SimplexIntegralBound.g A T (κ * t j)) ^ 2) (𝓡 n) := by
    refine Integrable.of_bound ((((hφmono.measurable.comp (measurable_const.sub
      (by fun_prop))).mul (measurable_prod_g_mul κ)).pow_const 2).aestronglyMeasurable) 1
      (ae_of_all _ fun t ↦ ?_)
    obtain ⟨h0, h1⟩ := prod_g_mul_mem_Icc hA (T := T) κ t.ofLp
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_one₀ (mul_nonneg (hφ0 _) h0)
      ((mul_le_mul (hφ1 _) h1 h0 zero_le_one).trans_eq (one_mul 1))
  have hsub : 𝓡(n, 1 - T / κ) ⊆ 𝓡 n := fun t ht ↦
    ⟨ht.1, ht.2.trans (by linarith [div_pos hT hκ0])⟩
  calc κ⁻¹ ^ 2 * ∫ y in PrimeGaps.simplexPi n (1 - T / κ),
        ∏ l, SimplexIntegralBound.g A T (κ * y l) ^ 2
      = ∫ t in 𝓡(n, 1 - T / κ),
          (φ (1 - ∑ i, t i) * ∏ j, SimplexIntegralBound.g A T (κ * t j)) ^ 2 := by
        rw [← integral_const_mul, ← setIntegral_scaledStdSimplex_eq]
        refine setIntegral_congr_fun isClosed_scaledStdSimplex.measurableSet fun t ht ↦ ?_
        have hc : T / κ ≤ 1 - ∑ i, t i := by linarith [ht.2]
        simp only [hφ, setIntegral_Icc_g_mul hκ0 hA hT hAT hc, mul_pow, prod_pow, one_div]
    _ ≤ _ := setIntegral_mono_set hint (ae_of_all _ fun t ↦ sq_nonneg _) hsub.eventuallyLE

end Witness

section Assembly

open PrimeGaps.M016Asymp B1_IkTensorUpperBound

/-- **Maynard's lower bound for `M k`.** With `k = n + 1`, `γ = ∫₀ᵀ g²`, `μ = γ⁻¹ ∫₀ᵀ u g(u)²`,
and `τ = n T μ / (k − T − n μ)²`, the witness gives `M k ≥ (1 − τ) / γ`. -/
lemma le_M_of_witness {A T : ℝ} (hA : 0 < A) (hT : 0 < T) (hAT : 1 + A * T = Real.exp A)
    {n : ℕ} (hn : 1 ≤ n) (hD : 0 < (n + 1 : ℝ) - T - n * A1_MuClosedForm.mu A T)
    (hτ : n * T * A1_MuClosedForm.mu A T /
      ((n + 1 : ℝ) - T - n * A1_MuClosedForm.mu A T) ^ 2 < 1) :
    (1 - n * T * A1_MuClosedForm.mu A T / ((n + 1 : ℝ) - T - n * A1_MuClosedForm.mu A T) ^ 2) /
      A1_MuClosedForm.gamma A T ≤ PrimeGaps.M (n + 1) := by
  set γ := A1_MuClosedForm.gamma A T with hγ_def
  set μ := A1_MuClosedForm.mu A T with hμ_def
  set E := (n + 1 : ℝ) - T - n * μ with hE_def
  set τ := n * T * μ / E ^ 2 with hτ_def
  set κ : ℝ := ((n + 1 : ℕ) : ℝ) with hκ
  have hκ' : κ = n + 1 := by rw [hκ]; push_cast; ring
  have hκ0 : 0 < κ := by rw [hκ']; positivity
  have hγ : 0 < γ := A1_MuClosedForm.gamma_pos A T hA hT
  set ν := γ / κ with hν_def
  have hν0 : 0 < ν := div_pos hγ hκ0
  -- Chebyshev for the density `g(κ s)²`
  have hcheb := sub_le_setIntegral_simplexPi_prod n
    (h := fun s ↦ SimplexIntegralBound.g A T (κ * s) ^ 2) (b := T / κ)
    (((SimplexIntegralBound.measurable_g A T).comp
      (measurable_const.mul measurable_id)).pow_const 2)
    (fun s ↦ sq_nonneg _)
    (fun s ↦ pow_le_one₀ (SimplexIntegralBound.g_mem_unitInterval A T hA _).1
      (SimplexIntegralBound.g_mem_unitInterval A T hA _).2)
    (fun s hs ↦ mem_Icc_of_g_mul_ne_zero hκ0 (pow_ne_zero_iff two_ne_zero |>.1 hs))
    (by rw [integral_g_mul_sq hκ0 hT]; exact hν0) (1 - T / κ)
  have hmean : (∫ s, s * SimplexIntegralBound.g A T (κ * s) ^ 2) /
      ∫ s, SimplexIntegralBound.g A T (κ * s) ^ 2 = μ / κ := by
    rw [integral_g_mul_sq hκ0 hT, integral_mul_g_mul_sq hκ0 hA hT, ← hγ_def, ← hμ_def]
    field_simp
  have hDκ : 1 - T / κ - n * (μ / κ) = E / κ := by
    rw [hE_def, hκ']
    field_simp
  rw [hmean, hDκ, integral_g_mul_sq hκ0 hT, integral_mul_g_mul_sq hκ0 hA hT, ← hγ_def,
    ← hμ_def] at hcheb
  have hlow : ν ^ n * (1 - τ) ≤ ∫ y in PrimeGaps.simplexPi n (1 - T / κ),
      ∏ l, SimplexIntegralBound.g A T (κ * y l) ^ 2 := by
    refine le_of_eq_of_le ?_ (hcheb (div_pos hD hκ0))
    rw [hτ_def, hν_def, ← pow_sub_one_mul (by omega : n ≠ 0)]
    field_simp
  set f := (memLp_maynardWitness hA (n + 1) (T := T)).toLp _ with hf
  have hsumJ : κ⁻¹ * ν ^ n * (1 - τ) ≤ ∑ m, PrimeGaps.J m f := by
    calc κ⁻¹ * ν ^ n * (1 - τ) = ∑ _m : Fin (n + 1), (κ⁻¹) ^ 2 * (ν ^ n * (1 - τ)) := by
          rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, ← hκ]
          field_simp
      _ ≤ ∑ m, PrimeGaps.J m f := sum_le_sum fun m _ ↦
          (mul_le_mul_of_nonneg_left hlow (by positivity)).trans
            (le_J_maynardWitness hA hT hAT n m)
  have hlow0 : 0 < κ⁻¹ * ν ^ n * (1 - τ) := by
    have : 0 < 1 - τ := by linarith
    positivity
  have hnorm : ‖f‖ ^ 2 ≤ ν ^ (n + 1) := norm_sq_maynardWitness_le hA hT (by omega)
  have hnorm0 : 0 < ‖f‖ ^ 2 := by
    refine (sq_nonneg _).lt_of_ne fun h0 ↦ ?_
    have : ∑ m, PrimeGaps.J m f ≤ 0 :=
      sum_nonpos fun m _ ↦ PrimeGaps.J_le.trans (by rw [← h0, mul_zero])
    linarith
  calc (1 - τ) / γ = κ⁻¹ * ν ^ n * (1 - τ) / ν ^ (n + 1) := by
        rw [pow_succ, hν_def]
        field_simp
    _ ≤ (∑ m, PrimeGaps.J m f) / ‖f‖ ^ 2 := div_le_div₀ (hlow0.le.trans hsumJ) hsumJ hnorm0 hnorm
    _ ≤ PrimeGaps.M (n + 1) := PrimeGaps.M_ge

end Assembly

section Asymptotics

open PrimeGaps.M016Asymp

/-- `2 log L ≤ 4 L / 5`, from `log L ≤ L / e` and `e ≥ 5 / 2`. -/
private lemma two_mul_log_le {L : ℝ} (hL : 0 < L) : 2 * Real.log L ≤ 4 * L / 5 := by
  have h1 := Real.add_one_le_exp (Real.log L - 1)
  rw [sub_add_cancel, Real.exp_sub, Real.exp_log hL] at h1
  have he : 5 / 2 ≤ Real.exp 1 := by nlinarith [Real.quadratic_le_exp_of_nonneg zero_le_one]
  have h2 : L / Real.exp 1 ≤ 2 * L / 5 := by
    rw [div_le_iff₀ (Real.exp_pos 1)]
    nlinarith
  linarith

/-- The numerical estimates of Section 7: for `k = n + 1`, `eᴬ L² = k` and `14 ≤ A ≤ L`, with
`T = (eᴬ − 1) / A` and `μ = 1 / (1 − e⁻ᴬ) − 1 / A`, the quantity `τ = n T μ / (k − T − n μ)²`
satisfies `A τ ≤ 16 / 9`, so `(1 − τ) / γ ≥ A − 2` for `γ = A⁻¹ (1 − e⁻ᴬ) ≤ A⁻¹`. -/
private lemma maynard_estimates {A L T μ : ℝ} {n : ℕ} (hA : 14 ≤ A) (hAL : A ≤ L)
    (hk : Real.exp A * L ^ 2 = n + 1) (hT : T = (Real.exp A - 1) / A)
    (hμ : μ = 1 / (1 - Real.exp (-A)) - 1 / A) :
    0 < (n + 1 : ℝ) - T - n * μ ∧ n * T * μ / ((n + 1 : ℝ) - T - n * μ) ^ 2 < 1 ∧
      A - 2 ≤ (1 - n * T * μ / ((n + 1 : ℝ) - T - n * μ) ^ 2) /
        (1 / A * (1 - 1 / Real.exp A)) := by
  set e := Real.exp A with he
  set k : ℝ := n + 1 with hk_def
  set E := k - T - n * μ with hE_def
  set τ := n * T * μ / E ^ 2 with hτ_def
  have hA0 : 0 < A := by linarith
  have he0 : 0 < e := Real.exp_pos A
  have he8 : 8 * A ≤ e - 1 := by nlinarith [Real.quadratic_le_exp_of_nonneg hA0.le]
  have he1 : 0 < e - 1 := by linarith
  have hkeA : e * A ^ 2 ≤ k := by
    rw [← hk]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hA0.le hAL 2) he0.le
  have hke : 196 * e ≤ k := by
    have : 196 ≤ A ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left this he0.le]
  have hn : (n : ℝ) ≤ k := by rw [hk_def]; linarith
  have hn0 : (0 : ℝ) ≤ n := n.cast_nonneg
  have hk0 : 0 ≤ k := by linarith
  have hAT : A * T = e - 1 := by rw [hT]; field_simp
  have hT0 : 0 < T := by rw [hT]; exact div_pos he1 hA0
  -- `A (1 − μ) = 1 − A / (e − 1) ∈ [7/8, 1]`
  have hX : A * (1 - μ) * (e - 1) = e - 1 - A := by
    have hinv : 1 - e⁻¹ = (e - 1) / e := by field_simp
    rw [hμ, Real.exp_neg, ← he, hinv]
    field_simp
    ring
  have hX0 : 7 / 8 ≤ A * (1 - μ) := by
    by_contra! h
    nlinarith [mul_lt_mul_of_pos_right h he1]
  have hX1 : A * (1 - μ) ≤ 1 := by
    by_contra! h
    nlinarith [mul_lt_mul_of_pos_right h he1]
  have hμ0 : 0 ≤ μ := by
    by_contra! h
    nlinarith [mul_neg_of_pos_of_neg hA0 h]
  have hμ1 : μ ≤ 1 := by
    by_contra! h
    nlinarith [mul_lt_mul_of_pos_left h hA0]
  -- `A E ≥ 3 k / 4`
  have hAE : 3 * k / 4 ≤ A * E := by
    have hid : A * E = k * (A * (1 - μ)) - A * T + (k - n) * (A * μ) := by rw [hE_def]; ring
    linarith [mul_le_mul_of_nonneg_left hX0 hk0,
      mul_nonneg (sub_nonneg.2 hn) (mul_nonneg hA0.le hμ0)]
  have hE0 : 0 < E := by
    by_contra! hE
    linarith [mul_nonpos_of_nonneg_of_nonpos hA0.le hE]
  -- `A τ ≤ 16 / 9`
  have h1 : A * (n * T * μ) ≤ k * e := by
    have : A * (n * T * μ) = n * μ * (e - 1) := by rw [← hAT]; ring
    rw [this]
    linarith [mul_le_mul_of_nonneg_right (mul_le_mul hn hμ1 hμ0 hk0) he1.le]
  have h2 : 9 * k ^ 2 / 16 ≤ (A * E) ^ 2 := by
    nlinarith [pow_le_pow_left₀ (by positivity) hAE 2]
  have h3 : A * (n * T * μ) ≤ 16 / 9 * E ^ 2 := by
    refine le_of_mul_le_mul_left ?_ (by positivity : 0 < A ^ 2)
    linarith [mul_le_mul_of_nonneg_left hkeA hk0, mul_le_mul_of_nonneg_left h1 (sq_nonneg A)]
  have hAτ : A * τ ≤ 16 / 9 := by
    rw [hτ_def, mul_div_assoc', div_le_iff₀ (by positivity)]
    exact h3
  have hτ1 : τ < 1 := by
    by_contra! h
    linarith [mul_le_mul_of_nonneg_left h hA0.le]
  refine ⟨hE0, hτ1, ?_⟩
  have hγ0 : 0 < 1 / A * (1 - 1 / e) :=
    mul_pos (by positivity) (sub_pos.2 ((div_lt_one he0).2 (by linarith)))
  have hγ1 : 1 / A * (1 - 1 / e) ≤ 1 / A :=
    mul_le_of_le_one_right (by positivity) (sub_le_self _ (by positivity))
  calc A - 2 ≤ (1 - τ) / (1 / A) := by
        rw [one_div, div_inv_eq_mul]
        linarith
    _ ≤ _ := div_le_div_of_nonneg_left (by linarith) hγ0 hγ1

/-- **Maynard, Proposition 4.3.** For all large `k`, `M k ≥ log k − 2 log log k − 2`. -/
theorem log_sub_two_log_log_sub_two_le_M :
    ∀ᶠ k : ℕ in atTop, Real.log k - 2 * Real.log (Real.log k) - 2 ≤ PrimeGaps.M k := by
  filter_upwards [eventually_ge_atTop ⌈Real.exp 70⌉₊, eventually_ge_atTop 2] with k hk hk2
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  have hk0 : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  set L := Real.log ((n + 1 : ℕ) : ℝ) with hL_def
  have hL : 70 ≤ L := (Real.le_log_iff_exp_le hk0).2 (Nat.ceil_le.1 hk)
  have hL0 : 0 < L := by linarith
  set A := L - 2 * Real.log L with hA_def
  have hA : 14 ≤ A := by linarith [two_mul_log_le hL0]
  have hA0 : 0 < A := by linarith
  have hAL : A ≤ L := by linarith [Real.log_nonneg (by linarith : (1 : ℝ) ≤ L)]
  have hexpL : Real.exp L = ((n + 1 : ℕ) : ℝ) := Real.exp_log hk0
  have hexpA : Real.exp A * L ^ 2 = n + 1 := by
    rw [hA_def, Real.exp_sub, show 2 * Real.log L = Real.log L + Real.log L by ring, Real.exp_add,
      Real.exp_log hL0, hexpL]
    field_simp
    push_cast
    ring
  set T := (Real.exp A - 1) / A with hT_def
  have hT0 : 0 < T := div_pos (by linarith [Real.add_one_le_exp A]) hA0
  have hAT : 1 + A * T = Real.exp A := by
    rw [hT_def]
    field_simp
    ring
  have hμ := A1_MuClosedForm.mu_special A T hA0 hT0 hAT
  have hγ : A1_MuClosedForm.gamma A T = 1 / A * (1 - 1 / Real.exp A) := by
    rw [A1_MuClosedForm.gamma_formula A T hA0 hT0, hAT]
  obtain ⟨hD, hτ, hbound⟩ := maynard_estimates hA hAL hexpA hT_def hμ
  have hM := le_M_of_witness hA0 hT0 hAT (n := n) (by omega) hD hτ
  rw [hγ] at hM
  exact hbound.trans hM

/-- Maynard's variational constant `M k` tends to infinity. -/
theorem tendsto_M_atTop : Tendsto (fun k : ℕ ↦ PrimeGaps.M k) atTop atTop := by
  have hlog : Tendsto (fun k : ℕ ↦ Real.log k / 5 + -2) atTop atTop :=
    tendsto_atTop_add_const_right _ (-2) <|
      tendsto_log_natCast_atTop.atTop_div_const (by norm_num)
  refine tendsto_atTop_mono' atTop ?_ hlog
  filter_upwards [log_sub_two_log_log_sub_two_le_M, eventually_ge_atTop 2] with k hk hk2
  have hL : 0 < Real.log k := Real.log_pos (by exact_mod_cast hk2)
  linarith [two_mul_log_le hL]

end Asymptotics

end Erdos420
