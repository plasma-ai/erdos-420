/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsTheory.Arithmetic.Mertens.DivisorPowerSum
public import PrimeGapsTheory.Sieve.Common.SieveDatumEval.KFold

/-!
# Partial summation with an Euler-product error

The sharp and the `k`-fold partial summation of a `SieveDatum` with the `τ(V)` errors of
`S1_partial_sum_sharp` and `sieveDatum_kfold_partial_sum` replaced by the Euler product
`P_σ(V) = ∑_{d ∣ V} d^{σ-1}`, for any `0 < σ ≤ 1/4`. Both rest on the `σ`-power `H` asymptotic
`slem_H_error_assembly_rpow`, `|S.H t - 𝔖 log t| ≤ C₁ 𝔖 (1 + ℓ_V) + C₂ t^{-σ} P_σ(V) / σ`, whose
Abel tail `∫₂^z t^{-σ-1} ≤ 1/σ` and endpoint `z^{-σ} ≤ 1/(σ log z)` give the residual
`P_σ(V) / (σ² log z)`. For a modulus `V` whose prime factors are at most `y`, `σ = 1 / log y` makes
`P_σ(V) ≤ (V/φ(V))³` (`sum_divisors_rpow_le_cube`), however large `τ(V)` is.

## Main results

* `S1_partial_sum_sharp_rpow`
* `sieveDatum_kfold_partial_sum_rpow`
-/

@[expose] public section

open scoped Finset

open MeasureTheory

namespace PrimeGaps

/-- `z^{-σ} ≤ 1/(σ log z)` for `z > 1` and `σ > 0`, since `σ log z ≤ exp (σ log z) = z^σ`. -/
theorem rpow_neg_le_one_div_mul_log {z σ : ℝ} (hz : 1 < z) (hσ : 0 < σ) :
    z ^ (-σ) ≤ 1 / (σ * Real.log z) := by
  have hz0 : 0 < z := by linarith
  have hlog : 0 < σ * Real.log z := mul_pos hσ (Real.log_pos hz)
  have hle : σ * Real.log z ≤ z ^ σ := by
    rw [Real.rpow_def_of_pos hz0, mul_comm σ]
    linarith only [Real.add_one_le_exp (Real.log z * σ)]
  rw [Real.rpow_neg hz0.le, ← one_div]
  exact one_div_le_one_div_of_le hlog hle

/-- `∫₂^z t^{-σ-1} ≤ 1/σ`. -/
theorem integral_rpow_neg_sub_one_le (z : ℝ) (hz : 2 ≤ z) {σ : ℝ} (hσ : 0 < σ) :
    (∫ t in (2 : ℝ)..z, t ^ (-σ - 1)) ≤ 1 / σ := by
  have hz0 : (0 : ℝ) < z := by linarith
  rw [integral_rpow (Or.inr ⟨by linarith, by
      rw [Set.uIcc_of_le hz]; simp only [Set.mem_Icc]; push Not; intro h; linarith⟩),
    show -σ - 1 + 1 = -σ by ring]
  have h21 : (2 : ℝ) ^ (-σ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
  rw [div_neg, ← neg_div, neg_sub, div_le_div_iff_of_pos_right hσ]
  linarith [Real.rpow_pos_of_pos hz0 (-σ)]

/-- **Abel tail from a pointwise `A + B t^{-σ}` bound.** If `|f t| ≤ A + B t^{-σ}` on `[2, z]`, then
`∫₂^z |f t| / t ≤ A log z + B / σ`. -/
theorem intTail_two_z_le_rpow (f : ℝ → ℝ) (z : ℝ) (hz : 2 ≤ z) {A B σ : ℝ} (hA : 0 ≤ A)
    (hB : 0 ≤ B) (hσ : 0 < σ)
    (hii : IntervalIntegrable (fun t ↦ |f t| / t) volume 2 z)
    (hpt : ∀ t ∈ Set.Icc (2 : ℝ) z, |f t| ≤ A + B * t ^ (-σ)) :
    (∫ t in (2 : ℝ)..z, |f t| / t) ≤ A * Real.log z + B / σ := by
  have hz0 : (0 : ℝ) < z := by linarith
  set g : ℝ → ℝ := fun t ↦ A * (1 / t) + B * t ^ (-σ - 1) with hg
  have hpos : ∀ x ∈ Set.uIcc (2 : ℝ) z, x ≠ 0 := fun x hx ↦ by
    rw [Set.uIcc_of_le hz] at hx; exact (by linarith [hx.1] : (0 : ℝ) < x).ne'
  have hg1 : IntervalIntegrable (fun t ↦ A * (1 / t)) volume 2 z :=
    (ContinuousOn.div continuousOn_const continuousOn_id hpos).intervalIntegrable.const_mul A
  have hg2 : IntervalIntegrable (fun t ↦ B * t ^ (-σ - 1)) volume 2 z :=
    (ContinuousOn.rpow_const continuousOn_id fun x hx ↦
      Or.inl (hpos x hx)).intervalIntegrable.const_mul B
  have hpoint : ∀ t ∈ Set.Icc (2 : ℝ) z, |f t| / t ≤ g t := by
    intro t ht
    have ht0 : (0 : ℝ) < t := by linarith [ht.1]
    have hrw : B * t ^ (-σ - 1) = B * t ^ (-σ) / t := by
      rw [Real.rpow_sub ht0, Real.rpow_one]; ring
    rw [hg]; simp only
    rw [hrw, div_le_iff₀ ht0]
    calc |f t| ≤ A + B * t ^ (-σ) := hpt t ht
      _ = (A * (1 / t) + B * t ^ (-σ) / t) * t := by field_simp
  have hint1 : (∫ t in (2 : ℝ)..z, (1 / t)) ≤ Real.log z := by
    rw [integral_one_div (by rw [Set.uIcc_of_le hz]; simp only [Set.mem_Icc]; norm_num),
      Real.log_div hz0.ne' (by norm_num)]
    linarith only [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)]
  calc (∫ t in (2 : ℝ)..z, |f t| / t) ≤ ∫ t in (2 : ℝ)..z, g t :=
        intervalIntegral.integral_mono_on hz hii (hg1.add hg2) hpoint
    _ = A * (∫ t in (2 : ℝ)..z, (1 / t)) + B * (∫ t in (2 : ℝ)..z, t ^ (-σ - 1)) := by
        rw [hg, intervalIntegral.integral_add hg1 hg2, intervalIntegral.integral_const_mul,
          intervalIntegral.integral_const_mul]
    _ ≤ A * Real.log z + B * (1 / σ) :=
        add_le_add (mul_le_mul_of_nonneg_left hint1 hA)
          (mul_le_mul_of_nonneg_left (integral_rpow_neg_sub_one_le z hz hσ) hB)
    _ = A * Real.log z + B / σ := by ring

/-- **The Abel bracket from a pointwise `A + B t^{-σ}` bound.** If
`|S.H t - 𝔖 log t| ≤ A + B t^{-σ}` for all `t ≥ 2`, then the endpoint term plus the normalised Abel
tail, `|S.H z - 𝔖 log z| + (1 / log z) ∫₁^z |S.H t - 𝔖 log t| / t`, is at most
`2 A + 𝔖 + (2 B / σ + 1) / log z`. -/
theorem abel_bracket_le_rpow (S : SieveDatum) (z : ℝ) (hz : 2 ≤ z) {A B σ : ℝ} (hA : 0 ≤ A)
    (hB : 0 ≤ B) (hσ : 0 < σ)
    (hH : ∀ t : ℝ, 2 ≤ t → |S.H t - 𝔖 S.γ * Real.log t| ≤ A + B * t ^ (-σ)) :
    |S.H z - 𝔖 S.γ * Real.log z| +
        1 / Real.log z * ∫ (t : ℝ) in 1..z, |S.H t - 𝔖 S.γ * Real.log t| / t ≤
      2 * A + 𝔖 S.γ + (2 * B / σ + 1) / Real.log z := by
  set SS := 𝔖 S.γ with hSS
  have hSS_pos : 0 < SS := by rw [hSS]; exact PrimeGaps.singularSeries_pos S
  have hlogz : 0 < Real.log z := Real.log_pos (by linarith)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2_lt1 : Real.log 2 < 1 := by linarith only [Real.log_two_lt_d9]
  have hlog2z : Real.log 2 ≤ Real.log z := Real.log_le_log (by norm_num) hz
  have hii12 : IntervalIntegrable (fun t ↦ |S.H t - SS * Real.log t| / t) volume 1 2 :=
    integrand_ii S 2 le_rfl
  have hii2z : IntervalIntegrable (fun t ↦ |S.H t - SS * Real.log t| / t) volume 2 z :=
    (integrand_ii S z hz).mono_set (by
      rw [Set.uIcc_of_le hz, Set.uIcc_of_le (by linarith : (1 : ℝ) ≤ z)]
      exact Set.Icc_subset_Icc (by norm_num) le_rfl)
  have htail : (∫ t in (1 : ℝ)..z, |S.H t - SS * Real.log t| / t) ≤
      A * Real.log z + B / σ + (Real.log 2 + SS * (Real.log 2) ^ 2) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals hii12 hii2z]
    linarith only [S1_intTail_one_two_le S,
      intTail_two_z_le_rpow (fun t ↦ S.H t - SS * Real.log t) z hz hA hB hσ hii2z
        fun t ht ↦ hH t ht.1]
  have hend : |S.H z - SS * Real.log z| ≤ A + B / (σ * Real.log z) :=
    (hH z hz).trans (by
      rw [show B / (σ * Real.log z) = B * (1 / (σ * Real.log z)) by ring]
      gcongr
      exact rpow_neg_le_one_div_mul_log (by linarith) hσ)
  have hsq : SS * (Real.log 2) ^ 2 / Real.log z ≤ SS := by
    rw [div_le_iff₀ hlogz]
    have h : (Real.log 2) ^ 2 ≤ Real.log z := by nlinarith only [hlog2_lt1, hlog2, hlog2z]
    exact mul_le_mul_of_nonneg_left h hSS_pos.le
  have hnorm : 1 / Real.log z * (A * Real.log z + B / σ + (Real.log 2 + SS * (Real.log 2) ^ 2)) =
      A + B / (σ * Real.log z) + Real.log 2 / Real.log z + SS * (Real.log 2) ^ 2 / Real.log z := by
    field_simp
    ring
  have hlog2div : Real.log 2 / Real.log z ≤ 1 / Real.log z :=
    div_le_div_of_nonneg_right hlog2_lt1.le hlogz.le
  have hrw : (2 * B / σ + 1) / Real.log z = 2 * (B / (σ * Real.log z)) + 1 / Real.log z := by
    field_simp
  rw [hrw]
  linarith only [hend, mul_le_mul_of_nonneg_left htail (by positivity : 0 ≤ 1 / Real.log z),
    hnorm, hsq, hlog2div]

/-- **Sharp partial summation, Euler-product error.** For `G` bounded by `M` and `M`-Lipschitz on
`[0, 1]`, `z ≥ 2` and `0 < σ ≤ 1/4`, the discrepancy between `∑_{0 < d < z} S.h d G (log d / log z)`
and `𝔖 log z ∫₀¹ G` is at most `2 M (C₁ 𝔖 (1 + ℓ_V) + C₂ P_σ(V) / (σ² log z))`, with
`P_σ(V) = ∑_{d ∣ V} d^{σ-1}`. This is `S1_partial_sum_sharp` with `τ(V)` replaced by `P_σ(V)`. -/
theorem S1_partial_sum_sharp_rpow : ∃ (C₁ : ℝ → ℝ → ℝ) (C₂ : ℝ → ℝ → ℝ),
      (∀ A₁ A₃ : ℝ, 0 < C₁ A₁ A₃) ∧ (∀ A₁ A₃ : ℝ, 0 < C₂ A₁ A₃) ∧
      ∀ (S : SieveDatum) (G : ℝ → ℝ) (M : ℝ), 0 ≤ M → (∀ x ∈ Set.Icc (0 : ℝ) 1, |G x| ≤ M) →
        (∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1, |G x - G y| ≤ M * |x - y|) →
        ∀ z : ℝ, 2 ≤ z → ∀ σ : ℝ, 0 < σ → σ ≤ 1 / 4 →
          |∑ d ∈ Finset.range ⌈z⌉₊ with (0 : ℕ) < d ∧ (↑d : ℝ) < z,
              S.h d * G (Real.log ↑d / Real.log z) -
            PrimeGaps.singularSeries S.γ * Real.log z * ∫ x in (0 : ℝ)..1, G x| ≤ (2 * M) *
              (C₁ S.A₁ S.A₃ * PrimeGaps.singularSeries S.γ * (1 + ellV S.V) +
                C₂ S.A₁ S.A₃ * ((∑ d ∈ S.V.divisors, (d : ℝ) ^ (σ - 1)) /
                  (σ ^ 2 * Real.log z))) := by
  obtain ⟨Ch₁, Ch₂, hCh₁, hCh₂, hHasymp⟩ := PrimeGaps.slem_H_error_assembly_rpow
  refine ⟨fun A₁ A₃ ↦ 2 * Ch₁ A₁ A₃ + 1, fun A₁ A₃ ↦ 2 * Ch₂ A₁ A₃ + 1,
    fun A₁ A₃ ↦ by linarith only [hCh₁ A₁ A₃], fun A₁ A₃ ↦ by linarith only [hCh₂ A₁ A₃], ?_⟩
  intro S G M hM hbdd hlip z hz σ hσ0 hσ1
  set SS := PrimeGaps.singularSeries S.γ with hSS
  set P : ℝ := ∑ d ∈ S.V.divisors, (d : ℝ) ^ (σ - 1) with hP
  have hSS_pos : 0 < SS := by rw [hSS]; exact PrimeGaps.singularSeries_pos S
  have hlogz : 0 < Real.log z := Real.log_pos (by linarith)
  have hP1 : 1 ≤ P := by rw [hP]; exact one_le_sum_divisors_rpow S.V_pos.ne' _
  have hP0 : 0 < P := by linarith
  have hℓ : 0 ≤ ellV S.V := ellV_nonneg S.V
  have hc₁ := hCh₁ S.A₁ S.A₃
  have hc₂ := hCh₂ S.A₁ S.A₃
  set INN : ℝ := (2 * Ch₁ S.A₁ S.A₃ + 1) * SS * (1 + ellV S.V) +
    (2 * Ch₂ S.A₁ S.A₃ + 1) * (P / (σ ^ 2 * Real.log z)) with hINN
  -- The bracket of the Abel identity, from `slem_H_error_assembly_rpow` with
  -- `A = Ch₁ 𝔖 (1 + ℓ_V)` and `B = Ch₂ P / σ`.
  have hbracket : |S.H z - 𝔖 S.γ * Real.log z| +
      1 / Real.log z * ∫ (t : ℝ) in 1..z, |S.H t - 𝔖 S.γ * Real.log t| / t ≤ INN := by
    have hb := abel_bracket_le_rpow S z hz (A := Ch₁ S.A₁ S.A₃ * SS * (1 + ellV S.V))
      (B := Ch₂ S.A₁ S.A₃ * (P / σ)) (by positivity) (by positivity) hσ0 fun t ht ↦ by
        refine (hHasymp S t ht σ hσ0 hσ1).trans_eq ?_
        rw [hSS, hP]; ring
    have hσ2 : 1 / (σ ^ 2 * Real.log z) ≤ P / (σ ^ 2 * Real.log z) :=
      div_le_div_of_nonneg_right hP1 (by positivity)
    have hσ1' : 1 / Real.log z ≤ 1 / (σ ^ 2 * Real.log z) := by
      refine one_div_le_one_div_of_le (by positivity) ?_
      calc σ ^ 2 * Real.log z ≤ 1 * Real.log z := by
            gcongr; nlinarith only [hσ0, hσ1]
        _ = Real.log z := one_mul _
    have hrw : (2 * (Ch₂ S.A₁ S.A₃ * (P / σ)) / σ + 1) / Real.log z =
        2 * Ch₂ S.A₁ S.A₃ * (P / (σ ^ 2 * Real.log z)) + 1 / Real.log z := by
      field_simp
    rw [hrw] at hb
    rw [hINN]
    nlinarith only [hb, hσ2, hσ1', hSS_pos, hℓ, mul_nonneg hSS_pos.le hℓ]
  have hINN_nn : 0 ≤ INN := by rw [hINN]; positivity
  refine abs_partialSum_sub_integral_le_of_smooth S G M hM hbdd hlip z hz _ fun F hF hFgmax ↦ ?_
  have hGmax_nonneg : 0 ≤ Gmax F := le_trans (abs_nonneg _) ((Gmax_bounds F hF (t := (0 : ℝ))
      (by constructor <;> norm_num)).1)
  calc _ ≤ Gmax F * (|S.H z - 𝔖 S.γ * Real.log z| +
          1 / Real.log z * ∫ (t : ℝ) in 1..z, |S.H t - 𝔖 S.γ * Real.log t| / t) :=
        partial_sum_abel S F hF z hz
    _ ≤ Gmax F * INN := mul_le_mul_of_nonneg_left hbracket hGmax_nonneg
    _ ≤ (2 * M) * INN := mul_le_mul_of_nonneg_right hFgmax hINN_nn

/-- **Truncated sieve sum bound from a pointwise `A + B t^{-σ}` bound.** Evaluating the hypothesis
at `t = ⌈z⌉₊ + 1 ∈ [z, z ^ 2]`, `∑_{d ≤ ⌈z⌉₊} S.h d ≤ 2 𝔖 log z + A + B z^{-σ}`. -/
private theorem sum_h_range_ceil_succ_le_rpow (S : SieveDatum) (z : ℝ) (hz : 2 ≤ z)
    {A B σ : ℝ} (hB : 0 ≤ B) (hσ : 0 < σ)
    (hH : ∀ t : ℝ, 2 ≤ t → |S.H t - 𝔖 S.γ * Real.log t| ≤ A + B * t ^ (-σ)) :
    ∑ d ∈ Finset.range (⌈z⌉₊ + 1), S.h d ≤
      2 * PrimeGaps.singularSeries S.γ * Real.log z + A + B * z ^ (-σ) := by
  have h𝔰pos : 0 < PrimeGaps.singularSeries S.γ := PrimeGaps.singularSeries_pos S
  set t : ℝ := ((⌈z⌉₊ + 1 : ℕ) : ℝ) with htdef
  have hzc : z ≤ (⌈z⌉₊ : ℝ) := Nat.le_ceil z
  have hceil_lt : (⌈z⌉₊ : ℝ) < z + 1 := Nat.ceil_lt_add_one (by linarith)
  have hzt : z ≤ t := by rw [htdef]; push_cast; linarith
  have ht2 : (2 : ℝ) ≤ t := by linarith
  have htpos : (0 : ℝ) < t := by linarith
  have hBeq : ∑ d ∈ Finset.range (⌈z⌉₊ + 1), S.h d = S.H t := by
    unfold SieveDatum.H
    rw [htdef, Nat.ceil_natCast, Finset.sum_filter]
    refine Finset.sum_congr rfl fun d hd ↦ ?_
    rw [Finset.mem_range] at hd
    split_ifs with hcond
    · rfl
    · rcases Nat.eq_zero_or_pos d with rfl | hd0
      · exact sieveDatum_h_zero S
      · exact absurd ⟨hd0, by exact_mod_cast hd⟩ hcond
  have htz2 : t ≤ z ^ 2 := by
    have hfac : (0 : ℝ) ≤ (z - 2) * (z + 1) := mul_nonneg (by linarith) (by linarith)
    rw [htdef]; push_cast; linarith only [hceil_lt, hz, hfac]
  have hlogt : Real.log t ≤ 2 * Real.log z :=
    calc Real.log t ≤ Real.log (z ^ 2) := Real.log_le_log htpos htz2
      _ = 2 * Real.log z := by rw [Real.log_pow]; push_cast; ring
  have htpow : t ^ (-σ) ≤ z ^ (-σ) :=
    Real.rpow_le_rpow_of_nonpos (by linarith) hzt (by linarith)
  have hHb := (abs_le.mp (hH t ht2)).2
  rw [hBeq]
  linarith only [hHb, mul_le_mul_of_nonneg_left hlogt h𝔰pos.le,
    mul_le_mul_of_nonneg_left htpow hB]

/-- **`k`-fold partial summation, Euler-product error.** For `z ≥ 2` and `0 < σ ≤ 1/4`, peeling the
`n` coordinates of `sieveE` one at a time with `S1_partial_sum_sharp_rpow` gives
`|sieveE S z F n - sieveE S z F 0| ≤ n Bc^{n-1} PE` with
`Bc = 2 𝔖 log z + Ch₁ 𝔖 (1 + ℓ_V) + Ch₂ P_σ(V) / (σ² log z)` and
`PE = 2 (3 Fmax²) (Cs₁ 𝔖 (1 + ℓ_V) + Cs₂ P_σ(V) / (σ² log z))`, where
`P_σ(V) = ∑_{d ∣ V} d^{σ-1}`. This is `sieveDatum_kfold_partial_sum` with `τ(V)` replaced by
`P_σ(V)`. -/
theorem sieveDatum_kfold_partial_sum_rpow : ∃ Cs₁ Cs₂ Ch₁ Ch₂ : ℝ → ℝ → ℝ,
      (∀ A₁ A₃ : ℝ, 0 < Cs₁ A₁ A₃) ∧ (∀ A₁ A₃ : ℝ, 0 < Cs₂ A₁ A₃) ∧
        (∀ A₁ A₃ : ℝ, 0 < Ch₁ A₁ A₃) ∧ (∀ A₁ A₃ : ℝ, 0 < Ch₂ A₁ A₃) ∧
      ∀ {n : ℕ} (S : SieveDatum) (F : EuclideanSpace ℝ (Fin n) → ℝ),
        ContDiff ℝ (⊤ : ℕ∞) F → Function.support F ⊆ 𝓡 n → ∀ z : ℝ, 2 ≤ z →
          ∀ σ : ℝ, 0 < σ → σ ≤ 1 / 4 →
          |sieveE S z F n - sieveE S z F 0| ≤ (n : ℝ) *
              (2 * PrimeGaps.singularSeries S.γ * Real.log z +
                  Ch₁ S.A₁ S.A₃ * PrimeGaps.singularSeries S.γ * (1 + ellV S.V) +
                  Ch₂ S.A₁ S.A₃ * ((∑ d ∈ S.V.divisors, (d : ℝ) ^ (σ - 1)) /
                    (σ ^ 2 * Real.log z))) ^ (n - 1) *
              (2 * (3 * MaynardSmoothY.Fmax F ^ 2) *
                  (Cs₁ S.A₁ S.A₃ * PrimeGaps.singularSeries S.γ * (1 + ellV S.V) +
                      Cs₂ S.A₁ S.A₃ * ((∑ d ∈ S.V.divisors, (d : ℝ) ^ (σ - 1)) /
                        (σ ^ 2 * Real.log z)))) := by
  classical
  obtain ⟨Cs₁, Cs₂, hCs₁, hCs₂, hsharp⟩ := S1_partial_sum_sharp_rpow
  obtain ⟨Ch₁, Ch₂, hCh₁, hCh₂, hHasymp⟩ := PrimeGaps.slem_H_error_assembly_rpow
  refine ⟨Cs₁, Cs₂, Ch₁, Ch₂, hCs₁, hCs₂, hCh₁, hCh₂, ?_⟩
  intro n S F hF hsupp z hz σ hσ0 hσ1
  set 𝔰 : ℝ := PrimeGaps.singularSeries S.γ with h𝔰
  set P : ℝ := ∑ d ∈ S.V.divisors, (d : ℝ) ^ (σ - 1) with hP
  set Fm : ℝ := MaynardSmoothY.Fmax F ^ 2 with hFm
  have hz1 : (1 : ℝ) < z := by linarith
  have hlogz : 0 < Real.log z := Real.log_pos hz1
  have h𝔰pos : 0 < 𝔰 := PrimeGaps.singularSeries_pos S
  have hP1 : 1 ≤ P := by rw [hP]; exact one_le_sum_divisors_rpow S.V_pos.ne' _
  have hP0 : 0 < P := by linarith
  have hFmnn : 0 ≤ Fm := by rw [hFm]; positivity
  have hℓ : 0 ≤ ellV S.V := ellV_nonneg S.V
  have hc₁ := hCh₁ S.A₁ S.A₃
  have hc₂ := hCh₂ S.A₁ S.A₃
  set PE : ℝ := 2 * (3 * Fm) * (Cs₁ S.A₁ S.A₃ * 𝔰 * (1 + ellV S.V) +
      Cs₂ S.A₁ S.A₃ * (P / (σ ^ 2 * Real.log z))) with hPEdef
  set Bc : ℝ := 2 * 𝔰 * Real.log z + Ch₁ S.A₁ S.A₃ * 𝔰 * (1 + ellV S.V) +
      Ch₂ S.A₁ S.A₃ * (P / (σ ^ 2 * Real.log z)) with hBcdef
  have hs₁ := hCs₁ S.A₁ S.A₃
  have hs₂ := hCs₂ S.A₁ S.A₃
  have hPEnn : 0 ≤ PE := by rw [hPEdef]; positivity
  have h𝔰logz_le_Bc : 𝔰 * Real.log z ≤ Bc := by
    have t1 : 0 ≤ Ch₁ S.A₁ S.A₃ * 𝔰 * (1 + ellV S.V) := by positivity
    have t2 : 0 ≤ Ch₂ S.A₁ S.A₃ * (P / (σ ^ 2 * Real.log z)) := by positivity
    rw [hBcdef]
    linarith only [mul_pos h𝔰pos hlogz, t1, t2]
  have hBcnn : 0 ≤ Bc := le_trans (mul_nonneg h𝔰pos.le hlogz.le) h𝔰logz_le_Bc
  have hBsum_le : ∑ d ∈ Finset.range (⌈z⌉₊ + 1), S.h d ≤ Bc := by
    have hb := sum_h_range_ceil_succ_le_rpow S z hz (A := Ch₁ S.A₁ S.A₃ * 𝔰 * (1 + ellV S.V))
      (B := Ch₂ S.A₁ S.A₃ * (P / σ)) (by positivity) hσ0 fun t ht ↦ by
        refine (hHasymp S t ht σ hσ0 hσ1).trans_eq ?_
        rw [h𝔰, hP]; ring
    have hzσ : z ^ (-σ) ≤ 1 / (σ * Real.log z) := rpow_neg_le_one_div_mul_log hz1 hσ0
    have hrw : Ch₂ S.A₁ S.A₃ * (P / σ) * (1 / (σ * Real.log z)) =
        Ch₂ S.A₁ S.A₃ * (P / (σ ^ 2 * Real.log z)) := by
      field_simp
    rw [hBcdef]
    linarith only [hb, mul_le_mul_of_nonneg_left hzσ
      (by positivity : 0 ≤ Ch₂ S.A₁ S.A₃ * (P / σ)), hrw]
  have hperprefix : ∀ (m : ℕ), m < n → ∀ u : Fin m → ℕ,
      |(∑ d ∈ Finset.range ⌈z⌉₊ with (0 : ℕ) < d ∧ (↑d : ℝ) < z,
            S.h d * layerG z F u (Real.log ↑d / Real.log z)) -
        𝔰 * Real.log z * ∫ s in (0 : ℝ)..1, layerG z F u s| ≤ PE := by
    intro m hm u
    have hbdd_lip := S1_layerG_bdd_lip hm z F hF hsupp u
    have hMnn : (0 : ℝ) ≤ 3 * Fm := by rw [hFm]; positivity
    have hGbdd : ∀ x ∈ Set.Icc (0 : ℝ) 1, |layerG z F u x| ≤ 3 * Fm := fun x hx ↦ by
      rw [hFm]; linarith only [hbdd_lip.1 x hx, sq_nonneg (MaynardSmoothY.Fmax F)]
    have hGlip : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
        |layerG z F u x - layerG z F u y| ≤ (3 * Fm) * |x - y| := by
      rw [hFm]; exact hbdd_lip.2
    rw [hPEdef, h𝔰, hP]
    exact hsharp S (layerG z F u) (3 * Fm) hMnn hGbdd hGlip z hz σ hσ0 hσ1
  have hstep : ∀ (m : ℕ), m < n →
      |sieveE S z F (m + 1) - sieveE S z F m| ≤ Bc ^ (n - 1) * PE := fun m hm ↦
    sieveE_layer_step_le S F hF hsupp z hz Bc PE hBcnn hPEnn hBsum_le h𝔰logz_le_Bc m hm
      (hperprefix m hm)
  rw [← Finset.sum_range_sub (fun m ↦ sieveE S z F m)]
  calc |∑ m ∈ Finset.range n, (sieveE S z F (m + 1) - sieveE S z F m)|
      ≤ ∑ m ∈ Finset.range n, |sieveE S z F (m + 1) - sieveE S z F m| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ ∈ Finset.range n, Bc ^ (n - 1) * PE :=
        Finset.sum_le_sum fun m hm ↦ hstep m (Finset.mem_range.mp hm)
    _ = (n : ℝ) * Bc ^ (n - 1) * PE := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

end PrimeGaps
