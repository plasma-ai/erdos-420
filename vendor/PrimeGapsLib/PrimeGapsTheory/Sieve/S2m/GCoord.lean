/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.MeasureTheory.Order.Group.Lattice
public import PrimeGapsTheory.Arithmetic.DivisorTails
public import PrimeGapsTheory.Arithmetic.GammaDensity
public import PrimeGapsTheory.Sieve.Common.SieveDatumEval
public import PrimeGapsTheory.Sieve.Common.SieveDatumEval.EulerProductError
public import PrimeGapsTheory.Sieve.PermissibleSupport.ModulusEulerFactor

import PrimeGapsTheory.Tactic.PaperTag

/-!
# Partial summation in a g-weighted coordinate

Estimates the one-dimensional partial sum with the Maynard g-weight.

## Main results

* `sharp_partial_sum`: Partial summation of `S.h` against a `C¹` test function.
* `sum_h_eq_muSq_g`: The Maynard datum's `h`-weight is `μ²/g` on integers coprime to `Q`.
* `lem_S2m_g_coord`: Approximates the g-weighted coordinate sum by its integral main term.
-/

@[expose] public section

open scoped ArithmeticFunction.Moebius
open scoped ArithmeticFunction.detotient
open scoped Finset

namespace PrimeGaps

/-- Partial summation against a `C¹` test function: `∑_{0 < d < z} S.h d * G (log d / log z)`
differs from `𝔖(S.γ) * log z * ∫₀¹ G` by an explicit error in `ellV S.V` and the Euler product
`P_σ(V) = ∑_{d ∣ V} d^{σ-1}` over `σ² log z`, for any `0 < σ ≤ 1/4`, with constants depending only
on `S.A₁` and `S.A₃`. (Upstream, the second error is
`τ(V) (z^{-1/8} log (2 V z) + log (2 V) / log z)`, which is not small for a modulus `V` with many
prime factors.) -/
theorem sharp_partial_sum : ∃ C₁ C₂ : ℝ → ℝ → ℝ,
      (∀ A₁ A₃ : ℝ, 0 ≤ C₁ A₁ A₃) ∧ (∀ A₁ A₃ : ℝ, 0 ≤ C₂ A₁ A₃) ∧
      ∀ (S : SieveDatum) (G : ℝ → ℝ), ContDiff ℝ 1 G → ∀ (z : ℝ), 2 ≤ z →
        ∀ σ : ℝ, 0 < σ → σ ≤ 1 / 4 →
        |(∑ d ∈ (Finset.range ⌈z⌉₊).filter (fun d : ℕ ↦ 0 < d ∧ (d : ℝ) < z),
              S.h d * G (Real.log d / Real.log z)) -
            PrimeGaps.singularSeries S.γ * Real.log z * ∫ x in (0 : ℝ)..1, G x| ≤
          C₁ S.A₁ S.A₃ * PrimeGaps.singularSeries S.γ * (1 + ellV S.V) * Gmax G +
            C₂ S.A₁ S.A₃ * ((∑ d ∈ S.V.divisors, (d : ℝ) ^ (σ - 1)) / (σ ^ 2 * Real.log z)) *
              Gmax G := by
  obtain ⟨D₁, D₂, hD₁pos, hD₂pos, hSharp⟩ := S1_partial_sum_sharp_rpow
  refine ⟨fun A₁ A₃ ↦ 2 * D₁ A₁ A₃, fun A₁ A₃ ↦ 2 * D₂ A₁ A₃, ?_, ?_, ?_⟩
  · exact fun A₁ A₃ ↦ mul_nonneg (by norm_num) (hD₁pos A₁ A₃).le
  · exact fun A₁ A₃ ↦ mul_nonneg (by norm_num) (hD₂pos A₁ A₃).le
  intro S G hG z hz σ hσ0 hσ1
  have hM : 0 ≤ Gmax G := le_trans (abs_nonneg _)
      (Gmax_bounds G hG (Set.mem_Icc.mpr ⟨le_refl (0 : ℝ), zero_le_one⟩)).1
  have hbdd : ∀ x ∈ Set.Icc (0 : ℝ) 1, |G x| ≤ Gmax G := fun x hx ↦ (Gmax_bounds G hG hx).1
  have hlip : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1, |G x - G y| ≤ Gmax G * |x - y| := by
    intro x hx y hy
    have hdiff : ∀ w ∈ Set.Icc (0 : ℝ) 1, DifferentiableAt ℝ G w :=
      fun w _ ↦ (hG.differentiable (by norm_num)).differentiableAt
    have hbound : ∀ w ∈ Set.Icc (0 : ℝ) 1, ‖deriv G w‖ ≤ Gmax G := fun w hw ↦ by
      simpa only [Real.norm_eq_abs] using (Gmax_bounds G hG hw).2
    have h := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_deriv_le hdiff hbound hy hx
    rwa [Real.norm_eq_abs, Real.norm_eq_abs] at h
  refine (hSharp S G (Gmax G) hM hbdd hlip z hz σ hσ0 hσ1).trans_eq ?_
  ring

/-- The `h` -weighted sum of the Maynard sieve datum is
`∑_{0 < r < z, (r, Q) = 1} μ(r)² / g(r) * G (log r / log z)`. -/
theorem sum_h_eq_muSq_g (Q : ℕ) (h2 : 2 ∣ Q) (hQ : Squarefree Q) (G : ℝ → ℝ) (z : ℝ) :
    (∑ d ∈ (Finset.range ⌈z⌉₊).filter (fun d : ℕ ↦ 0 < d ∧ (↑d : ℝ) < z),
        (maynardSieveDatum Q h2 hQ).h d * G (Real.log ↑d / Real.log z))
      =
    (∑ r ∈ (Finset.range ⌈z⌉₊).filter (fun r : ℕ ↦ 0 < r ∧ (r : ℝ) < z ∧ Nat.Coprime r Q),
        (μ r : ℝ) ^ 2 / (g r : ℝ) * G (Real.log r / Real.log z)) := by
  have hbase : ((Finset.range ⌈z⌉₊).filter
          (fun r : ℕ ↦ 0 < r ∧ (r : ℝ) < z ∧ Nat.Coprime r Q)) =
        ((Finset.range ⌈z⌉₊).filter (fun d : ℕ ↦ 0 < d ∧ (↑d : ℝ) < z)).filter
            (fun r : ℕ ↦ Nat.Coprime r Q) := by
    rw [Finset.filter_filter]
    exact Finset.filter_congr fun x _ ↦ and_assoc.symm
  rw [hbase]
  conv_rhs => rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun d _ ↦ ?_
  have hh : (maynardSieveDatum Q h2 hQ).h d =
      (μ d : ℝ) ^ 2 * (maynardSieveDatum Q h2 hQ).gStar d := rfl
  rw [hh]
  by_cases hcop : Nat.Coprime d Q
  · rw [if_pos hcop]
    by_cases hsf : Squarefree d
    · rw [maynardSieveDatum_gStar_squarefree_coprime Q h2 hQ d hsf hcop]
      have hmu : (μ d : ℝ) ^ 2 = 1 := by
        exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hsf
      rw [hmu]; ring
    · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsf]; push_cast; ring
  · rw [if_neg hcop]
    by_cases hsf : Squarefree d
    · rw [maynardSieveDatum_gStar_not_coprime Q h2 hQ d hsf hcop]
      ring
    · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsf]; push_cast; ring

/-- `|𝔖(γ) - φ(Q) / Q| ≤ C * (φ(Q) / Q) * (1 / D₀ N)` for the Maynard datum's density, all large
`N` and every squarefree `Q` with `2 ∣ Q` and `primorial ⌊D₀ N⌋₊ ∣ Q`. -/
theorem singularSeries_maynard_asymptotic : ∃ C : ℝ, 0 < C ∧ ∃ x₀ : ℝ, ∀ (N : ℕ), x₀ ≤ (N : ℝ) →
      ∀ (Q : ℕ) (h2 : 2 ∣ Q) (hQ : Squarefree Q), primorial ⌊PrimeGaps.D₀ (N : ℝ)⌋₊ ∣ Q →
        |PrimeGaps.singularSeries (maynardSieveDatum Q h2 hQ).γ - (Q.totient : ℝ) / (Q : ℝ)| ≤
          C * ((Q.totient : ℝ) / (Q : ℝ)) *
              (1 / PrimeGaps.D₀ (N : ℝ)) := by
  exact singularSeries_maynardSieveDatum_γ_asymptotic

open scoped PrimeGaps.sieveTruncation in
/-- `2 ≤ R` for all large `N`. -/
theorem two_le_R (δ θ : ℝ) (hδ : δ ∈ Set.Ioo (0 : ℝ) (θ / 2)) :
    ∃ x₀ : ℝ, ∀ (N : ℕ), x₀ ≤ (N : ℝ) → 2 ≤ R := by
  obtain ⟨a, ha⟩ := Filter.eventually_atTop.mp (PrimeGaps.R_eventually_ge θ δ hδ.2 2)
  exact ⟨(a : ℝ), fun N hN ↦ ha N (by exact_mod_cast hN)⟩

open scoped PrimeGaps.sieveTruncation in
/-- The `rᵢ` -coordinate `g` -Mertens sum. There is a constant `C > 0` and a threshold `N₀` such
that for all `N ≥ N₀`, every modulus `Q` with `ModulusHyp CQ η N Q` and every `ContDiff ℝ 1` test
function `G`, the weighted sum `∑_{r < R, gcd(r,Q)=1} μ(r)²/g(r) · G(log r / log R)` lies within
`C·(φ(Q)/Q)·((log R / D₀)·|∫₀¹ G| + (log log N)·Gmax G)` of its main term
`(φ(Q)/Q)·(log R)·∫₀¹ G`. (Upstream, at `Q = W N`, the budget is `log D₀` in place of
`log log N`.) -/
@[pg_tag "bg246" "lem_S2m_g_coord"]
theorem lem_S2m_g_coord (δ θ : ℝ) (hδ : δ ∈ Set.Ioo (0 : ℝ) (θ / 2)) (CQ η : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ N → ∀ Q : ℕ, ModulusHyp CQ η N Q →
      ∀ (G : ℝ → ℝ), ContDiff ℝ 1 G →
        |(∑ r ∈ (Finset.range ⌈R⌉₊).filter (fun r : ℕ ↦ 0 < r ∧ (r : ℝ) < R ∧ Nat.Coprime r Q),
            (μ r : ℝ) ^ 2 / (g r : ℝ) * G (Real.log r / Real.log (R))) -
          (Q.totient : ℝ) / (Q : ℝ) * Real.log (R) * (∫ x in (0 : ℝ)..1, G x)| ≤
        C * ((Q.totient : ℝ) / (Q : ℝ)) * (Real.log (R) / PrimeGaps.D₀ (N : ℝ) *
                  |∫ x in (0 : ℝ)..1, G x| + Real.log (Real.log (N : ℝ)) * Gmax G) := by
  obtain ⟨B₁, B₂, hB₁, hB₂, hSharp⟩ := sharp_partial_sum
  obtain ⟨Cs, hCs, xs, hSing⟩ := singularSeries_maynard_asymptotic
  obtain ⟨xE, hE⟩ := ModulusHyp.exists_euler_regime δ θ hδ.2 CQ η
  obtain ⟨x2, h2R⟩ := two_le_R δ θ hδ
  set B₁' : ℝ := B₁ (1 / 2) 2 with hB₁'def
  set B₂' : ℝ := B₂ (1 / 2) 2 with hB₂'def
  have hB₁'nn : 0 ≤ B₁' := hB₁ (1 / 2) 2
  have hB₂'nn : 0 ≤ B₂' := hB₂ (1 / 2) 2
  set K₁ : ℝ := B₁' * (1 + Cs / 2) * (1 + |CQ|) with hK₁def
  set C : ℝ := max Cs (K₁ + B₂') with hCdef
  refine ⟨C, lt_of_lt_of_le hCs (le_max_left _ _),
    max xs (max xE (max x2 (Real.exp (Real.exp (Real.exp 2))))), ?_⟩
  intro N hN₀ Q hQ G hG
  simp only [max_le_iff] at hN₀
  obtain ⟨hxs, hxE, hx2, hNe⟩ := hN₀
  have hD : 2 ≤ PrimeGaps.D₀ (N : ℝ) := MaynardOffDiagonal.two_le_D0_of_large hNe
  obtain ⟨hσ0, hσ1, hLL1, hQE⟩ := hE N hxE
  obtain ⟨hell, hres⟩ := hQE Q hQ
  set S : SieveDatum := maynardSieveDatum Q (hQ.two_dvd hD) hQ.squarefree with hSdef
  set R₀ : ℝ := R with hRdef
  set singular : ℝ := PrimeGaps.singularSeries S.γ with hsingulardef
  set ratio : ℝ := (Q.totient : ℝ) / (Q : ℝ) with hratiodef
  set I : ℝ := ∫ x in (0 : ℝ)..1, G x with hIdef
  set Gsup : ℝ := Gmax G with hGsupdef
  set D₀ : ℝ := PrimeGaps.D₀ (N : ℝ) with hD₀def
  set LL : ℝ := Real.log (Real.log (N : ℝ)) with hLLdef
  set P : ℝ := ∑ d ∈ Q.divisors, (d : ℝ) ^ (1 / LL - 1) with hPdef
  have hR2 : 2 ≤ R₀ := h2R N hx2
  have hlogR_nonneg : 0 ≤ Real.log R₀ := Real.log_nonneg (by linarith)
  have hD₀_pos : 0 < D₀ := by linarith [(hD : (2 : ℝ) ≤ D₀)]
  have hGsup_nonneg : 0 ≤ Gsup := by
    rw [hGsupdef]; unfold Gmax; exact Real.iSup_nonneg fun t ↦ by positivity
  have hratio_nonneg : 0 ≤ ratio := by rw [hratiodef]; positivity
  have hsingular_pos : 0 < singular := PrimeGaps.singularSeries_pos S
  have hSharp' := hSharp S G hG R₀ hR2 (1 / LL) hσ0 hσ1
  rw [sum_h_eq_muSq_g Q (hQ.two_dvd hD) hQ.squarefree G R₀, maynardSieveDatum_A₁,
    maynardSieveDatum_A₃, maynardSieveDatum_V] at hSharp'
  have hSing'' : |singular - ratio| ≤ Cs * ratio * (1 / D₀) :=
    hSing N hxs Q (hQ.two_dvd hD) hQ.squarefree hQ.primorial_dvd
  have hbudget1 :
      |singular * Real.log R₀ * I - ratio * Real.log R₀ * I| ≤
        Cs * ratio * (Real.log R₀ / D₀ * |I|) := by
    have hfac : singular * Real.log R₀ * I - ratio * Real.log R₀ * I =
        (singular - ratio) * (Real.log R₀ * I) := by ring
    rw [hfac, abs_mul, abs_mul, abs_of_nonneg hlogR_nonneg]
    have hrhs : Cs * ratio * (Real.log R₀ / D₀ * |I|) =
        (Cs * ratio * (1 / D₀)) * (Real.log R₀ * |I|) := by ring
    rw [hrhs]
    exact mul_le_mul_of_nonneg_right hSing'' (mul_nonneg hlogR_nonneg (abs_nonneg I))
  have hterm1 : B₁' * singular * (1 + ellV Q) * Gsup ≤ K₁ * (ratio * LL * Gsup) := by
    have hSingle : singular - ratio ≤ Cs * ratio * (1 / D₀) := (le_abs_self _).trans hSing''
    have h1 : singular ≤ ratio * (1 + Cs / 2) := by
      have hCr : Cs * ratio * (1 / D₀) ≤ Cs * ratio * (1 / 2) :=
        mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le (by norm_num) hD) (by positivity)
      nlinarith [hSingle, hCr]
    calc B₁' * singular * (1 + ellV Q) * Gsup
        ≤ B₁' * (ratio * (1 + Cs / 2)) * ((1 + |CQ|) * LL) * Gsup := by
          gcongr
          linarith [ellV_nonneg Q]
      _ = K₁ * (ratio * LL * Gsup) := by rw [hK₁def]; ring
  have hterm2 : B₂' * (P / ((1 / LL) ^ 2 * Real.log R₀)) * Gsup ≤ B₂' * (ratio * LL * Gsup) := by
    calc B₂' * (P / ((1 / LL) ^ 2 * Real.log R₀)) * Gsup ≤ B₂' * (ratio * LL) * Gsup := by
          gcongr
      _ = B₂' * (ratio * LL * Gsup) := by ring
  have htri :
      |(∑ r ∈ (Finset.range ⌈R₀⌉₊).filter (fun r : ℕ ↦ 0 < r ∧ (r : ℝ) < R₀ ∧ Nat.Coprime r Q),
            (μ r : ℝ) ^ 2 / (g r : ℝ) * G (Real.log r / Real.log R₀)) -
          ratio * Real.log R₀ * I| ≤ |(∑ r ∈ (Finset.range ⌈R₀⌉₊).filter
              (fun r : ℕ ↦ 0 < r ∧ (r : ℝ) < R₀ ∧ Nat.Coprime r Q),
            (μ r : ℝ) ^ 2 / (g r : ℝ) * G (Real.log r / Real.log R₀)) -
            singular * Real.log R₀ * I| +
          |singular * Real.log R₀ * I - ratio * Real.log R₀ * I| :=
    abs_sub_le _ (singular * Real.log R₀ * I) _
  have hnn1 : 0 ≤ ratio * LL * Gsup :=
    mul_nonneg (mul_nonneg hratio_nonneg (by linarith)) hGsup_nonneg
  have hnn2 : 0 ≤ ratio * (Real.log R₀ / D₀ * |I|) :=
    mul_nonneg hratio_nonneg (mul_nonneg (div_nonneg hlogR_nonneg hD₀_pos.le) (abs_nonneg I))
  calc |(∑ r ∈ (Finset.range ⌈R₀⌉₊).filter (fun r : ℕ ↦ 0 < r ∧ (r : ℝ) < R₀ ∧ Nat.Coprime r Q),
            (μ r : ℝ) ^ 2 / (g r : ℝ) * G (Real.log r / Real.log R₀)) -
          ratio * Real.log R₀ * I| ≤
        (B₁' * singular * (1 + ellV Q) * Gsup +
          B₂' * (P / ((1 / LL) ^ 2 * Real.log R₀)) * Gsup) +
          Cs * ratio * (Real.log R₀ / D₀ * |I|) :=
        htri.trans (add_le_add hSharp' hbudget1)
    _ ≤ (K₁ * (ratio * LL * Gsup) + B₂' * (ratio * LL * Gsup)) +
          Cs * ratio * (Real.log R₀ / D₀ * |I|) :=
        add_le_add (add_le_add hterm1 hterm2) le_rfl
    _ = (K₁ + B₂') * (ratio * LL * Gsup) + Cs * (ratio * (Real.log R₀ / D₀ * |I|)) := by ring
    _ ≤ C * (ratio * LL * Gsup) + C * (ratio * (Real.log R₀ / D₀ * |I|)) :=
        add_le_add (mul_le_mul_of_nonneg_right (le_max_right _ _) hnn1)
          (mul_le_mul_of_nonneg_right (le_max_left _ _) hnn2)
    _ = C * ratio * (Real.log R₀ / D₀ * |I| + LL * Gsup) := by ring

end PrimeGaps
