/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsTheory.Sieve.S1.ApplyPartialSum
public import PrimeGapsTheory.Variational.Marginal.DecoupledSeparate
public import PrimeGapsTheory.Variational.Marginal.Infra

/-!
# Approximation of the inner sum `Ydisc`

Evaluates the one-dimensional inner sum `Ydisc` uniformly in its free coordinates.

## Main definitions

*  `sigmaPt`: The logarithmically normalized free-coordinate point.
*  `Gsigma`: The one-dimensional profile obtained by freezing the free coordinates.

## Main results

*  `Ydisc_approx`: Approximates `Ydisc` by the marginal profile with a uniform error bound.
-/

@[expose] public section

open scoped ArithmeticFunction.Moebius
open scoped Finset
open scoped Topology


namespace PrimeGaps

open MeasureTheory EuclideanSpace

variable {n : ℕ}

/-- Evaluation point of the free coordinates `σ`. -/
noncomputable def sigmaPt (z : ℝ) (σ : Fin n → ℕ) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun j ↦ Real.log (σ j) / Real.log z)

/-- The one-dimensional profile: `F` with the free coordinates frozen at `σ̃` and the isolated
coordinate `m` carrying the running scalar `s`. -/
noncomputable def Gsigma (m : Fin (n + 1)) (F : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) (z : ℝ)
    (σ : Fin n → ℕ) : ℝ → ℝ :=
  fun s ↦ F (insertLp m s (sigmaPt z σ))

/-- The `Ydisc` summand's point (`update (insertNth m 1 σ) m u`) coincides with
`insertLp m (log u / log z) σ̃`, so the `F` -value is `Gσ (log u / log z)`. -/
theorem F_update_eq_Gsigma (m : Fin (n + 1)) (F : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) (z : ℝ)
    (σ : Fin n → ℕ) (u : ℕ) :
    F (WithLp.toLp 2 (fun i ↦
        Real.log ((Function.update (Fin.insertNth m (1 : ℕ) σ : Fin (n + 1) → ℕ) m u) i : ℝ) /
          Real.log z)) = Gsigma m F z σ (Real.log u / Real.log z) := by
  have hfun : (fun i ↦
      Real.log ((Function.update (Fin.insertNth m (1 : ℕ) σ : Fin (n + 1) → ℕ) m u) i : ℝ) /
        Real.log z) =
      m.insertNth (Real.log u / Real.log z) (fun j ↦ Real.log (σ j) / Real.log z) := by
    funext i
    refine Fin.succAboveCases m ?_ ?_ i
    · rw [Function.update_self, Fin.insertNth_apply_same]
    · intro j
      rw [Function.update_of_ne (Fin.succAbove_ne m j),
          Fin.insertNth_apply_succAbove, Fin.insertNth_apply_succAbove]
  unfold Gsigma insertLp sigmaPt
  rw [WithLp.ofLp_toLp]
  exact congrArg F (congrArg (WithLp.toLp 2) hfun)

/-- `s ↦ insertLp m s t` is smooth (it is affine in `s` ). -/
theorem contDiff_insertLp_fixed (m : Fin (n + 1)) (t : EuclideanSpace ℝ (Fin n)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun s : ℝ ↦ insertLp m s t) := by
  have h := contDiff_insertLp_neg (n := n) m
  have hcomp : (fun s : ℝ ↦ insertLp m s t) =
      (fun p : EuclideanSpace ℝ (Fin n) × ℝ ↦ insertLp m (-p.2) p.1)
        ∘ (fun s : ℝ ↦ (t, -s)) := by
    funext s; simp
  rw [hcomp]
  exact h.comp (contDiff_const.prodMk contDiff_neg)

/-- `Gσ` is smooth (hence `ContDiff ℝ 1` ). -/
theorem Gsigma_contDiff (m : Fin (n + 1)) (F : EuclideanSpace ℝ (Fin (n + 1)) → ℝ)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (z : ℝ) (σ : Fin n → ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (Gsigma m F z σ) :=
  hF.comp (contDiff_insertLp_fixed m (sigmaPt z σ))

/-- `Gσ` is uniformly bounded by `Fmax F`. -/
theorem Gsigma_abs_le_Fmax (m : Fin (n + 1)) (F : EuclideanSpace ℝ (Fin (n + 1)) → ℝ)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hsupp : Function.support F ⊆ 𝓡 (n + 1)) (z : ℝ)
    (σ : Fin n → ℕ) (s : ℝ) :
    |Gsigma m F z σ s| ≤ MaynardSmoothY.Fmax F :=
  S1_abs_F_le_Fmax_global F hF hsupp _

/-- Coordinate `m` of `insertLp m s t` is `s`. -/
theorem insertLp_ofLp_same (m : Fin (n + 1)) (s : ℝ) (t : EuclideanSpace ℝ (Fin n)) :
    (insertLp m s t).ofLp m = s := by
  unfold insertLp
  rw [WithLp.ofLp_toLp, Fin.insertNth_apply_same]

/-- `Gσ` vanishes outside `Ioc 0 1`. -/
theorem Gsigma_vanish (m : Fin (n + 1)) (F : EuclideanSpace ℝ (Fin (n + 1)) → ℝ)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hsupp : Function.support F ⊆ 𝓡 (n + 1)) (z : ℝ)
    (σ : Fin n → ℕ) {s : ℝ} (hs : s ∉ Set.Ioc (0 : ℝ) 1) :
    Gsigma m F z σ s = 0 := by
  unfold Gsigma
  by_cases hmem : insertLp m s (sigmaPt z σ) ∈ 𝓡 (n + 1)
  · have hmem' := hmem
    rw [EuclideanSpace.mem_scaledStdSimplex_iff] at hmem
    obtain ⟨hnn, hsum⟩ := hmem
    have hcm : (insertLp m s (sigmaPt z σ)).ofLp m = s := insertLp_ofLp_same m s (sigmaPt z σ)
    have h0 : 0 ≤ s := hcm ▸ hnn m
    have h1 : s ≤ 1 := by
      have hle := Finset.single_le_sum
        (f := fun i ↦ (insertLp m s (sigmaPt z σ)).ofLp i) (fun i _ ↦ hnn i) (Finset.mem_univ m)
      rw [hcm] at hle; linarith
    have hs0 : s = 0 := by
      rcases eq_or_lt_of_le h0 with h | h
      exacts [h.symm, absurd ⟨h, h1⟩ hs]
    exact S1_boundary_vanish F hF hsupp hmem' (Or.inl ⟨m, by rw [hcm, hs0]⟩)
  · by_contra hne
    exact hmem (hsupp (Function.mem_support.mpr hne))

/-- `Gσ` vanishes for `s ≥ 1`. -/
theorem Gsigma_vanish_ge_one (m : Fin (n + 1)) (F : EuclideanSpace ℝ (Fin (n + 1)) → ℝ)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hsupp : Function.support F ⊆ 𝓡 (n + 1)) (z : ℝ)
    (σ : Fin n → ℕ) {s : ℝ} (hs : 1 ≤ s) :
    Gsigma m F z σ s = 0 := by
  unfold Gsigma
  by_cases hmem : insertLp m s (sigmaPt z σ) ∈ 𝓡 (n + 1)
  · have hmem' := hmem
    rw [EuclideanSpace.mem_scaledStdSimplex_iff] at hmem
    obtain ⟨hnn, hsum⟩ := hmem
    have hcm : (insertLp m s (sigmaPt z σ)).ofLp m = s := insertLp_ofLp_same m s (sigmaPt z σ)
    have hge : s ≤ ∑ i, (insertLp m s (sigmaPt z σ)).ofLp i := by
      have hle := Finset.single_le_sum
        (f := fun i ↦ (insertLp m s (sigmaPt z σ)).ofLp i) (fun i _ ↦ hnn i) (Finset.mem_univ m)
      rwa [hcm] at hle
    have hsum1 : ∑ i, (insertLp m s (sigmaPt z σ)).ofLp i = 1 := le_antisymm hsum (by linarith)
    exact S1_boundary_vanish F hF hsupp hmem' (Or.inr hsum1)
  · by_contra hne
    exact hmem (hsupp (Function.mem_support.mpr hne))

/-- `s ↦ insertLp m s t` is affine with slope `EuclideanSpace.single m 1`. -/
theorem insertLp_affine (m : Fin (n + 1)) (s : ℝ) (t : EuclideanSpace ℝ (Fin n)) :
    insertLp m s t = insertLp m 0 t + s • EuclideanSpace.single m (1 : ℝ) := by
  ext i
  refine Fin.succAboveCases m ?_ ?_ i
  · simp [insertLp_apply_same]
  · intro j
    simp [insertLp_apply_succAbove, (Fin.succAbove_ne m j)]

/-- Derivative of `Gσ`: the `m` -directional derivative of `F` at `insertLp m s σ̃`. -/
theorem Gsigma_hasDerivAt (m : Fin (n + 1)) (F : EuclideanSpace ℝ (Fin (n + 1)) → ℝ)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (z : ℝ) (σ : Fin n → ℕ) (s : ℝ) :
    HasDerivAt (Gsigma m F z σ)
      (fderiv ℝ F (insertLp m s (sigmaPt z σ)) (EuclideanSpace.single m (1 : ℝ))) s := by
  have hlin : HasDerivAt (fun s : ℝ ↦ insertLp m s (sigmaPt z σ))
      (EuclideanSpace.single m (1 : ℝ)) s := by
    have h1 : HasDerivAt (fun s : ℝ ↦ s • EuclideanSpace.single m (1 : ℝ))
        (EuclideanSpace.single m (1 : ℝ)) s := by
      simpa using (hasDerivAt_id s).smul_const (EuclideanSpace.single m (1 : ℝ))
    have h2 := h1.const_add (insertLp m 0 (sigmaPt z σ))
    have haff : (fun s : ℝ ↦ insertLp m s (sigmaPt z σ)) =
        fun s : ℝ ↦ insertLp m 0 (sigmaPt z σ) + s • EuclideanSpace.single m (1 : ℝ) := by
      funext s; exact insertLp_affine m s (sigmaPt z σ)
    rw [haff]; exact h2
  have hFd : HasFDerivAt F (fderiv ℝ F (insertLp m s (sigmaPt z σ))) (insertLp m s (sigmaPt z σ)) :=
    (hF.differentiable (by simp)).differentiableAt.hasFDerivAt
  exact hFd.comp_hasDerivAt s hlin

/-- `Gmax Gσ ≤ Fmax F`. -/
theorem Gmax_Gsigma_le (m : Fin (n + 1)) (F : EuclideanSpace ℝ (Fin (n + 1)) → ℝ)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hsupp : Function.support F ⊆ 𝓡 (n + 1)) (z : ℝ)
    (σ : Fin n → ℕ) :
    Gmax (Gsigma m F z σ) ≤ MaynardSmoothY.Fmax F := by
  have hFnn : 0 ≤ MaynardSmoothY.Fmax F := MaynardSmoothY.Fmax_nonneg F hF
  have hbdd := MaynardSmoothY.abs_F_bddAbove F hF
  have hpt : ∀ s : ℝ, |Gsigma m F z σ s| + |deriv (Gsigma m F z σ) s| ≤ MaynardSmoothY.Fmax F := by
    intro s
    set pt : EuclideanSpace ℝ (Fin (n + 1)) := insertLp m s (sigmaPt z σ) with hpt
    have hderiv : deriv (Gsigma m F z σ) s = fderiv ℝ F pt (EuclideanSpace.single m (1 : ℝ)) :=
      (Gsigma_hasDerivAt m F hF z σ s).deriv
    by_cases hin : ∀ i, pt i ∈ Set.Icc (0 : ℝ) 1
    · have hmem : |F pt| + ∑ i : Fin (n + 1), |fderiv ℝ F pt (EuclideanSpace.single i 1)| ∈
          ((fun w : EuclideanSpace ℝ (Fin (n + 1)) ↦
            |F w| + ∑ i, |fderiv ℝ F w (EuclideanSpace.single i 1)|) ''
            {w : EuclideanSpace ℝ (Fin (n + 1)) | ∀ i, w i ∈ Set.Icc (0 : ℝ) 1}) :=
          ⟨pt, hin, rfl⟩
      have hle : |F pt| + ∑ i, |fderiv ℝ F pt (EuclideanSpace.single i 1)| ≤
          MaynardSmoothY.Fmax F := le_csSup hbdd hmem
      have hsingle : |fderiv ℝ F pt (EuclideanSpace.single m (1 : ℝ))| ≤
          ∑ i, |fderiv ℝ F pt (EuclideanSpace.single i 1)| :=
        Finset.single_le_sum (f := fun i ↦ |fderiv ℝ F pt (EuclideanSpace.single i 1)|)
          (fun i _ ↦ abs_nonneg _) (Finset.mem_univ m)
      have hGeq : Gsigma m F z σ s = F pt := rfl
      rw [hderiv, hGeq]; linarith
    · have hptR : pt ∉ 𝓡 (n + 1) := by
        intro hR
        obtain ⟨hnn, hsum⟩ := EuclideanSpace.mem_scaledStdSimplex_iff.mp hR
        exact hin (fun i ↦ ⟨hnn i, le_trans (Finset.single_le_sum
          (f := fun j ↦ pt j) (fun j _ ↦ hnn j) (Finset.mem_univ i)) hsum⟩)
      have hFev : F =ᶠ[𝓝 pt] 0 := by
        refine Filter.eventuallyEq_of_mem
          ((isClosed_scaledStdSimplex.isOpen_compl).mem_nhds hptR) ?_
        intro w hw
        by_contra hne
        exact hw (hsupp (Function.mem_support.mpr hne))
      have hF0 : F pt = 0 := by simpa using hFev.eq_of_nhds
      have hfd0 : fderiv ℝ F pt = 0 := by
        rw [hFev.fderiv_eq]; simp
      have hGeq : Gsigma m F z σ s = F pt := rfl
      rw [hderiv, hGeq, hF0, hfd0]; simp [hFnn]
  refine ciSup_le ?_
  exact fun t ↦ hpt t.1

/-- The interval integral of `Gσ` is the marginal `Tm` at the frozen point `σ̃`. -/
theorem Gsigma_integral_eq_Tm (m : Fin (n + 1)) (F : EuclideanSpace ℝ (Fin (n + 1)) → ℝ)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hsupp : Function.support F ⊆ 𝓡 (n + 1)) (z : ℝ)
    (σ : Fin n → ℕ) :
    ∫ x in (0 : ℝ)..1, Gsigma m F z σ x = Tm m F (sigmaPt z σ) := by
  have hTm : Tm m F (sigmaPt z σ) = ∫ s, Gsigma m F z σ s := rfl
  rw [hTm, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
      MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero]
  exact fun s hs ↦ Gsigma_vanish m F hF hsupp z σ hs

/-- At the reindexed argument, `Ydisc` equals the filtered sum with weight
`S.h u = μ²/φ · [coprime]` and profile `Gσ`. -/
theorem Ydisc_eq_filtered (R : ℝ) (W : ℕ) (m : Fin (n + 1))
    (F : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hsupp : Function.support F ⊆ 𝓡 (n + 1))
    (hR : 1 < R) (σ : Fin n → ℕ) (S : SieveDatum)
    (hSh : ∀ u : ℕ, S.h u = if (u.Coprime W ∧ Squarefree u) then (1 / (u.totient : ℝ)) else 0) :
    Ydisc R W F m (Fin.insertNth m 1 σ) = ∑ d ∈ (Finset.range ⌈R⌉₊).filter
            (fun d : ℕ ↦ 0 < d ∧ (d : ℝ) < R),
          S.h d * Gsigma m F R σ (Real.log d / Real.log R) := by
  set z := R with hz
  have hz0 : (0 : ℝ) < z := by linarith
  have hlogz : 0 < Real.log z := Real.log_pos hR
  have hsummand : ∀ u : ℕ, (if (u.Coprime W ∧ Squarefree u) then (1 / (u.totient : ℝ)) *
          F (WithLp.toLp 2 (fun i ↦
              Real.log ((Function.update (Fin.insertNth m (1 : ℕ) σ : Fin (n + 1) → ℕ) m u) i : ℝ) /
              Real.log z)) else 0) = S.h u * Gsigma m F z σ (Real.log u / Real.log z) := by
    intro u
    rw [F_update_eq_Gsigma m F z σ u, hSh u]
    split <;> ring
  have hYd : Ydisc R W F m (Fin.insertNth m 1 σ) =
      ∑' u : ℕ, S.h u * Gsigma m F z σ (Real.log u / Real.log z) := by
    unfold Ydisc
    exact tsum_congr hsummand
  rw [hYd]
  apply tsum_eq_sum
  intro u hu
  rcases Nat.eq_zero_or_pos u with hu0 | hupos
  · subst hu0
    rw [hSh 0, if_neg (by rintro ⟨_, hsf⟩; exact not_squarefree_zero hsf), zero_mul]
  · have huz : z ≤ (u : ℝ) := by
      by_contra hlt
      push Not at hlt
      exact hu (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr
        (by exact_mod_cast lt_of_lt_of_le hlt (Nat.le_ceil z)), hupos, hlt⟩)
    have hs1 : 1 ≤ Real.log u / Real.log z := by
      rw [le_div_iff₀ hlogz, one_mul]
      exact Real.log_le_log hz0 huz
    rw [Gsigma_vanish_ge_one m F hF hsupp z σ hs1, mul_zero]

-- For the γ_Q datum, `Ydisc` at the reindexed argument equals `(φ(Q)/Q)·log R·Tm σ̃`
-- up to `O((φ(Q)/Q)·log log N·Fmax)`, uniformly in `σ`.
open scoped PrimeGaps.sieveTruncation in
/-- `Ydisc R Q F m (Fin.insertNth m 1 σ)` agrees with
`(φ(Q) / Q) * log R * Tm m F (sigmaPt R σ)` up to
`C * (φ(Q) / Q) * log log N * Fmax F`, uniformly in the free coordinates `σ` and in the moduli `Q`
with `ModulusHyp CQ η N Q`. (Upstream, at `Q = W N`, the budget is `log D₀` in place of
`log log N`.) -/
theorem Ydisc_approx {n : ℕ} (δ θ : ℝ) (hδ : δ ∈ Set.Ioo (0 : ℝ) (θ / 2)) (CQ η : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ N → ∀ Q : ℕ, ModulusHyp CQ η N Q →
      ∀ (F : EuclideanSpace ℝ (Fin (n + 1)) → ℝ), ContDiff ℝ (⊤ : ℕ∞) F →
        Function.support F ⊆ 𝓡 (n + 1) → ∀ (m : Fin (n + 1)) (σ : Fin n → ℕ),
        |Ydisc (R) Q F m (Fin.insertNth m 1 σ) - (Q.totient : ℝ) /
          (Q : ℝ) * Real.log (R) * Tm m F (sigmaPt (R) σ)| ≤
        C * ((Q.totient : ℝ) / (Q : ℝ)) *
            Real.log (Real.log (N : ℝ)) * MaynardSmoothY.Fmax F := by
  classical
  obtain ⟨B₁, B₂, hB₁, hB₂, hSharp⟩ := sharp_partial_sum
  obtain ⟨xE, hE⟩ := ModulusHyp.exists_euler_regime δ θ hδ.2 CQ η
  obtain ⟨x2, h2R⟩ := two_le_R δ θ hδ
  set B₁' : ℝ := B₁ (1 / 2) 0 with hB₁'def
  set B₂' : ℝ := B₂ (1 / 2) 0 with hB₂'def
  have hB₁'nn : 0 ≤ B₁' := hB₁ _ _
  have hB₂'nn : 0 ≤ B₂' := hB₂ _ _
  set C : ℝ := B₁' * (1 + |CQ|) + B₂' with hCdef
  refine ⟨C, by positivity, max xE x2, ?_⟩
  intro N hN₀ Q hQ F hF hsupp m σ
  have hxE : xE ≤ (N : ℝ) := le_trans (le_max_left _ _) hN₀
  have hx2 : x2 ≤ (N : ℝ) := le_trans (le_max_right _ _) hN₀
  obtain ⟨hσ0, hσ1, hLL1, hQE⟩ := hE N hxE
  obtain ⟨hell, hres⟩ := hQE Q hQ
  obtain ⟨S, hSγ, hSV, hSA₁, hSA₃⟩ := S1_WSieveDatum Q hQ.pos hQ.squarefree
  obtain ⟨h𝔖eq, hSh2, hSh3⟩ := S1_datum_facts Q hQ.ne_zero S hSγ hSV
  set Rt : ℝ := R with hRdef
  set ratio : ℝ := (Q.totient : ℝ) / (Q : ℝ) with hratiodef
  set LL : ℝ := Real.log (Real.log (N : ℝ)) with hLLdef
  set P : ℝ := ∑ d ∈ Q.divisors, (d : ℝ) ^ (1 / LL - 1) with hPdef
  set Fm : ℝ := MaynardSmoothY.Fmax F with hFmdef
  set G : ℝ → ℝ := Gsigma m F Rt σ with hGdef
  have hR2 : 2 ≤ Rt := h2R N hx2
  have hR1 : 1 < Rt := by linarith
  have hratio_nn : 0 ≤ ratio := by rw [hratiodef]; positivity
  have hFm_nn : 0 ≤ Fm := MaynardSmoothY.Fmax_nonneg F hF
  have hg : Gmax G ≤ Fm := by rw [hGdef, hFmdef]; exact Gmax_Gsigma_le m F hF hsupp Rt σ
  have hgnn : 0 ≤ Gmax G := by
    rw [hGdef]; unfold Gmax; exact Real.iSup_nonneg (fun t ↦ by positivity)
  have hSh : ∀ u : ℕ, S.h u = if (u.Coprime Q ∧ Squarefree u) then (1 /
        (u.totient : ℝ)) else 0 := by
    intro u
    by_cases hcs : u.Coprime Q ∧ Squarefree u
    · rw [if_pos hcs, hSh2 u hcs.2 hcs.1]
      have hμ : (μ u : ℝ) ^ 2 = 1 := by
        exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hcs.2
      rw [hμ]
    · rw [if_neg hcs, hSh3 u (fun h ↦ hcs ⟨h.2, h.1⟩)]
  rw [Ydisc_eq_filtered Rt Q m F hF hsupp hR1 σ S hSh]
  have hsharp := hSharp S G ((Gsigma_contDiff m F hF Rt σ).of_le (by exact_mod_cast le_top)) Rt hR2
    (1 / LL) hσ0 hσ1
  have hInt : ∫ x in (0 : ℝ)..1, G x = Tm m F (sigmaPt Rt σ) := by
    rw [hGdef]; exact Gsigma_integral_eq_Tm m F hF hsupp Rt σ
  rw [h𝔖eq, hInt, hSV, hSA₁, hSA₃, ← hB₁'def, ← hB₂'def] at hsharp
  refine le_trans hsharp ?_
  have hterm1 : B₁' * ratio * (1 + ellV Q) * Gmax G ≤ B₁' * (1 + |CQ|) * (ratio * LL * Fm) :=
    calc B₁' * ratio * (1 + ellV Q) * Gmax G ≤ B₁' * ratio * ((1 + |CQ|) * LL) * Fm := by
          gcongr
      _ = B₁' * (1 + |CQ|) * (ratio * LL * Fm) := by ring
  have hterm2 : B₂' * (P / ((1 / LL) ^ 2 * Real.log Rt)) * Gmax G ≤ B₂' * (ratio * LL * Fm) :=
    calc B₂' * (P / ((1 / LL) ^ 2 * Real.log Rt)) * Gmax G ≤ B₂' * (ratio * LL) * Fm := by
          gcongr
      _ = B₂' * (ratio * LL * Fm) := by ring
  calc B₁' * ratio * (1 + ellV Q) * Gmax G + B₂' * (P / ((1 / LL) ^ 2 * Real.log Rt)) * Gmax G
      ≤ B₁' * (1 + |CQ|) * (ratio * LL * Fm) + B₂' * (ratio * LL * Fm) :=
        add_le_add hterm1 hterm2
    _ = C * ratio * LL * Fm := by rw [hCdef]; ring

end PrimeGaps
