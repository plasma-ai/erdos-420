module

public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
public import Mathlib.Analysis.Complex.AbsMax
public import Mathlib.Analysis.Complex.BorelCaratheodory
public import Mathlib.Analysis.Complex.BranchLogRoot
public import Mathlib.Analysis.Complex.JensenFormula
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.Normed.Module.Connected

/-!
# The local formula for a logarithmic derivative

If `f` is analytic on `closedBall c R` with `‖f‖ ≤ M ‖f c‖` there, then on a
smaller ball `f' / f` differs from the sum of `1 / (z - ρ)` over the zeros `ρ`
of `f` near `c` by `O(log M)`. This is Landau's lemma, with radii whose ratios
may be close to one; the constant depends only on the radii.
-/

@[expose] public section

namespace Erdos420

open Metric MeromorphicOn

/-- Factor out the zeros of `f` in `closedBall c r`: on `ball c R`, `f` is the product of
`(z - u) ^ m` over these zeros `u` (with multiplicity `m`) and a holomorphic function `g`
without zeros on `closedBall c r`. -/
lemma exists_eq_prod_mul {f : ℂ → ℂ} {c : ℂ} {r R : ℝ} (hr : 0 ≤ r) (hrR : r < R)
    (hf : AnalyticOnNhd ℂ f (closedBall c R)) (hfc : f c ≠ 0) :
    ∃ (T : Finset ℂ) (g : ℂ → ℂ), (divisor f (closedBall c r)).support ⊆ T ∧
      DifferentiableOn ℂ g (ball c R) ∧ (∀ z ∈ closedBall c r, g z ≠ 0) ∧
      ∀ z ∈ ball c R,
        f z = (∏ u ∈ T, (z - u) ^ (divisor f (closedBall c r) u).toNat) * g z := by
  set D := divisor f (closedBall c R)
  set D₂ := divisor f (closedBall c r)
  have hsub : closedBall c r ⊆ closedBall c R := closedBall_subset_closedBall hrR.le
  have hfin : D.support.Finite := D.finiteSupport (isCompact_closedBall c R)
  set T := hfin.toFinset
  -- `D₂` agrees with `D` on `closedBall c r` and vanishes elsewhere
  have hD₂eq : ∀ u ∈ closedBall c r, D₂ u = D u := fun u hu ↦ by
    rw [(hf.mono hsub).divisor_apply hu, hf.divisor_apply (hsub hu)]
  have hD₂le : ∀ u, D₂ u ≤ D u := by
    intro u
    by_cases hu : u ∈ closedBall c r
    · exact (hD₂eq u hu).le
    · simpa [D₂, hu] using hf.divisor_nonneg u
  have hD₂T : D₂.support ⊆ T := by
    intro u hu
    simp only [T, Set.Finite.coe_toFinset, Function.mem_support] at hu ⊢
    have hu' : u ∈ closedBall c r := D₂.supportWithinDomain hu
    rwa [← hD₂eq u hu']
  -- extract the zeros of `f` on `closedBall c R`
  have htop : ∀ u : closedBall c R, meromorphicOrderAt f u ≠ ⊤ := by
    intro u
    have hc : c ∈ closedBall c R := mem_closedBall_self (hr.trans hrR.le)
    refine hf.meromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected
      (convex_closedBall c R).isPreconnected hc u.2 ?_
    rw [(hf c hc).meromorphicOrderAt_eq, (hf c hc).analyticOrderAt_eq_zero.mpr hfc]
    simp
  obtain ⟨gR, hgR, hgR0, hfeq⟩ := hf.meromorphicOn.extract_zeros_poles htop hfin
  set m : ℂ → ℕ := fun u ↦ (D u).toNat
  set n : ℂ → ℕ := fun u ↦ (D₂ u).toNat
  refine ⟨T, fun z ↦ (∏ u ∈ T, (z - u) ^ (m u - n u)) * gR z, hD₂T, ?_, ?_, ?_⟩
  · have hP : Differentiable ℂ fun z : ℂ ↦ ∏ u ∈ T, (z - u) ^ (m u - n u) := by fun_prop
    exact hP.differentiableOn.mul (hgR.differentiableOn.mono ball_subset_closedBall)
  · intro z hz
    refine mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun u _ ↦ ?_) (hgR0 ⟨z, hsub hz⟩)
    by_cases hzu : z = u
    · subst hzu
      simp [m, n, hD₂eq z hz]
    · exact pow_ne_zero _ (sub_ne_zero.mpr hzu)
  · intro z hz
    have hzU : z ∈ closedBall c R := ball_subset_closedBall hz
    -- upgrade the codiscrete equality to an equality at `z` by continuity
    have hFz : ContinuousAt ((∏ᶠ u, (· - u) ^ D u) • gR) z :=
      ((Function.FactorizedRational.analyticAt (hf.divisor_nonneg z)).continuousAt).smul
        (hgR z hzU).continuousAt
    have hev : f =ᶠ[nhdsWithin z {z}ᶜ] (∏ᶠ u, (· - u) ^ D u) • gR := by
      have h := mem_codiscreteWithin_iff_forall_mem_nhdsNE.mp hfeq z hzU
      filter_upwards [h, nhdsWithin_le_nhds (isOpen_ball.mem_nhds hz)] with w hw hwb
      exact hw.resolve_right (not_not_intro (ball_subset_closedBall hwb))
    have hz' := ((hf z hzU).continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE hFz).mp
      hev |>.eq_of_nhds
    rw [hz', Pi.smul_apply', Function.FactorizedRational.finprod_eq_fun hfin, smul_eq_mul]
    dsimp only
    rw [finprod_eq_prod_of_mulSupport_subset (s := T), ← mul_assoc, ← Finset.prod_mul_distrib]
    · congr 1
      refine Finset.prod_congr rfl fun u _ ↦ ?_
      rw [← pow_add, Nat.add_sub_cancel' (Int.toNat_le_toNat (hD₂le u)),
        ← zpow_natCast, Int.toNat_of_nonneg (hf.divisor_nonneg u)]
    · intro u hu
      simp only [T, Set.Finite.coe_toFinset, Function.mem_support]
      contrapose! hu
      simp [hu]

/-- The logarithmic derivative of `∏ u ∈ T, (z - u) ^ n u` at a point where it is
nonzero. -/
lemma logDeriv_prod_sub_pow {T : Finset ℂ} {n : ℂ → ℕ} {z : ℂ}
    (hz : ∏ u ∈ T, (z - u) ^ n u ≠ 0) :
    logDeriv (fun s ↦ ∏ u ∈ T, (s - u) ^ n u) z = ∑ u ∈ T, (n u : ℂ) / (z - u) := by
  rw [logDeriv_fun_prod (fun u hu ↦ Finset.prod_ne_zero_iff.mp hz u hu)
    (fun u _ ↦ by fun_prop)]
  refine Finset.sum_congr rfl fun u _ ↦ ?_
  rw [logDeriv_fun_pow (by fun_prop)]
  simp [logDeriv_apply, div_eq_mul_inv]

/-- A holomorphic function on an open set whose exponential is holomorphic is holomorphic.
Adapted from `OAI.SevenEighths.LogarithmicControl.differentiableOn_of_exp_eq`. -/
lemma differentiableOn_of_exp_eq {U : Set ℂ} (hU : IsOpen U) {L g : ℂ → ℂ}
    (hL : DifferentiableOn ℂ L U) (hg : ContinuousOn g U)
    (he : Set.EqOn (Complex.exp ∘ g) L U) :
    DifferentiableOn ℂ g U := by
  intro z hz
  have hgc : ContinuousAt g z := (hg z hz).continuousAt (hU.mem_nhds hz)
  have hLc : DifferentiableAt ℂ L z := (hL z hz).differentiableAt (hU.mem_nhds hz)
  have hs := Complex.hasStrictDerivAt_exp (g z)
  let inv := hs.localInverse Complex.exp (Complex.exp (g z)) (g z) (Complex.exp_ne_zero _)
  have hi : DifferentiableAt ℂ inv (L z) := by
    rw [← he hz]
    exact (hs.to_localInverse (Complex.exp_ne_zero _)).hasDerivAt.differentiableAt
  have heq : (fun w ↦ inv (L w)) =ᶠ[nhds z] g := by
    have hlocal := hgc.eventually (hs.eventually_left_inverse (Complex.exp_ne_zero _))
    filter_upwards [hlocal, hU.mem_nhds hz] with w hw hwU
    simpa only [← he hwU, Function.comp_apply] using hw
  exact ((hi.comp z hLc).congr_of_eventuallyEq heq.symm).differentiableWithinAt

/-- A holomorphic function on a ball with no zeros and value `1` at the center has a
holomorphic logarithm vanishing at the center. Adapted from
`OAI.SevenEighths.LogarithmicControl.exists_holomorphic_log_normalized`. -/
lemma exists_holomorphic_log {L : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hL : DifferentiableOn ℂ L (ball c R)) (h0 : ∀ z ∈ ball c R, L z ≠ 0) (hc : L c = 1) :
    ∃ h : ℂ → ℂ, DifferentiableOn ℂ h (ball c R) ∧
      Set.EqOn (Complex.exp ∘ h) L (ball c R) ∧ h c = 0 := by
  have : ContractibleSpace (ball c R) := contractibleSpace_ball hR
  have hsc : IsSimplyConnected (ball c R) := by
    change SimplyConnectedSpace (ball c R)
    infer_instance
  obtain ⟨h, hh, he⟩ := Complex.exists_continuousOn_eqOn_exp_comp hsc isOpen_ball
    hL.continuousOn (by rintro ⟨z, hz, heq⟩; exact h0 z hz heq)
  refine ⟨fun z ↦ h z - h c, (differentiableOn_of_exp_eq isOpen_ball hL hh he).sub_const _,
    fun z hz ↦ ?_, sub_self _⟩
  have hec : Complex.exp (h c) = 1 := (he (mem_ball_self hR)).trans hc
  simp only [Function.comp_apply, Complex.exp_sub, hec, div_one]
  exact he hz

/-- **Borel–Carathéodory** followed by a **Cauchy estimate**: if `h` is holomorphic on
`ball c r₂` with `h c = 0` and `re h ≤ B` there, then `‖h'‖ = O(B)` on `closedBall c r₁`. -/
lemma norm_deriv_le_of_re_le {h : ℂ → ℂ} {c z : ℂ} {r₁ r₂ B : ℝ} (h₁ : 0 ≤ r₁)
    (h₁₂ : r₁ < r₂) (hB : 0 ≤ B) (hh : DifferentiableOn ℂ h (ball c r₂)) (hc : h c = 0)
    (hre : ∀ w ∈ ball c r₂, (h w).re ≤ B) (hz : z ∈ closedBall c r₁) :
    ‖deriv h z‖ ≤ 4 * (r₁ + r₂) / (r₂ - r₁) ^ 2 * B := by
  set r₃ := (r₁ + r₂) / 2 with hr₃
  have h₁₃ : r₁ < r₃ := by linarith
  have h₃₂ : r₃ < r₂ := by linarith
  have hC : 4 * (r₁ + r₂) / (r₂ - r₁) ^ 2 = 2 * r₃ / (r₂ - r₃) / (r₃ - r₁) := by
    have : r₂ - r₁ ≠ 0 := by linarith
    rw [show r₂ - r₃ = (r₂ - r₁) / 2 by linarith, show r₃ - r₁ = (r₂ - r₁) / 2 by linarith, hr₃]
    field_simp
    ring
  rw [hC]
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  set C := 2 * r₃ / (r₂ - r₃) / (r₃ - r₁)
  have hCpos : 0 < C := by
    have : 0 < r₃ := by linarith
    have : 0 < r₂ - r₃ := by linarith
    have : 0 < r₃ - r₁ := by linarith
    positivity
  -- Borel–Carathéodory on `closedBall c r₃`, recentred at the origin
  have hbc : ∀ w ∈ closedBall c r₃, ‖h w‖ ≤ 2 * (B + ε / C) * r₃ / (r₂ - r₃) := by
    intro w hw
    have hw' : ‖w - c‖ ≤ r₃ := by simpa [dist_eq_norm] using hw
    have hh' : DifferentiableOn ℂ (fun v ↦ h (c + v)) (ball 0 r₂) := by
      refine hh.comp (by fun_prop) fun v hv ↦ ?_
      simpa [mem_ball, dist_eq_norm] using hv
    have hb := Complex.borelCaratheodory (M := B + ε / C) (by positivity) hh'
      (fun v hv ↦ (hre _ (by simpa [mem_ball, dist_eq_norm] using hv)).trans
        (le_add_of_nonneg_right (by positivity)))
      (by linarith) (show w - c ∈ ball 0 r₂ by simpa using hw'.trans_lt h₃₂)
    simp only [add_sub_cancel, add_zero, hc, norm_zero, zero_mul, zero_div] at hb
    refine hb.trans ?_
    have : 0 < r₂ - ‖w - c‖ := by linarith
    have : 0 ≤ r₃ := by linarith
    gcongr
  -- Cauchy estimate on `sphere z (r₃ - r₁)`
  have hzc : ‖z - c‖ ≤ r₁ := by simpa [dist_eq_norm] using hz
  have hsub : closedBall z (r₃ - r₁) ⊆ closedBall c r₃ := by
    intro w hw
    rw [mem_closedBall, dist_eq_norm] at hw ⊢
    calc ‖w - c‖ = ‖(w - z) + (z - c)‖ := by ring_nf
      _ ≤ ‖w - z‖ + ‖z - c‖ := norm_add_le _ _
      _ ≤ r₃ := by linarith
  have hd := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by linarith)
    (hh.diffContOnCl_ball (hsub.trans (closedBall_subset_ball h₃₂)))
    (fun w hw ↦ hbc w (hsub (sphere_subset_closedBall hw)))
  refine hd.trans (le_of_eq ?_)
  rw [show 2 * (B + ε / C) * r₃ / (r₂ - r₃) / (r₃ - r₁) = C * (B + ε / C) by simp only [C]; ring,
    mul_add, mul_div_cancel₀ _ hCpos.ne']

/-- **Landau's lemma.** The logarithmic derivative of an analytic function is
the sum over its nearby zeros, up to an error of order `log M`. -/
theorem exists_norm_logDeriv_sub_sum_le {r₁ r₂ R : ℝ} (h₁ : 0 < r₁) (h₁₂ : r₁ < r₂)
    (h₂ : r₂ < R) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (f : ℂ → ℂ) (c : ℂ) (M : ℝ), AnalyticOnNhd ℂ f (closedBall c R) →
      f c ≠ 0 → 1 ≤ M → (∀ z ∈ closedBall c R, ‖f z‖ ≤ M * ‖f c‖) →
      ∀ z ∈ closedBall c r₁, f z ≠ 0 →
        ‖deriv f z / f z - ∑ᶠ ρ, (divisor f (closedBall c r₂) ρ : ℂ) / (z - ρ)‖ ≤
          K * Real.log M := by
  set R₀ := (r₂ + R) / 2 with hR₀
  have h₀₂ : 0 < r₂ := h₁.trans h₁₂
  have h₂₀ : r₂ < R₀ := by linarith
  have h₀R : R₀ < R := by linarith
  have hlogR : 0 < Real.log (R / r₂) := Real.log_pos ((one_lt_div h₀₂).mpr h₂)
  set A := 1 + |Real.log (r₂ / (R₀ - r₂))| / Real.log (R / r₂) with hA
  have hA0 : 0 ≤ A := by positivity
  have hC0 : 0 ≤ 4 * (r₁ + r₂) / (r₂ - r₁) ^ 2 := by positivity
  refine ⟨4 * (r₁ + r₂) / (r₂ - r₁) ^ 2 * A, mul_nonneg hC0 hA0, ?_⟩
  intro f c M hf hfc hM hfM z hz hfz
  obtain ⟨T, g, hT, hg, hg0, hfg⟩ := exists_eq_prod_mul h₀₂.le h₂ hf hfc
  set D₂ := divisor f (closedBall c r₂)
  set n : ℂ → ℕ := fun u ↦ (D₂ u).toNat
  set N := ∑ u ∈ T, n u
  have hlogM : 0 ≤ Real.log M := Real.log_nonneg hM
  have hn : ∀ u, n u ≠ 0 → u ∈ closedBall c r₂ := by
    intro u hu
    refine D₂.supportWithinDomain fun h ↦ hu ?_
    simp [n, h]
  have hD₂n : ∀ u, (D₂ u : ℤ) = n u := fun u ↦
    (Int.toNat_of_nonneg ((hf.mono (closedBall_subset_closedBall h₂.le)).divisor_nonneg u)).symm
  -- Jensen's formula bounds the number of zeros
  have hN : (N : ℝ) ≤ Real.log M / Real.log (R / r₂) := by
    have hR : |R| = R := abs_of_pos (h₀₂.trans h₂)
    have hr : |r₂| = r₂ := abs_of_pos h₀₂
    have hF : AnalyticOnNhd ℂ ((f c)⁻¹ • f) (closedBall c |R|) := by
      rw [hR]
      exact hf.const_smul
    have hJ := hF.sum_divisor_le (r := r₂) (by rwa [hr]) (by rwa [hr, hR]) hM
      (by simp [hfc]) (fun s hs ↦ ?_)
    · rw [hr, divisor_const_smul (inv_ne_zero hfc), Pi.smul_apply, smul_eq_mul,
        inv_mul_cancel₀ hfc, norm_one, div_one, finsum_eq_sum_of_support_subset _ hT] at hJ
      convert hJ using 1
      simp only [N, hD₂n]
      push_cast
      rfl
    · rw [hR] at hs
      rw [Pi.smul_apply, smul_eq_mul, norm_mul, norm_inv, inv_mul_le_iff₀ (norm_pos_iff.mpr hfc),
        mul_comm]
      exact hfM s (sphere_subset_closedBall hs)
  -- the polynomial `P` vanishing at the zeros is large on `sphere c R₀` and small at `c`
  obtain ⟨P, hP⟩ : ∃ P : ℂ → ℂ, P = fun s ↦ ∏ u ∈ T, (s - u) ^ n u := ⟨_, rfl⟩
  have hfg' : ∀ s ∈ ball c R, f s = P s * g s := by
    rw [hP]
    exact hfg
  have hP_lower : ∀ s ∈ sphere c R₀, (R₀ - r₂) ^ N ≤ ‖P s‖ := by
    intro s hs
    rw [mem_sphere, dist_eq_norm] at hs
    rw [hP, norm_prod, ← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_le_prod₀ (fun u _ ↦ pow_nonneg (sub_pos.mpr h₂₀).le _) fun u _ ↦ ?_
    rw [norm_pow]
    by_cases hu : n u = 0
    · simp [hu]
    · have hu' := hn u hu
      rw [mem_closedBall, dist_eq_norm] at hu'
      have hsu : ‖s - c‖ - ‖u - c‖ ≤ ‖s - u‖ := by
        simpa using norm_sub_norm_le (s - c) (u - c)
      gcongr
      linarith
  have hP_upper : ‖P c‖ ≤ r₂ ^ N := by
    rw [hP, norm_prod, ← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_le_prod₀ (fun u _ ↦ by positivity) fun u _ ↦ ?_
    rw [norm_pow]
    by_cases hu : n u = 0
    · simp [hu]
    · have hu' := hn u hu
      rw [mem_closedBall, dist_eq_norm, ← norm_neg, neg_sub] at hu'
      gcongr
  -- maximum modulus principle for `g` on `closedBall c R₀`
  have hgc0 : g c ≠ 0 := hg0 c (mem_closedBall_self h₀₂.le)
  have hg_bound : ∀ s ∈ closedBall c R₀, ‖g s‖ ≤ M * (r₂ / (R₀ - r₂)) ^ N * ‖g c‖ := by
    intro s hs
    refine Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball
      (hg.diffContOnCl_ball (closedBall_subset_ball h₀R)) (fun w hw ↦ ?_)
      (by rwa [closure_ball c (by linarith)])
    rw [frontier_ball c (by linarith)] at hw
    have hwR : w ∈ ball c R := closedBall_subset_ball h₀R (sphere_subset_closedBall hw)
    have hfw := hfM w (ball_subset_closedBall hwR)
    rw [hfg' w hwR, hfg' c (mem_ball_self (by linarith)), norm_mul, norm_mul] at hfw
    have hpos : 0 < (R₀ - r₂) ^ N := pow_pos (sub_pos.mpr h₂₀) N
    rw [show M * (r₂ / (R₀ - r₂)) ^ N * ‖g c‖ = M * (r₂ ^ N * ‖g c‖) / (R₀ - r₂) ^ N by
      rw [div_pow]; ring, le_div_iff₀ hpos]
    calc ‖g w‖ * (R₀ - r₂) ^ N ≤ ‖P w‖ * ‖g w‖ := by
          rw [mul_comm]
          exact mul_le_mul_of_nonneg_right (hP_lower w hw) (norm_nonneg _)
      _ ≤ M * (‖P c‖ * ‖g c‖) := hfw
      _ ≤ M * (r₂ ^ N * ‖g c‖) := by gcongr
  -- hence `log ‖g / g c‖ ≤ A log M` on `ball c r₂`
  have hlog_bound : ∀ s ∈ ball c r₂, Real.log (‖g s‖ / ‖g c‖) ≤ A * Real.log M := by
    intro s hs
    have hgs : 0 < ‖g s‖ := norm_pos_iff.mpr (hg0 s (ball_subset_closedBall hs))
    have hgc : 0 < ‖g c‖ := norm_pos_iff.mpr hgc0
    have hx : 0 < r₂ / (R₀ - r₂) := div_pos h₀₂ (sub_pos.mpr h₂₀)
    have h1 : ‖g s‖ / ‖g c‖ ≤ M * (r₂ / (R₀ - r₂)) ^ N := by
      rw [div_le_iff₀ hgc]
      exact hg_bound s (ball_subset_closedBall.trans (closedBall_subset_closedBall h₂₀.le) hs)
    have h2 : (N : ℝ) * Real.log (r₂ / (R₀ - r₂)) ≤
        Real.log M / Real.log (R / r₂) * |Real.log (r₂ / (R₀ - r₂))| :=
      (mul_le_mul_of_nonneg_left (le_abs_self _) N.cast_nonneg).trans
        (mul_le_mul_of_nonneg_right hN (abs_nonneg _))
    have h3 : A * Real.log M =
        Real.log M + Real.log M / Real.log (R / r₂) * |Real.log (r₂ / (R₀ - r₂))| := by
      rw [hA]
      ring
    calc Real.log (‖g s‖ / ‖g c‖) ≤ Real.log (M * (r₂ / (R₀ - r₂)) ^ N) :=
          Real.log_le_log (div_pos hgs hgc) h1
      _ = Real.log M + N * Real.log (r₂ / (R₀ - r₂)) := by
          rw [Real.log_mul (by linarith) (pow_ne_zero _ hx.ne'), Real.log_pow]
      _ ≤ A * Real.log M := by linarith
  -- a holomorphic logarithm `h` of `g / g c` on `ball c r₂`
  obtain ⟨h, hh, hexp, hc⟩ := exists_holomorphic_log h₀₂ (L := fun s ↦ g s / g c)
    ((hg.mono (ball_subset_ball h₂.le)).div_const _)
    (fun s hs ↦ div_ne_zero (hg0 s (ball_subset_closedBall hs)) hgc0) (div_self hgc0)
  have hre : ∀ w ∈ ball c r₂, (h w).re ≤ A * Real.log M := by
    intro w hw
    calc (h w).re = Real.log ‖Complex.exp (h w)‖ := by rw [Complex.norm_exp, Real.log_exp]
      _ = Real.log (‖g w‖ / ‖g c‖) := by rw [← norm_div]; exact congrArg _ (congrArg _ (hexp hw))
      _ ≤ A * Real.log M := hlog_bound w hw
  -- the logarithmic derivative of `f` splits as that of `P` plus `h'`
  have hzb : z ∈ ball c r₂ := closedBall_subset_ball h₁₂ hz
  have hzR : z ∈ ball c R := ball_subset_ball h₂.le hzb
  have hPz : P z ≠ 0 := by
    intro h0
    apply hfz
    rw [hfg' z hzR, h0, zero_mul]
  have hgz : g z ≠ 0 := hg0 z (ball_subset_closedBall hzb)
  have hlogf : deriv f z / f z = logDeriv P z + logDeriv g z := by
    have hev : f =ᶠ[nhds z] P * g := by
      filter_upwards [isOpen_ball.mem_nhds hzR] with s hs using hfg' s hs
    have hPd : DifferentiableAt ℂ P z := by
      rw [hP]
      fun_prop
    rw [← logDeriv_apply, (logDeriv_congr_nhds hev).eq_of_nhds,
      logDeriv_mul z hPz hgz hPd (hg.differentiableAt (isOpen_ball.mem_nhds hzR))]
  have hlogP : logDeriv P z = ∑ᶠ ρ, (D₂ ρ : ℂ) / (z - ρ) := by
    rw [finsum_eq_sum_of_support_subset (s := T) _ ?_]
    · rw [hP] at hPz ⊢
      rw [logDeriv_prod_sub_pow hPz]
      refine Finset.sum_congr rfl fun u _ ↦ ?_
      rw [hD₂n]
      push_cast
      rfl
    · intro u hu
      apply hT
      contrapose! hu
      simp [Function.notMem_support.mp hu]
  have hlogh : logDeriv g z = deriv h z := by
    have hev : (fun s ↦ g s / g c) =ᶠ[nhds z] Complex.exp ∘ h := by
      filter_upwards [isOpen_ball.mem_nhds hzb] with s hs using (hexp hs).symm
    have hgg : logDeriv (fun s ↦ g s / g c) z = logDeriv g z := by
      simp_rw [div_eq_mul_inv]
      exact logDeriv_mul_const z _ (inv_ne_zero hgc0)
    rw [← hgg, (logDeriv_congr_nhds hev).eq_of_nhds,
      logDeriv_comp Complex.differentiableAt_exp (hh.differentiableAt (isOpen_ball.mem_nhds hzb)),
      Complex.logDeriv_exp, Pi.one_apply, one_mul]
  -- Borel–Carathéodory and Cauchy's estimate bound `h'`
  rw [hlogf, hlogP, add_sub_cancel_left]
  calc ‖logDeriv g z‖ ≤ 4 * (r₁ + r₂) / (r₂ - r₁) ^ 2 * (A * Real.log M) := by
        rw [hlogh]
        exact norm_deriv_le_of_re_le h₁.le h₁₂ (mul_nonneg hA0 hlogM) hh hc hre hz
    _ = 4 * (r₁ + r₂) / (r₂ - r₁) ^ 2 * A * Real.log M := by ring

end Erdos420
