import PrimeNumberTheoremAnd.ResidueCalcOnRectangles
import Mathlib.Analysis.Meromorphic.FactorizedRational

/-!
# The argument principle on rectangles

For an entire function `f` with no zeros on the border of a rectangle and a
function `K` holomorphic near the rectangle, the integral of `f' / f · K` around
the rectangle is `2πi` times the sum of `K` over the zeros inside, counted with
multiplicity.
-/

namespace Erdos420

open Complex MeromorphicOn

open Filter Topology Set in
/-- A point of a rectangle that is not on its border lies in its interior. -/
lemma rectangle_mem_nhds_of_notMem_border {z w p : ℂ} (hre : z.re ≤ w.re) (him : z.im ≤ w.im)
    (hpR : p ∈ Rectangle z w) (hpB : p ∉ RectangleBorder z w) : Rectangle z w ∈ 𝓝 p := by
  rw [mem_Rect hre him] at hpR
  have hre₁ : z.re < p.re := lt_of_le_of_ne hpR.1 fun h ↦ hpB
    (by simp [RectangleBorder, h, hpR.2.2.1, hpR.2.2.2, him, mem_reProdIm])
  have hre₂ : p.re < w.re := lt_of_le_of_ne hpR.2.1 fun h ↦ hpB
    (by simp [RectangleBorder, h, hpR.2.2.1, hpR.2.2.2, him, mem_reProdIm])
  have him₁ : z.im < p.im := lt_of_le_of_ne hpR.2.2.1 fun h ↦ hpB
    (by simp [RectangleBorder, h, hpR.1, hpR.2.1, hre, mem_reProdIm])
  have him₂ : p.im < w.im := lt_of_le_of_ne hpR.2.2.2 fun h ↦ hpB
    (by simp [RectangleBorder, h, hpR.1, hpR.2.1, hre, mem_reProdIm])
  rw [rectangle_mem_nhds_iff, mem_reProdIm, uIoo_of_le hre, uIoo_of_le him]
  exact ⟨⟨hre₁, hre₂⟩, ⟨him₁, him₂⟩⟩

open Filter Topology Set in
/-- A property that holds codiscretely within a nondegenerate rectangle holds frequently near
each point of the rectangle. -/
lemma frequently_nhdsNE_of_codiscreteWithin_rectangle {z w u : ℂ} {p : ℂ → Prop}
    (hzw : z ≠ w) (hu : u ∈ Rectangle z w)
    (h : ∀ᶠ x in codiscreteWithin (Rectangle z w), p x) : ∃ᶠ x in 𝓝[≠] u, p x := by
  obtain ⟨v, hvR, hvu⟩ : ∃ v ∈ Rectangle z w, v ≠ u := by
    by_cases hzu : z = u
    · exact ⟨w, right_mem_rect z w, fun h ↦ hzw (hzu.trans h.symm)⟩
    · exact ⟨z, left_mem_rect z w, hzu⟩
  have hconv : Convex ℝ (Rectangle z w) := by
    rw [rectangle_eq_convexHull]
    exact convex_convexHull ℝ _
  have hlim :
      Tendsto (fun t : ℝ ↦ u + t • (v - u)) (𝓝[>] 0) (𝓝[Rectangle z w \ {u}] u) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have hcont : Continuous (fun t : ℝ ↦ u + t • (v - u)) := by fun_prop
      simpa using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
    · filter_upwards [Ioo_mem_nhdsGT one_pos] with t ht
      refine ⟨hconv.add_smul_sub_mem hu hvR ⟨ht.1.le, ht.2.le⟩, fun htu ↦ ?_⟩
      have htv : t = 0 ∨ v = u := by simpa [sub_eq_zero] using htu
      exact htv.elim ht.1.ne' hvu
  have := hlim.neBot
  exact (h.filter_mono (nhdsWithin_le_codiscreteWithin hu)).frequently.filter_mono
    (nhdsWithin_mono _ fun x hx ↦ hx.2)

/-- A finite sum of simple poles off the border of a rectangle is integrable on its border. -/
lemma rectangleBorderIntegrable_sum_div_sub {z w : ℂ} (S : Finset ℂ)
    (hS : ∀ p ∈ S, p ∉ RectangleBorder z w) (c : ℂ → ℂ) :
    RectangleBorderIntegrable (fun s ↦ ∑ p ∈ S, c p / (s - p)) z w := by
  refine ContinuousOn.rectangleBorder_integrable (continuousOn_finsetSum _ fun p hp s hs ↦ ?_)
  have hsp : s - p ≠ 0 := sub_ne_zero.2 fun h ↦ hS p hp (h ▸ hs)
  exact (continuousAt_const.div (continuousAt_id.sub continuousAt_const) hsp).continuousWithinAt

open Topology in
/-- The rectangle integral of a finite sum of simple poles inside the rectangle is `2πi` times
the sum of their residues. -/
lemma rectangleIntegral_sum_div_sub {z w : ℂ} (hre : z.re ≤ w.re) (him : z.im ≤ w.im)
    (S : Finset ℂ) (hS : ∀ p ∈ S, Rectangle z w ∈ 𝓝 p) (c : ℂ → ℂ) :
    RectangleIntegral (fun s ↦ ∑ p ∈ S, c p / (s - p)) z w =
      2 * Real.pi * I * ∑ p ∈ S, c p := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [RectangleIntegral, HIntegral, VIntegral]
  | insert a S ha ih =>
    rw [Finset.forall_mem_insert] at hS
    have hterm : RectangleIntegral (fun s ↦ c a / (s - a)) z w = 2 * Real.pi * I * c a := by
      have h := ResidueTheoremInRectangle (c := c a) hre him hS.1
      have hπ : (2 * Real.pi * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
      rw [RectangleIntegral', smul_eq_mul, one_div, inv_mul_eq_iff_eq_mul₀ hπ] at h
      exact h
    have hint : RectangleBorderIntegrable (fun s ↦ c a / (s - a)) z w := by
      simpa using rectangleBorderIntegrable_sum_div_sub {a}
        (by simpa using not_mem_rectangleBorder_of_rectangle_mem_nhds hS.1) c
    have hfun : (fun s ↦ ∑ p ∈ insert a S, c p / (s - p)) =
        (fun s ↦ c a / (s - a)) + fun s ↦ ∑ p ∈ S, c p / (s - p) := by
      funext s
      simp [Finset.sum_insert ha]
    rw [hfun, hint.add (rectangleBorderIntegrable_sum_div_sub S
      (fun p hp ↦ not_mem_rectangleBorder_of_rectangle_mem_nhds (hS.2 p hp)) c), hterm,
      ih hS.2, Finset.sum_insert ha]
    ring

open Topology in
/-- The rectangle integral of `K(s) / (s - p)`, with `K` holomorphic near the rectangle and
`p` inside it, is `2πi K(p)`. -/
theorem rectangleIntegral_div_sub {K : ℂ → ℂ} {U : Set ℂ} {z w p : ℂ} (hre : z.re ≤ w.re)
    (him : z.im ≤ w.im) (hU : IsOpen U) (hRU : Rectangle z w ⊆ U) (hK : DifferentiableOn ℂ K U)
    (hp : Rectangle z w ∈ 𝓝 p) :
    RectangleIntegral (fun s ↦ K s / (s - p)) z w = 2 * Real.pi * I * K p := by
  have hpB : p ∉ RectangleBorder z w := not_mem_rectangleBorder_of_rectangle_mem_nhds hp
  have hpR : p ∈ Rectangle z w := mem_of_mem_nhds hp
  -- the holomorphic part of the integrand
  have hH : HolomorphicOn (dslope K p) (Rectangle z w) := fun s hs ↦
    (((differentiableOn_dslope (hU.mem_nhds (hRU hpR))).2 hK).differentiableAt
      (hU.mem_nhds (hRU hs))).differentiableWithinAt
  -- on the border, the integrand splits into the holomorphic part and a simple pole
  have hborder : Set.EqOn (fun s ↦ K s / (s - p))
      (dslope K p + fun s ↦ ∑ q ∈ {p}, K p / (s - q)) (RectangleBorder z w) := by
    intro s hs
    have hsp : s - p ≠ 0 := sub_ne_zero.2 fun h ↦ hpB (h ▸ hs)
    simp only [Pi.add_apply, Finset.sum_singleton]
    rw [dslope_of_ne _ (sub_ne_zero.1 hsp), slope_def_field]
    field_simp
    ring
  rw [RectangleIntegral_congr hborder, hH.rectangleBorderIntegrable.add
    (rectangleBorderIntegrable_sum_div_sub {p} (by simpa using hpB) fun _ ↦ K p),
    hH.vanishesOnRectangle subset_rfl,
    rectangleIntegral_sum_div_sub hre him {p} (by simpa using hp) fun _ ↦ K p, zero_add,
    Finset.sum_singleton]

/-- The rectangle integral of `f' / f · K` picks up `K` at each zero of `f`,
counted with multiplicity. -/
theorem rectangleIntegral_logDeriv_mul {f K : ℂ → ℂ} {U : Set ℂ} {z w : ℂ}
    (hre : z.re < w.re) (him : z.im < w.im) (hU : IsOpen U) (hRU : Rectangle z w ⊆ U)
    (hf : Differentiable ℂ f) (hK : DifferentiableOn ℂ K U)
    (hbd : ∀ s ∈ RectangleBorder z w, f s ≠ 0) :
    RectangleIntegral (fun s ↦ deriv f s / f s * K s) z w =
      2 * Real.pi * I * ∑ᶠ ρ, (divisor f (Rectangle z w) ρ : ℂ) * K ρ := by
  classical
  have hfA : AnalyticOnNhd ℂ f (Rectangle z w) := fun s _ ↦ hf.analyticAt s
  have hzB : z ∈ RectangleBorder z w := Or.inl <| Or.inl <| Or.inl ⟨Set.left_mem_uIcc, rfl⟩
  -- `f` is entire and nonzero at `z`, so it has finite order everywhere
  have htop : ∀ u : Rectangle z w, meromorphicOrderAt f u ≠ ⊤ := by
    intro u
    have hz : analyticOrderAt f z ≠ ⊤ := by
      rw [(hf.analyticAt z).analyticOrderAt_eq_zero.2 (hbd z hzB)]
      exact ENat.zero_ne_top
    have hu : analyticOrderAt f u ≠ ⊤ :=
      AnalyticOnNhd.analyticOrderAt_ne_top_of_isPreconnected (fun s _ ↦ hf.analyticAt s)
        isPreconnected_univ (Set.mem_univ z) (Set.mem_univ (u : ℂ)) hz
    rw [(hf.analyticAt u).meromorphicOrderAt_eq]
    simpa using hu
  have hfin : (divisor f (Rectangle z w)).support.Finite :=
    (divisor f (Rectangle z w)).finiteSupport (isCompact_uIcc.reProdIm isCompact_uIcc)
  have hD0 : 0 ≤ divisor f (Rectangle z w) := hfA.divisor_nonneg
  -- factor out the zeros of `f` in the rectangle
  obtain ⟨g, hgA, hg0, hfg⟩ := MeromorphicOn.extract_zeros_poles hfA.meromorphicOn htop hfin
  set S := hfin.toFinset with hS
  have hSzero : ∀ ρ ∈ S, ρ ∈ Rectangle z w ∧ f ρ = 0 := by
    intro ρ hρ
    have hρ' : divisor f (Rectangle z w) ρ ≠ 0 := by simpa [S] using hρ
    have hρR : ρ ∈ Rectangle z w := (divisor f (Rectangle z w)).supportWithinDomain hρ'
    refine ⟨hρR, by_contra fun h ↦ hρ' ?_⟩
    rw [hfA.divisor_apply hρR, (hf.analyticAt ρ).analyticOrderAt_eq_zero.2 h]
    simp
  have hSint : ∀ ρ ∈ S, Rectangle z w ∈ nhds ρ := fun ρ hρ ↦
    rectangle_mem_nhds_of_notMem_border hre.le him.le (hSzero ρ hρ).1
      fun hB ↦ hbd ρ hB (hSzero ρ hρ).2
  have hφ : (∏ᶠ u, (· - u) ^ divisor f (Rectangle z w) u) =
      ∏ ρ ∈ S, (· - ρ) ^ divisor f (Rectangle z w) ρ := by
    apply finprod_eq_prod_of_mulSupport_subset
    rw [Function.FactorizedRational.mulSupport]
    simp [S]
  set P : ℂ → ℂ := ∏ ρ ∈ S, (· - ρ) ^ divisor f (Rectangle z w) ρ with hP
  have hPA : ∀ s, AnalyticAt ℂ P s := fun s ↦
    hφ ▸ Function.FactorizedRational.analyticAt (hD0 s)
  -- upgrade the codiscrete factorization to a local one by the identity theorem
  have hloc : ∀ u ∈ Rectangle z w, f =ᶠ[nhds u] P * g := fun u hu ↦
    ((hf.analyticAt u).frequently_eq_iff_eventually_eq ((hPA u).mul (hgA u hu))).1
      (frequently_nhdsNE_of_codiscreteWithin_rectangle (fun h ↦ hre.ne (by rw [h])) hu
        (hφ ▸ hfg))
  -- the holomorphic part of the integrand
  let H : ℂ → ℂ := fun s ↦ deriv g s / g s * K s +
    ∑ ρ ∈ S, (divisor f (Rectangle z w) ρ : ℂ) * dslope K ρ s
  have hH : HolomorphicOn H (Rectangle z w) := by
    intro s hs
    have hKs : DifferentiableAt ℂ K s := hK.differentiableAt (hU.mem_nhds (hRU hs))
    have hdg : DifferentiableAt ℂ (deriv g) s := (hgA s hs).deriv.differentiableAt
    have hslope : ∀ ρ ∈ S, DifferentiableAt ℂ (dslope K ρ) s := fun ρ hρ ↦
      ((differentiableOn_dslope (hU.mem_nhds (hRU (hSzero ρ hρ).1))).2 hK).differentiableAt
        (hU.mem_nhds (hRU hs))
    refine DifferentiableAt.differentiableWithinAt ?_
    exact ((hdg.div (hgA s hs).differentiableAt (hg0 ⟨s, hs⟩)).mul hKs).add
      (DifferentiableAt.fun_sum fun ρ hρ ↦ (hslope ρ hρ).const_mul _)
  -- on the border, the integrand splits into the holomorphic part and simple poles
  have hborder : Set.EqOn (fun s ↦ deriv f s / f s * K s)
      (H + fun s ↦ ∑ ρ ∈ S, (divisor f (Rectangle z w) ρ : ℂ) * K ρ / (s - ρ))
      (RectangleBorder z w) := by
    intro s hs
    have hsR : s ∈ Rectangle z w := rectangleBorder_subset_rectangle z w hs
    have hsρ : ∀ ρ ∈ S, s - ρ ≠ 0 := fun ρ hρ ↦
      sub_ne_zero.2 fun h ↦ hbd s hs (h ▸ (hSzero ρ hρ).2)
    have hfs : f s = P s * g s := (hloc s hsR).eq_of_nhds
    have hPs : P s ≠ 0 := fun h ↦ hbd s hs (by rw [hfs, h, zero_mul])
    have hlogP : logDeriv P s = ∑ ρ ∈ S, (divisor f (Rectangle z w) ρ : ℂ) / (s - ρ) := by
      rw [hP, logDeriv_prod (f := fun ρ ↦ (· - ρ) ^ divisor f (Rectangle z w) ρ)
        (fun ρ hρ ↦ zpow_ne_zero _ (hsρ ρ hρ))
        (fun ρ hρ ↦ (differentiableAt_id.sub_const ρ).zpow (Or.inl (hsρ ρ hρ)))]
      refine Finset.sum_congr rfl fun ρ _ ↦ ?_
      change logDeriv (fun x ↦ (x - ρ) ^ divisor f (Rectangle z w) ρ) s = _
      rw [logDeriv_fun_zpow (by fun_prop : DifferentiableAt ℂ (fun x : ℂ ↦ x - ρ) s)]
      simp [logDeriv_apply, div_eq_mul_inv]
    have hlog : deriv f s / f s = logDeriv P s + logDeriv g s := by
      rw [← logDeriv_apply, (logDeriv_congr_nhds (hloc s hsR)).eq_of_nhds]
      exact logDeriv_mul s hPs (hg0 ⟨s, hsR⟩) (hPA s).differentiableAt
        (hgA s hsR).differentiableAt
    simp only [Pi.add_apply, H]
    rw [hlog, hlogP, add_mul, Finset.sum_mul, add_assoc, ← Finset.sum_add_distrib, add_comm,
      logDeriv_apply]
    congr 1
    refine Finset.sum_congr rfl fun ρ hρ ↦ ?_
    rw [dslope_of_ne _ (sub_ne_zero.1 (hsρ ρ hρ)), slope_def_field]
    field_simp [hsρ ρ hρ]
    ring
  have hsum : RectangleIntegral
      (fun s ↦ ∑ ρ ∈ S, (divisor f (Rectangle z w) ρ : ℂ) * K ρ / (s - ρ)) z w =
      2 * Real.pi * I * ∑ ρ ∈ S, (divisor f (Rectangle z w) ρ : ℂ) * K ρ :=
    rectangleIntegral_sum_div_sub hre.le him.le S hSint
      (fun ρ ↦ (divisor f (Rectangle z w) ρ : ℂ) * K ρ)
  have hsumInt : RectangleBorderIntegrable
      (fun s ↦ ∑ ρ ∈ S, (divisor f (Rectangle z w) ρ : ℂ) * K ρ / (s - ρ)) z w :=
    rectangleBorderIntegrable_sum_div_sub S
      (fun ρ hρ ↦ not_mem_rectangleBorder_of_rectangle_mem_nhds (hSint ρ hρ))
      (fun ρ ↦ (divisor f (Rectangle z w) ρ : ℂ) * K ρ)
  have hfinsum : ∑ᶠ ρ, (divisor f (Rectangle z w) ρ : ℂ) * K ρ =
      ∑ ρ ∈ S, (divisor f (Rectangle z w) ρ : ℂ) * K ρ := by
    refine finsum_eq_sum_of_support_subset _ fun ρ hρ ↦ ?_
    rw [hS, Set.Finite.coe_toFinset, Function.mem_support]
    intro h
    exact hρ (by simp [h])
  rw [RectangleIntegral_congr hborder, hH.rectangleBorderIntegrable.add hsumInt,
    hH.vanishesOnRectangle subset_rfl, hsum, hfinsum, zero_add]

end Erdos420
