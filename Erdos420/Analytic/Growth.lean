module

public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import Mathlib.NumberTheory.LSeries.SumCoeff

/-!
# Growth of Dirichlet L-functions to the right of zero

Partial summation bounds a nontrivial Dirichlet L-function by `N ‖s‖ / re s`
on `0 < re s`, where `N` is the modulus. The bound is first proved for
`1 < re s` from the integral representation and then continued analytically.
-/

@[expose] public section

namespace Erdos420

open DirichletCharacter Asymptotics Filter MeasureTheory

open scoped LSeries.notation Topology

/-- The partial sums of a nontrivial Dirichlet character are bounded by its modulus. -/
lemma norm_sum_Icc_le {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1)
    (n : ℕ) : ‖∑ k ∈ Finset.Icc 1 n, χ k‖ ≤ N := by
  let f : ℕ → ℂ := fun k ↦ χ k
  -- a full period of values sums to zero
  have h₀ : ∑ k ∈ Finset.range N, f k = 0 := by
    rw [← χ.sum_eq_zero_of_ne_one hχ]
    exact Finset.sum_nbij' (fun k ↦ (k : ZMod N)) ZMod.val (by simp)
      (fun x _ ↦ Finset.mem_range.mpr (ZMod.val_lt x))
      (fun k hk ↦ ZMod.val_cast_of_lt (Finset.mem_range.mp hk))
      (fun x _ ↦ ZMod.natCast_zmod_val x) (fun _ _ ↦ rfl)
  -- so does a shifted full period
  have hperiod : ∑ k ∈ Finset.range N, f (k + 1) = 0 := by
    have h₁ := Finset.sum_range_succ f N
    have h₂ := Finset.sum_range_succ' f N
    have hN : f N = f 0 := by simp [f]
    linear_combination h₁ - h₂ + h₀ + hN
  -- rewrite the partial sums over `range`
  have hIcc (n : ℕ) : ∑ k ∈ Finset.Icc 1 n, f k = ∑ k ∈ Finset.range n, f (k + 1) := by
    induction n with
    | zero => simp
    | succ n ih => rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]
  -- bound by strong induction, peeling off full periods
  have hbound (n : ℕ) : ‖∑ k ∈ Finset.range n, f (k + 1)‖ ≤ N := by
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      rcases lt_or_ge n N with hn | hn
      · calc ‖∑ k ∈ Finset.range n, f (k + 1)‖
          _ ≤ ∑ k ∈ Finset.range n, ‖f (k + 1)‖ := norm_sum_le _ _
          _ ≤ ∑ _k ∈ Finset.range n, (1 : ℝ) :=
            Finset.sum_le_sum fun k _ ↦ χ.norm_le_one _
          _ = n := by simp
          _ ≤ N := by exact_mod_cast hn.le
      · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
        have hshift (k : ℕ) : f (N + k + 1) = f (k + 1) := by
          change χ ((N + k + 1 : ℕ) : ZMod N) = χ ((k + 1 : ℕ) : ZMod N)
          push_cast
          rw [ZMod.natCast_self, zero_add]
        rw [Finset.sum_range_add, hperiod, zero_add]
        simp_rw [hshift]
        exact ih m (by have := NeZero.pos N; omega)
  exact (hIcc n).symm ▸ hbound n

/-- A nontrivial Dirichlet L-function grows at most linearly in `‖s‖` to the
right of zero. -/
theorem norm_LFunction_le {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1)
    {s : ℂ} (hs : 0 < s.re) : ‖LFunction χ s‖ ≤ N * ‖s‖ / s.re := by
  let A : ℝ → ℂ := fun t ↦ ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, χ k
  have hA (t : ℝ) : ‖A t‖ ≤ N := norm_sum_Icc_le hχ _
  -- the partial sums cut off below one, as a Mellin transform input
  let F : ℝ → ℂ := fun t ↦ (Set.Ioi (1 : ℝ)).indicator (fun _ ↦ (1 : ℂ)) t * A t
  have hF (t : ℝ) : ‖F t‖ ≤ N := by
    by_cases ht : t ∈ Set.Ioi (1 : ℝ) <;> simp [F, ht, hA t]
  let G : ℂ → ℂ := fun z ↦ z * ∫ t in Set.Ioi (1 : ℝ), A t * (t : ℂ) ^ (-(z + 1))
  have hGmellin : G = fun z ↦ z * mellin F (-z) := by
    funext z
    have hint : (fun t : ℝ ↦ (t : ℂ) ^ (-z - 1) • F t) =
        (Set.Ioi (1 : ℝ)).indicator (fun t ↦ A t * (t : ℂ) ^ (-(z + 1))) := by
      funext t
      rw [show -z - 1 = -(z + 1) by ring]
      by_cases ht : t ∈ Set.Ioi (1 : ℝ) <;> simp [F, ht, mul_comm]
    rw [mellin, hint, setIntegral_indicator measurableSet_Ioi, Set.Ioi_inter_Ioi,
      sup_eq_right.mpr zero_le_one]
  -- the integral representation holds to the right of one
  have hO :
      (fun n ↦ ∑ k ∈ Finset.Icc 1 n, ↗χ k) =O[atTop] fun n ↦ (n : ℝ) ^ (0 : ℝ) :=
    IsBigO.of_bound N (Eventually.of_forall fun n ↦ by simpa using norm_sum_Icc_le hχ n)
  have hL₁ {z : ℂ} (hz : 1 < z.re) : LFunction χ z = G z := by
    rw [LFunction_eq_LSeries χ hz]
    exact LSeries_eq_mul_integral _ le_rfl (by linarith) (LSeriesSummable_of_one_lt_re χ hz) hO
  -- both sides are analytic on the right half-plane
  let U : Set ℂ := {z | 0 < z.re}
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hGdiff : DifferentiableOn ℂ G U := by
    intro z hz
    have hmellin : DifferentiableAt ℂ (mellin F) (-z) := by
      refine mellin_differentiableAt_of_isBigO_rpow (a := 0) (b := -z.re - 1) ?_ ?_
        (by simpa using (show 0 < z.re from hz)) ?_ (by simp)
      · have hg : LocallyIntegrableOn ((Set.Ioi (1 : ℝ)).indicator fun _ ↦ (1 : ℂ))
            (Set.Ici 0) :=
          ((locallyIntegrable_const 1).indicator measurableSet_Ioi).locallyIntegrableOn _
        exact (locallyIntegrableOn_mul_sum_Icc (fun n ↦ χ n) le_rfl hg).mono_set
          Set.Ioi_subset_Ici_self
      · exact IsBigO.of_bound N (Eventually.of_forall fun t ↦ by simpa using hF t)
      · refine EventuallyEq.trans_isBigO ?_ (isBigO_zero _ _)
        filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds zero_lt_one)] with t ht
        simp [F, not_lt.mpr (Set.mem_Iio.mp ht).le]
    rw [hGmellin]
    exact (differentiableAt_id.mul (hmellin.comp z differentiableAt_id.neg)).differentiableWithinAt
  have hEq : Set.EqOn (LFunction χ) G U := by
    have hLan := (differentiable_LFunction hχ).differentiableOn.analyticOnNhd hU
    refine hLan.eqOn_of_preconnected_of_eventuallyEq (hGdiff.analyticOnNhd hU)
      (convex_halfSpace_re_gt 0).isPreconnected (z₀ := 2) (by simp [U]) ?_
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show (1 : ℝ) < (2 : ℂ).re by norm_num)] with z hz
    exact hL₁ hz
  -- bound the integral representation
  have hint : ‖∫ t in Set.Ioi (1 : ℝ), A t * (t : ℂ) ^ (-(s + 1))‖ ≤ N / s.re := by
    have hrpow : IntegrableOn (fun t : ℝ ↦ t ^ (-s.re - 1)) (Set.Ioi 1) :=
      integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one
    calc ‖∫ t in Set.Ioi (1 : ℝ), A t * (t : ℂ) ^ (-(s + 1))‖
      _ ≤ ∫ t in Set.Ioi (1 : ℝ), N * t ^ (-s.re - 1) := by
        refine norm_integral_le_of_norm_le (hrpow.const_mul _) ?_
        refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht ↦ ?_
        have ht₀ : 0 < t := zero_lt_one.trans ht
        rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht₀]
        have hre : (-(s + 1)).re = -s.re - 1 := by simp; ring
        rw [hre]
        gcongr
        exact hA t
      _ = N / s.re := by
        rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) zero_lt_one,
          show -s.re - 1 + 1 = -s.re by ring, Real.one_rpow]
        field_simp
  calc ‖LFunction χ s‖
    _ = ‖s‖ * ‖∫ t in Set.Ioi (1 : ℝ), A t * (t : ℂ) ^ (-(s + 1))‖ := by
      rw [hEq hs, norm_mul]
    _ ≤ ‖s‖ * (N / s.re) := by gcongr
    _ = N * ‖s‖ / s.re := by ring

end Erdos420
