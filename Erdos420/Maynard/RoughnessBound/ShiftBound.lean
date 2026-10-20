import Erdos420.Maynard.RoughnessBound.Shift

/-!
# Size of the shifted variables for smooth `F`

For `y_r = F(log r / log R)` on the support `T` (the library's `PrimeGaps.y₀`), with `F`
Lipschitz, bounded and supported on the simplex `𝓡 k`, and `p ∤ W`, the shifted variables
`z_r = (y_r − y_{r p e_m}) + ∑_{j ≠ m} c_j y_{r p e_j}` satisfy
`|z_r| ≤ L log p / log R + F₀ ∑_{j ≠ m} |c_j|`. The difference `y_r − y_{r p e_m}` is
`F(t) − F(t')` with `t' − t = (log p / log R) e_m` even when `r p e_m ∉ T`: then
`∏ r p e_m > R`, so `t'` lies outside the simplex and `F(t') = 0`.
-/

namespace Erdos420

open Finset
open scoped PrimeGaps

variable {k : ℕ}

/-- The point `(log rᵢ / log R)ᵢ`. -/
noncomputable def logPoint (R : ℝ) (r : Fin k → ℕ) : EuclideanSpace ℝ (Fin k) :=
  WithLp.toLp 2 fun i ↦ Real.log (r i) / Real.log R

/-- Multiplying `r_m` by `p` moves `(log rᵢ / log R)ᵢ` by `log p / log R`. -/
lemma dist_logPoint_mulAt {R : ℝ} (hR : 1 < R) {p : ℕ} (hp : p.Prime) {r : Fin k → ℕ}
    (m : Fin k) (hr : r m ≠ 0) :
    dist (logPoint R r) (logPoint R (mulAt r m p)) = Real.log p / Real.log R := by
  have hlogR : 0 < Real.log R := Real.log_pos hR
  have hlogp : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.one_le)
  rw [EuclideanSpace.dist_eq, sum_eq_single m]
  · simp only [logPoint, mulAt, Function.update_self, Real.dist_eq, sq_abs]
    push_cast
    rw [Real.log_mul (by exact_mod_cast hp.ne_zero) (by exact_mod_cast hr),
      show Real.log (r m) / Real.log R - (Real.log p + Real.log (r m)) / Real.log R =
        -(Real.log p / Real.log R) by ring, neg_sq, Real.sqrt_sq (by positivity)]
  · intro i _ hi
    simp [logPoint, mulAt, Function.update_of_ne hi]
  · simp

/-- **Size of the shifted variables.** For `c_m = −1`, the shift of `y_r = F(log r / log R)`
has `|z_r| ≤ L log p / log R + F₀ ∑_{j ≠ m} |c_j|`. -/
theorem abs_shiftY_y₀_le {R : ℝ} (hR : 1 < R) {W p : ℕ} (hp : p.Prime) (hpW : ¬p ∣ W)
    {G : EuclideanSpace ℝ (Fin k) → ℝ} {L : NNReal} (hG : LipschitzWith L G) {F₀ : ℝ}
    (hF₀ : ∀ x, |G x| ≤ F₀) (hsupp : Function.support G ⊆ 𝓡 k) (m : Fin k) (c : Fin k → ℝ)
    (hcm : c m = -1) (r : Fin k → ℕ) :
    |shiftY (permissibleSupport k ⌊R⌋₊ W) (PrimeGaps.y₀ R W G) p c r| ≤
      L * (Real.log p / Real.log R) + (∑ j ∈ univ.erase m, |c j|) * F₀ := by
  classical
  set T := permissibleSupport k ⌊R⌋₊ W
  set y := PrimeGaps.y₀ R W G
  have hlogR : 0 < Real.log R := Real.log_pos hR
  have hlogp : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.one_le)
  have hF₀0 : 0 ≤ F₀ := (abs_nonneg _).trans (hF₀ 0)
  have hrhs : 0 ≤ L * (Real.log p / Real.log R) + (∑ j ∈ univ.erase m, |c j|) * F₀ :=
    add_nonneg (mul_nonneg L.2 (by positivity))
      (mul_nonneg (sum_nonneg fun _ _ ↦ abs_nonneg _) hF₀0)
  have hy : ∀ s, |y s| ≤ F₀ := fun s ↦ by
    rw [PrimeGaps.y₀_apply]
    split_ifs
    · exact hF₀ _
    · simpa using hF₀0
  rw [shiftY_apply]
  split_ifs with hr
  swap
  · simpa using hrhs
  obtain ⟨hrT, hpr⟩ := hr
  obtain ⟨hr0, hle, hcop, hsq⟩ := mem_permissibleSupport_iff'.mp hrT
  -- `y_{r p e_m} = F(t')` also when `r p e_m ∉ T`
  have hyr : y r = G (logPoint R r) := by rw [PrimeGaps.y₀_apply, ite_eq_left hrT]; rfl
  have hys : y (mulAt r m p) = G (logPoint R (mulAt r m p)) := by
    rw [PrimeGaps.y₀_apply]
    split_ifs with hs
    · rfl
    symm
    refine Function.notMem_support.mp fun hmem ↦ ?_
    have hsimp := hsupp hmem
    rw [EuclideanSpace.mem_scaledStdSimplex_iff] at hsimp
    have hcop' : (∏ i, mulAt r m p i).Coprime W := by
      rw [prod_mulAt]
      exact Nat.coprime_mul_iff_left.mpr ⟨(Nat.Prime.coprime_iff_not_dvd hp).mpr hpW, hcop⟩
    have hsq' : Squarefree (∏ i, mulAt r m p i) := by
      rw [prod_mulAt]
      exact Nat.squarefree_mul_iff.mpr
        ⟨(Nat.Prime.coprime_iff_not_dvd hp).mpr hpr, hp.squarefree, hsq⟩
    have hgt : R < ((∏ i, mulAt r m p i : ℕ) : ℝ) := Nat.lt_of_floor_lt
      (not_le.mp fun h ↦ hs (mem_permissibleSupport_iff.mpr ⟨h, hcop', hsq'⟩))
    have hs0 : ∀ i, (mulAt r m p i : ℝ) ≠ 0 := fun i ↦ by
      exact_mod_cast prod_ne_zero_iff.mp hsq'.ne_zero i (mem_univ i)
    have hsum : ∑ i, (logPoint R (mulAt r m p)) i = Real.log (∏ i, (mulAt r m p i : ℝ)) /
        Real.log R := by
      rw [Real.log_prod fun i _ ↦ hs0 i, sum_div]
      rfl
    have hlt : 1 < ∑ i, (logPoint R (mulAt r m p)) i := by
      rw [hsum, one_lt_div hlogR]
      push_cast at hgt
      exact Real.log_lt_log (by linarith) hgt
    exact absurd hsimp.2 (not_le.mpr hlt)
  have hz : y r + ∑ j, c j * y (mulAt r j p) =
      (y r - y (mulAt r m p)) + ∑ j ∈ univ.erase m, c j * y (mulAt r j p) := by
    rw [← add_sum_erase univ _ (mem_univ m), hcm]
    ring
  rw [hz]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [hyr, hys, ← Real.dist_eq, ← dist_logPoint_mulAt hR hp m (hr0 m)]
    exact hG.dist_le_mul _ _
  · refine (abs_sum_le_sum_abs _ _).trans ?_
    rw [sum_mul]
    refine sum_le_sum fun j _ ↦ ?_
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hy _) (abs_nonneg _)

end Erdos420
