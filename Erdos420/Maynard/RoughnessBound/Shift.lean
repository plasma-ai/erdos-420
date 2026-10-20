import Erdos420.Maynard.RoughnessBound.Kernel

/-!
# Weights at `n` with `p ∣ n + h_m` as weights of modulus `W p`

Fix a prime `p` and the support `T` of the variables `y`: tuples `r` with squarefree product
coprime to `W` and `∏ rᵢ ≤ R`. Each `r ∈ T` is either coprime to `p`, or `r = r' p e_j` for a
unique `j` and `r' ∈ T` coprime to `p`. If `p ∣ a_m` and `p ∤ aᵢ` for `i ≠ m`, the kernel
satisfies `κ(p r'_j, a_j) = c_j κ(r'_j, a_j)` with `c_m = −1` and `c_j = 1 / (p − 1)` otherwise,
so the divisor sum of `yToL y` at `a` equals that of `yToL z`, where

  `z_r = y_r + ∑_j c_j y_{r p e_j} = (y_r − y_{r p e_m}) + (p − 1)⁻¹ ∑_{j ≠ m} y_{r p e_j}`

for `r` coprime to `p` (and `z_r = 0` otherwise). This is Maynard's (9.74): `z` is supported on
tuples coprime to `W p`, and for `y_r = F(log r / log R)` it is `O(log p / log R + 1 / p)`.
-/

namespace Erdos420

open Finset
open scoped PrimeGaps

variable {k : ℕ}

/-- `r` with its `j`-th coordinate multiplied by `p`. -/
def mulAt (r : Fin k → ℕ) (j : Fin k) (p : ℕ) : Fin k → ℕ := Function.update r j (p * r j)

/-- `∏ᵢ (r p e_j)ᵢ = p ∏ᵢ rᵢ`. -/
lemma prod_mulAt (r : Fin k → ℕ) (j : Fin k) (p : ℕ) : ∏ i, mulAt r j p i = p * ∏ i, r i := by
  classical
  rw [mulAt, prod_update_of_mem (mem_univ j), ← mul_prod_erase univ r (mem_univ j),
    sdiff_singleton_eq_erase, mul_assoc]

/-- Each coordinate of `r` divides that of `r p e_j`. -/
lemma dvd_mulAt (r : Fin k → ℕ) (j : Fin k) (p : ℕ) (i : Fin k) : r i ∣ mulAt r j p i := by
  rcases eq_or_ne i j with rfl | hij
  · simp [mulAt]
  · simp [mulAt, Function.update_of_ne hij]

/-- `r ↦ r p e_j` is injective for `p ≠ 0`. -/
lemma mulAt_injective {j : Fin k} {p : ℕ} (hp : p ≠ 0) : Function.Injective (mulAt · j p) := by
  intro r r' h
  funext i
  have := congrFun h i
  rcases eq_or_ne i j with rfl | hij
  · simpa [mulAt, hp] using this
  · simpa [mulAt, Function.update_of_ne hij] using this

/-- A prime divides at most one coordinate of a tuple with squarefree product. -/
private lemma eq_of_prime_dvd_of_squarefree {r : Fin k → ℕ} (hsq : Squarefree (∏ i, r i)) {p : ℕ}
    (hp : p.Prime) {i j : Fin k} (hi : p ∣ r i) (hj : p ∣ r j) : i = j := by
  classical
  by_contra hij
  have hdvd : r i * r j ∣ ∏ l, r l := by
    have := prod_dvd_prod_of_subset {i, j} univ r (subset_univ _)
    rwa [prod_pair hij] at this
  exact hp.not_isUnit (hsq p ((mul_dvd_mul hi hj).trans hdvd))

/-- Splitting the sum over the support `T` by the `p`-part of `r`:
`∑_{r ∈ T} f(r) = ∑_{r ∈ T, p ∤ r} (f(r) + ∑_j f(r p e_j))` when `f` vanishes off `T`. -/
lemma sum_permissibleSupport_eq {R W p : ℕ} (hp : p.Prime) (f : (Fin k → ℕ) → ℝ)
    (hf : ∀ r ∉ permissibleSupport k R W, f r = 0) :
    ∑ r ∈ permissibleSupport k R W, f r =
      ∑ r ∈ permissibleSupport k R W with ¬p ∣ ∏ i, r i, (f r + ∑ j, f (mulAt r j p)) := by
  classical
  set T := permissibleSupport k R W
  rw [sum_add_distrib, ← sum_filter_add_sum_filter_not T (fun r ↦ p ∣ ∏ i, r i), add_comm]
  congr 1
  -- each `r ∈ T` with `p ∣ ∏ r` has `p ∣ r j` for exactly one `j`
  have hone : ∀ r ∈ T.filter (fun r ↦ p ∣ ∏ i, r i),
      f r = ∑ j, if p ∣ r j then f r else 0 := by
    intro r hr
    obtain ⟨hrT, hpr⟩ := mem_filter.mp hr
    have hsq := (mem_permissibleSupport_iff.mp hrT).2.2
    obtain ⟨j, -, hj⟩ := (Prime.dvd_finsetProd_iff hp.prime _).mp hpr
    rw [sum_eq_single j (fun i _ hij ↦ ite_eq_right fun hi ↦ hij
      (eq_of_prime_dvd_of_squarefree hsq hp hi hj)) (by simp), ite_eq_left hj]
  rw [sum_congr rfl hone, sum_comm (s := T.filter fun r ↦ p ∣ ∏ i, r i),
    sum_comm (s := T.filter fun r ↦ ¬p ∣ ∏ i, r i)]
  refine sum_congr rfl fun j _ ↦ ?_
  rw [← sum_filter, filter_filter]
  symm
  refine sum_bij_ne_zero (fun r _ _ ↦ mulAt r j p) ?_ ?_ ?_ (fun _ _ _ ↦ rfl)
  · intro r hr hne
    refine mem_filter.mpr ⟨by_contra fun h ↦ hne (hf _ h), ?_, ?_⟩
    · rw [prod_mulAt]
      exact dvd_mul_right p _
    · simp [mulAt]
  · intro r₁ _ _ r₂ _ _ h
    exact mulAt_injective hp.ne_zero h
  · intro s hs hne
    obtain ⟨hsT, -, hps⟩ := mem_filter.mp hs
    have hsq := (mem_permissibleSupport_iff.mp hsT).2.2
    set r := Function.update s j (s j / p) with hr
    have hrs : mulAt r j p = s := by
      funext i
      rcases eq_or_ne i j with rfl | hij
      · simp [mulAt, hr, Nat.mul_div_cancel' hps]
      · simp [mulAt, hr, Function.update_of_ne hij]
    have hrT : r ∈ T := mem_permissibleSupport_of_dvd hsT fun i ↦ hrs ▸ dvd_mulAt r j p i
    refine ⟨r, mem_filter.mpr ⟨hrT, fun hpr ↦ ?_⟩, by rwa [hrs], hrs⟩
    have : p * p ∣ ∏ i, s i := by
      rw [← hrs, prod_mulAt]
      exact mul_dvd_mul_left p hpr
    exact hp.not_isUnit (hsq p this)

/-- The shifted variables `z_r = y_r + ∑_j c_j y_{r p e_j}` for `r ∈ T` coprime to `p`, and
`z_r = 0` otherwise. -/
noncomputable def shiftY (T : Finset (Fin k → ℕ)) (y : (Fin k → ℕ) →₀ ℝ) (p : ℕ)
    (c : Fin k → ℝ) : (Fin k → ℕ) →₀ ℝ :=
  Finsupp.onFinset T (fun r ↦ if r ∈ T ∧ ¬p ∣ ∏ i, r i then y r + ∑ j, c j * y (mulAt r j p)
    else 0) fun r hr ↦ by
      by_contra h
      exact hr (ite_eq_right fun h' ↦ h h'.1)

/-- The values of the shifted variables. -/
lemma shiftY_apply (T : Finset (Fin k → ℕ)) (y : (Fin k → ℕ) →₀ ℝ) (p : ℕ) (c : Fin k → ℝ)
    (r : Fin k → ℕ) : shiftY T y p c r =
      if r ∈ T ∧ ¬p ∣ ∏ i, r i then y r + ∑ j, c j * y (mulAt r j p) else 0 :=
  Finsupp.onFinset_apply

/-- The shifted variables are supported in `T`. -/
lemma support_shiftY_subset (T : Finset (Fin k → ℕ)) (y : (Fin k → ℕ) →₀ ℝ) (p : ℕ)
    (c : Fin k → ℝ) : (shiftY T y p c).support ⊆ T :=
  Finsupp.support_onFinset_subset

/-- The shifted variables are supported on tuples coprime to `W p`. -/
lemma hasPermissibleSupport_shiftY {R W p : ℕ} (hp : p.Prime) (y : (Fin k → ℕ) →₀ ℝ)
    (c : Fin k → ℝ) :
    (shiftY (permissibleSupport k R W) y p c).HasPermissibleSupport R (W * p) := by
  intro r hr
  rw [Finsupp.mem_support_iff, shiftY_apply] at hr
  obtain ⟨hrT, hpr⟩ : r ∈ permissibleSupport k R W ∧ ¬p ∣ ∏ i, r i := by
    by_contra h
    exact hr (ite_eq_right h)
  obtain ⟨hle, hcop, hsq⟩ := mem_permissibleSupport_iff.mp hrT
  exact mem_permissibleSupport_iff.mpr
    ⟨hle, Nat.Coprime.mul_right hcop ((Nat.coprime_comm.mp
      ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpr))), hsq⟩

/-- **Divisor sums at `a` with `p ∣ a_m`.** If `c_j = κ(p, a_j)` for every `j`, the divisor
sums of `yToL y` and `yToL z` at `a` agree. -/
theorem sum_yToL_eq_sum_yToL_shiftY {R W p : ℕ} (hp : p.Prime) {y : (Fin k → ℕ) →₀ ℝ}
    (hy : y.HasPermissibleSupport R W) (a : Fin k → ℕ) (ha : ∀ i, a i ≠ 0) (c : Fin k → ℝ)
    (hc : ∀ j, c j = divKernel p (a j)) :
    ∑ d ∈ Fintype.piFinset (fun i ↦ (a i).divisors), PrimeGaps.yToL y d =
      ∑ d ∈ Fintype.piFinset (fun i ↦ (a i).divisors),
        PrimeGaps.yToL (shiftY (permissibleSupport k R W) y p c) d := by
  classical
  set T := permissibleSupport k R W
  set z := shiftY T y p c
  have hz : z.HasPermissibleSupport R W := support_shiftY_subset T y p c
  rw [sum_yToL_eq_sum_divKernel hy a ha (T := T) hy,
    sum_yToL_eq_sum_divKernel hz a ha (T := T) hz]
  set K : (Fin k → ℕ) → ℝ := fun r ↦ ∏ i, divKernel (r i) (a i) with hK
  -- `κ(r p e_j) = c_j κ(r)` for `r ∈ T` coprime to `p`
  have hKmul : ∀ r ∈ T.filter (fun r ↦ ¬p ∣ ∏ i, r i), ∀ j,
      K (mulAt r j p) = c j * K r := by
    intro r hr j
    have hpj : ¬p ∣ r j := fun h ↦ (mem_filter.mp hr).2
      (h.trans (dvd_prod_of_mem r (mem_univ j)))
    simp only [hK, mulAt]
    rw [show (fun i ↦ divKernel (Function.update r j (p * r j) i) (a i)) =
        Function.update (fun i ↦ divKernel (r i) (a i)) j (divKernel (p * r j) (a j)) from
      funext fun i ↦ Function.apply_update (fun i x ↦ divKernel x (a i)) r j (p * r j) i,
      prod_update_of_mem (mem_univ j), ← mul_prod_erase univ (fun i ↦ divKernel (r i) (a i))
        (mem_univ j), sdiff_singleton_eq_erase, divKernel_mul _ hp hpj, hc j]
    ring
  rw [sum_permissibleSupport_eq hp (fun r ↦ y r * K r) fun r hr ↦ by
      rw [Finsupp.notMem_support_iff.mp fun h ↦ hr (hy h), zero_mul],
    sum_permissibleSupport_eq hp (fun r ↦ z r * K r) fun r hr ↦ by
      rw [Finsupp.notMem_support_iff.mp fun h ↦ hr (hz h), zero_mul]]
  refine sum_congr rfl fun r hr ↦ ?_
  have hzr : z r = y r + ∑ j, c j * y (mulAt r j p) := by
    rw [shiftY_apply, ite_eq_left (mem_filter.mp hr)]
  have hzj : ∀ j, z (mulAt r j p) = 0 := fun j ↦ by
    rw [shiftY_apply, ite_eq_right fun h ↦ h.2 (by rw [prod_mulAt]; exact dvd_mul_right p _)]
  simp only [hzr, hzj, zero_mul, sum_const_zero, add_zero]
  rw [sum_congr rfl fun j _ ↦ by rw [hKmul r hr j], add_mul, sum_mul]
  congr 1
  exact sum_congr rfl fun j _ ↦ by ring

end Erdos420
