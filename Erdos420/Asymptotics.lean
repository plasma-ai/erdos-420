module

public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Shared real estimates

Elementary estimates used across the development.

* The logarithm grows slower than every power: eventually `log x ≤ c x`,
  `c (log x)^k ≤ x`, `(log x)^n ≤ ε x^δ`, and `c (log x)² ≤ ε √x`, and
  `(log x)² ≤ (2/ε)² x^ε` for all `x ≥ 1`. Along the naturals, `log X → ∞`.
* `log 4 < 2`.
* `∑_{n ∈ S} 1/n² ≤ 2 / (K + 1)` when every element of `S` exceeds `K`.
-/

@[expose] public section

namespace Erdos420

open Filter Finset Real

/-! ### Growth of the logarithm -/

/-- Eventually `log x ≤ c x`, for `c > 0`. -/
lemma eventually_log_le_const_mul {c : ℝ} (hc : 0 < c) : ∀ᶠ x : ℝ in atTop, log x ≤ c * x := by
  filter_upwards [isLittleO_log_id_atTop.bound hc, eventually_ge_atTop 1] with x hx hx1
  rwa [norm_of_nonneg (log_nonneg hx1), id, norm_of_nonneg (by linarith)] at hx

/-- Eventually `c (log x)^k ≤ x`. -/
lemma eventually_mul_log_pow_le_self (c : ℝ) (k : ℕ) : ∀ᶠ x : ℝ in atTop, c * log x ^ k ≤ x := by
  have h := (tendsto_pow_log_div_mul_add_atTop 1 0 k one_ne_zero).eventually
    (gt_mem_nhds (show (0 : ℝ) < 1 / (|c| + 1) by positivity))
  filter_upwards [h, eventually_ge_atTop 1] with x hx hx1
  simp only [one_mul, add_zero] at hx
  have hlog : 0 ≤ log x ^ k := pow_nonneg (log_nonneg hx1) k
  rw [div_lt_div_iff₀ (by linarith) (by positivity), one_mul] at hx
  nlinarith [le_abs_self c, abs_nonneg c]

/-- Eventually `(log x)^n ≤ ε x^δ`, for `δ, ε > 0`. -/
lemma eventually_log_pow_le_mul_rpow (n : ℕ) {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, log x ^ n ≤ ε * x ^ δ := by
  filter_upwards [(isLittleO_log_rpow_rpow_atTop (n : ℝ) hδ).bound hε, eventually_ge_atTop 1]
    with x hx hx₁
  rwa [rpow_natCast, norm_of_nonneg (pow_nonneg (log_nonneg hx₁) n),
    norm_of_nonneg (rpow_nonneg (by linarith) δ)] at hx

/-- Eventually `c (log x)² ≤ ε √x`, for `ε > 0`. -/
lemma eventually_mul_log_sq_le_mul_sqrt (c : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, c * log x ^ 2 ≤ ε * √x := by
  filter_upwards [eventually_log_pow_le_mul_rpow 2 (δ := 1 / 2) (ε := ε / (|c| + 1))
    (by norm_num) (by positivity)] with x hx
  rw [← sqrt_eq_rpow] at hx
  calc c * log x ^ 2 ≤ |c| * log x ^ 2 := by gcongr; exact le_abs_self c
    _ ≤ |c| * (ε / (|c| + 1) * √x) := by gcongr
    _ = |c| / (|c| + 1) * (ε * √x) := by ring
    _ ≤ 1 * (ε * √x) := by
        gcongr
        rw [div_le_one (by positivity)]
        linarith
    _ = ε * √x := one_mul _

/-- `(log x)² ≤ (2/ε)² x^ε` for `x ≥ 1` and `ε > 0`, since `log x ≤ x^{ε/2} / (ε/2)`. -/
lemma log_sq_le_mul_rpow {x ε : ℝ} (hx : 1 ≤ x) (hε : 0 < ε) :
    log x ^ 2 ≤ (2 / ε) ^ 2 * x ^ ε := by
  have hx₀ : 0 < x := by linarith
  have hlog : log x ≤ x ^ (ε / 2) / (ε / 2) := log_le_rpow_div hx₀.le (by positivity)
  have hlog₀ : 0 ≤ log x := log_nonneg hx
  calc log x ^ 2 ≤ (x ^ (ε / 2) / (ε / 2)) ^ 2 := by gcongr
    _ = (2 / ε) ^ 2 * x ^ ε := by
        rw [div_pow, ← rpow_natCast (x ^ (ε / 2)), ← rpow_mul hx₀.le]
        field_simp
        ring_nf

/-- `log X → ∞` along the naturals. -/
lemma tendsto_log_natCast_atTop : Tendsto (fun X : ℕ ↦ log X) atTop atTop :=
  tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

/-! ### `log 4` -/

/-- `log 4 < 2`. -/
lemma log_four_lt_two : log 4 < 2 := by
  rw [log_four_eq]
  linarith [log_two_lt_d9]

/-! ### Sums of `1/n²` -/

/-- `∑_{n ∈ S} 1/n² ≤ 2 / (K + 1)` when every element of `S` exceeds `K`. -/
lemma sum_one_div_sq_le_of_lt {S : Finset ℕ} {K : ℕ} (hS : ∀ n ∈ S, K < n) :
    ∑ n ∈ S, 1 / (n : ℝ) ^ 2 ≤ 2 / ((K : ℝ) + 1) := by
  calc ∑ n ∈ S, 1 / (n : ℝ) ^ 2 ≤ ∑ n ∈ Ioo K (S.sup id + 1), ((n : ℝ) ^ 2)⁻¹ := by
        simp_rw [one_div]
        refine sum_le_sum_of_subset_of_nonneg (fun n hn ↦ mem_Ioo.mpr ⟨hS n hn, ?_⟩)
          fun _ _ _ ↦ by positivity
        exact Nat.lt_succ_of_le (le_sup (f := id) hn)
    _ ≤ 2 / ((K : ℝ) + 1) := sum_Ioo_inv_sq_le K _

end Erdos420
