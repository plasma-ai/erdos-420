module

public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Removing the smoothing weight

If `∑_{m ≤ y} a_m (1 - m / y) = δ y / 2 + O(B y^{7/8})` at every half-integer
`y ≥ 2`, with `|a_m| ≤ Λ(m)`, then `∑_{m ≤ x} a_m = δ x + O((1 + log x + B) x^{15/16})`.

`W(y) = ∑_{m ≤ y} a_m (y - m)` is `y` times the smoothed sum, so
`W(y) = δ y² / 2 + O(B y^{15/8})`. Differencing at `y` and `y + h` with
`h ≈ y^{15/16}` gives `h ∑_{m ≤ y} a_m` up to the `O(h² log y)` terms in
`(y, y + h]`.
-/

@[expose] public section

namespace Erdos420

open ArithmeticFunction

/-- A half-integer is not a natural number. -/
lemma natCast_ne_natCast_add_one_half (k m : ℕ) : (m : ℝ) ≠ k + 1 / 2 := by
  intro hm
  have h : ((2 * m : ℕ) : ℝ) = (2 * k + 1 : ℕ) := by
    push_cast
    linarith
  have := Nat.cast_injective h
  omega

/-- The integer part of a half-integer. -/
lemma floor_natCast_add_one_half (k : ℕ) : ⌊(k : ℝ) + 1 / 2⌋₊ = k := by
  rw [Nat.floor_eq_iff (by positivity)]
  constructor <;> linarith

/-- **Unsmoothing.** A smoothed asymptotic at the half-integers with error `O(B y^{7/8})`
gives a sharp one with error `O((1 + log x + B) x^{15/16})`. -/
theorem norm_sum_sub_mul_le {a : ℕ → ℂ} (ha : ∀ m, ‖a m‖ ≤ Λ m) {δ : ℂ} (hδ : ‖δ‖ ≤ 1)
    {B : ℝ} (hB : 0 ≤ B)
    (hS : ∀ k : ℕ, 2 ≤ k → ‖∑ m ∈ Finset.Icc 1 k, a m * (1 - m / ((k : ℝ) + 1 / 2 : ℝ)) -
      δ * ((k : ℝ) + 1 / 2 : ℝ) / 2‖ ≤ B * ((k : ℝ) + 1 / 2) ^ (7 / 8 : ℝ))
    {x : ℝ} (hx : 2 ≤ x) :
    ‖∑ m ∈ Finset.Icc 1 ⌊x⌋₊, a m - δ * x‖ ≤
      (25 + 4 * Real.log x + 34 * B) * x ^ (15 / 16 : ℝ) := by
  set n := ⌊x⌋₊ with hn
  have hn₁ : (n : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hn₂ : x < n + 1 := Nat.lt_floor_add_one x
  have hn₃ : 2 ≤ n := Nat.le_floor (by exact_mod_cast hx)
  set y : ℝ := n + 1 / 2 with hy
  have hy₂ : 2 ≤ y := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn₃
    linarith
  -- the step `h ≈ y^{15/16}`
  set u : ℝ := y ^ (15 / 16 : ℝ) with hu
  set h : ℕ := ⌊u⌋₊ + 1 with hh
  have hu₁ : 1 ≤ u := Real.one_le_rpow (by linarith) (by norm_num)
  have huy : u ≤ y := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ y)
      (show (15 / 16 : ℝ) ≤ 1 by norm_num)
  have hhu : u < h := by
    simp only [hh]
    push_cast
    exact Nat.lt_floor_add_one u
  have hhu' : (h : ℝ) ≤ u + 1 := by
    simp only [hh]
    push_cast
    linarith [Nat.floor_le (by linarith : 0 ≤ u)]
  set z : ℝ := y + h with hz
  have hz' : z = ((n + h : ℕ) : ℝ) + 1 / 2 := by
    push_cast
    ring
  have hz₄ : z ≤ 4 * y := by linarith
  -- `W(v) = ∑_{m ≤ v} a_m (v - m)` is `v` times the smoothed sum
  set W : ℝ → ℂ := fun v ↦ ∑ m ∈ Finset.Icc 1 ⌊v⌋₊, a m * (v - m)
  have hW : ∀ k : ℕ, 2 ≤ k → ‖W (k + 1 / 2) - δ * ((k : ℝ) + 1 / 2 : ℝ) ^ 2 / 2‖ ≤
      B * ((k : ℝ) + 1 / 2) ^ (15 / 8 : ℝ) := by
    intro k hk
    set v : ℝ := k + 1 / 2 with hv
    have hv₀ : 0 < v := by positivity
    have hvc : (v : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hv₀.ne'
    have heq : W v - δ * (v : ℂ) ^ 2 / 2 =
        v * (∑ m ∈ Finset.Icc 1 k, a m * (1 - m / (v : ℂ)) - δ * v / 2) := by
      simp only [W, hv, floor_natCast_add_one_half, mul_sub, Finset.mul_sum]
      congr 1
      · refine Finset.sum_congr rfl fun m _ ↦ ?_
        rw [← hv]
        field_simp
      · ring
    rw [heq, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hv₀]
    calc v * ‖∑ m ∈ Finset.Icc 1 k, a m * (1 - m / (v : ℂ)) - δ * v / 2‖
        ≤ v * (B * v ^ (7 / 8 : ℝ)) := by
          gcongr
          exact hS k hk
      _ = B * v ^ (15 / 8 : ℝ) := by
          rw [show (15 / 8 : ℝ) = 1 + 7 / 8 by norm_num, Real.rpow_add hv₀, Real.rpow_one]
          ring
  have hWy := hW n hn₃
  have hWz := hW (n + h) (by omega)
  rw [← hz'] at hWz
  -- `W(z) - W(y) = h S + R`, with `R` the terms in `(y, z]`
  set S := ∑ m ∈ Finset.Icc 1 n, a m with hSdef
  set R := ∑ m ∈ Finset.Ioc n (n + h), a m * (z - m) with hRdef
  have hIcc (k : ℕ) : Finset.Icc 1 k = Finset.Ioc 0 k := by
    ext m
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  have hzc : (z : ℂ) = y + h := by
    rw [hz]
    push_cast
    ring
  have hWz₀ : W z = ∑ m ∈ Finset.Icc 1 (n + h), a m * (z - m) := by
    simp only [W]
    rw [show ⌊z⌋₊ = n + h by rw [hz']; exact floor_natCast_add_one_half _]
  have hWy₀ : W y = ∑ m ∈ Finset.Icc 1 n, a m * (y - m) := by
    simp only [W]
    rw [show ⌊y⌋₊ = n from floor_natCast_add_one_half n]
  have hdiff : W z - W y = h * S + R := by
    rw [hWz₀, hWy₀, hSdef, hRdef, hIcc, hIcc,
      ← Finset.sum_Ioc_consecutive _ (Nat.zero_le n) (Nat.le_add_right n h), Finset.mul_sum,
      add_sub_right_comm, ← Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl fun m _ ↦ ?_
    rw [hzc]
    ring
  -- `‖R‖ ≤ h² log z`
  have hR : ‖R‖ ≤ h ^ 2 * Real.log z := by
    have hterm : ∀ m ∈ Finset.Ioc n (n + h), ‖a m * (z - m)‖ ≤ h * Real.log z := by
      intro m hm
      rw [Finset.mem_Ioc] at hm
      have hm₁ : (n : ℝ) + 1 ≤ m := by exact_mod_cast hm.1
      have hm₂ : (m : ℝ) ≤ n + h := by exact_mod_cast hm.2
      have hm₀ : (0 : ℝ) < m := by linarith
      rw [norm_mul, show (z : ℂ) - m = ((z - m : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (by linarith)]
      have hΛ : ‖a m‖ ≤ Real.log z :=
        (ha m).trans (vonMangoldt_le_log.trans (Real.log_le_log hm₀ (by linarith)))
      have hlog : 0 ≤ Real.log z := Real.log_nonneg (by linarith)
      calc ‖a m‖ * (z - m) ≤ Real.log z * h := mul_le_mul hΛ (by linarith) (by linarith) hlog
        _ = h * Real.log z := by ring
    calc ‖R‖ ≤ ∑ m ∈ Finset.Ioc n (n + h), ‖a m * (z - m)‖ := norm_sum_le _ _
      _ ≤ ∑ _m ∈ Finset.Ioc n (n + h), h * Real.log z := Finset.sum_le_sum hterm
      _ = h ^ 2 * Real.log z := by
          rw [Finset.sum_const, Nat.card_Ioc, show n + h - n = h by omega, nsmul_eq_mul]
          ring
  -- the main terms
  have hpow : z ^ (15 / 8 : ℝ) ≤ 16 * y ^ (15 / 8 : ℝ) := by
    calc z ^ (15 / 8 : ℝ) ≤ (4 * y) ^ (15 / 8 : ℝ) := by gcongr
      _ = 4 ^ (15 / 8 : ℝ) * y ^ (15 / 8 : ℝ) := Real.mul_rpow (by norm_num) (by linarith)
      _ ≤ 4 ^ (2 : ℝ) * y ^ (15 / 8 : ℝ) := by
          gcongr
          · norm_num
          · norm_num
      _ = 16 * y ^ (15 / 8 : ℝ) := by norm_num
  have hu₂ : y ^ (15 / 8 : ℝ) = u ^ 2 := by
    rw [hu, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
    norm_num
  have hkey : (h : ℂ) * (S - δ * y) =
      (W z - δ * (z : ℂ) ^ 2 / 2) - (W y - δ * (y : ℂ) ^ 2 / 2) - R + δ * (h : ℂ) ^ 2 / 2 := by
    linear_combination -hdiff + δ / 2 * ((z : ℂ) + y + h) * hzc
  have hh₀ : (0 : ℝ) < h := by linarith
  have hlogz : 0 ≤ Real.log z := Real.log_nonneg (by linarith)
  have hWy' : ‖W y - δ * (y : ℂ) ^ 2 / 2‖ ≤ B * y ^ (15 / 8 : ℝ) := hWy
  have hmain : h * ‖S - δ * y‖ ≤ 17 * B * u ^ 2 + h ^ 2 * (Real.log z + 1 / 2) := by
    have h₁ : ‖(h : ℂ) * (S - δ * y)‖ = h * ‖S - δ * y‖ := by
      rw [norm_mul, Complex.norm_natCast]
    have h₂ : ‖δ * (h : ℂ) ^ 2 / 2‖ ≤ h ^ 2 / 2 := by
      rw [norm_div, norm_mul, norm_pow, Complex.norm_natCast, Complex.norm_ofNat]
      have : ‖δ‖ * (h : ℝ) ^ 2 ≤ 1 * h ^ 2 := by gcongr
      linarith
    rw [← h₁, hkey]
    have h₃ := norm_add_le ((W z - δ * (z : ℂ) ^ 2 / 2) - (W y - δ * (y : ℂ) ^ 2 / 2) - R)
      (δ * (h : ℂ) ^ 2 / 2)
    have h₄ := norm_sub_le ((W z - δ * (z : ℂ) ^ 2 / 2) - (W y - δ * (y : ℂ) ^ 2 / 2)) R
    have h₅ := norm_sub_le (W z - δ * (z : ℂ) ^ 2 / 2) (W y - δ * (y : ℂ) ^ 2 / 2)
    have h₆ : B * z ^ (15 / 8 : ℝ) ≤ B * (16 * y ^ (15 / 8 : ℝ)) := by gcongr
    rw [hu₂] at hWy' h₆
    linarith
  have hS' : ‖S - δ * y‖ ≤ 17 * B * u + (u + 1) * (Real.log z + 1 / 2) := by
    have h₁ := mul_le_mul_of_nonneg_left hhu.le (by positivity : 0 ≤ 17 * B * u)
    have h₂ := mul_le_mul_of_nonneg_left hhu' (by positivity : 0 ≤ h * (Real.log z + 1 / 2))
    refine le_of_mul_le_mul_left ?_ hh₀
    calc (h : ℝ) * ‖S - δ * y‖ ≤ 17 * B * u ^ 2 + h ^ 2 * (Real.log z + 1 / 2) := hmain
      _ ≤ h * (17 * B * u + (u + 1) * (Real.log z + 1 / 2)) := by nlinarith
  have hSx : ‖S - δ * x‖ ≤ ‖S - δ * y‖ + 1 := by
    have h₁ : S - δ * x = (S - δ * y) + δ * ((y - x : ℝ) : ℂ) := by
      push_cast
      ring
    rw [h₁]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have h₂ : |y - x| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
    nlinarith [norm_nonneg δ, abs_nonneg (y - x)]
  have hux : u ≤ 2 * x ^ (15 / 16 : ℝ) := by
    calc u ≤ (2 * x) ^ (15 / 16 : ℝ) := by
          rw [hu]
          gcongr
          linarith
      _ = 2 ^ (15 / 16 : ℝ) * x ^ (15 / 16 : ℝ) := Real.mul_rpow (by norm_num) (by linarith)
      _ ≤ 2 ^ (1 : ℝ) * x ^ (15 / 16 : ℝ) := by
          gcongr
          · norm_num
          · norm_num
      _ = 2 * x ^ (15 / 16 : ℝ) := by rw [Real.rpow_one]
  have hlogz' : Real.log z ≤ 21 / 10 + Real.log x := by
    have h₁ : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
      norm_num
    calc Real.log z ≤ Real.log (8 * x) := Real.log_le_log (by linarith) (by linarith)
      _ = Real.log 8 + Real.log x := Real.log_mul (by norm_num) (by linarith)
      _ ≤ _ := by
          linarith [Real.log_two_lt_d9]
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hx₁₅ : 0 ≤ x ^ (15 / 16 : ℝ) := by positivity
  have h₁ : ‖S - δ * x‖ ≤ u * (17 * B + 2 * Real.log z + 3) := by
    have h₂ : 1 * Real.log z ≤ u * Real.log z := mul_le_mul_of_nonneg_right hu₁ hlogz
    have h₃ : (u + 1) * (Real.log z + 1 / 2) = u * Real.log z + Real.log z + u / 2 + 1 / 2 := by
      ring
    have h₄ : u * (17 * B + 2 * Real.log z + 3) = 17 * B * u + 2 * (u * Real.log z) + 3 * u := by
      ring
    linarith
  calc ‖∑ m ∈ Finset.Icc 1 ⌊x⌋₊, a m - δ * x‖ = ‖S - δ * x‖ := rfl
    _ ≤ u * (17 * B + 2 * Real.log z + 3) := h₁
    _ ≤ (2 * x ^ (15 / 16 : ℝ)) * (17 * B + 2 * (21 / 10 + Real.log x) + 3) := by
        gcongr
    _ = (34 * B + 72 / 5 + 4 * Real.log x) * x ^ (15 / 16 : ℝ) := by ring
    _ ≤ (25 + 4 * Real.log x + 34 * B) * x ^ (15 / 16 : ℝ) :=
        mul_le_mul_of_nonneg_right (by linarith) hx₁₅

end Erdos420
