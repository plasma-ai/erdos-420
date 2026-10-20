module

public import Erdos420.Elementary.Mertens.First

/-!
# Mertens' second theorem

`∑_{p ≤ x} 1/p = log log x + O(1)`, by partial summation from Mertens' first theorem
`S(n) = ∑_{p ≤ n} log p / p = log n + O(1)`. Write `u = log n` and `v = log (n + 1)`. The error
`G(n) = ∑_{p ≤ n} 1/p − S(n) / log n − log log n` moves from `n` to `n + 1` by
`(S(n) − u) (1/u − 1/v) + (1 − u/v − log (v/u))`, and both terms are `O(1/u − 1/v)`, which
telescopes.
-/

@[expose] public section

namespace Erdos420

open Finset Real

/-- Adding `n + 1` to the primes moves `∑ 1/p` by `1 / log (n + 1)` times the move of
`∑ log p / p`. -/
private lemma sum_primesLE_succ_inv_sub {n : ℕ} (hn : 1 ≤ n) :
    ∑ p ∈ Nat.primesLE (n + 1), (1 : ℝ) / p - ∑ p ∈ Nat.primesLE n, (1 : ℝ) / p =
      (∑ p ∈ Nat.primesLE (n + 1), log p / p - ∑ p ∈ Nat.primesLE n, log p / p) /
        log (n + 1) := by
  rw [Nat.primesLE_eq_filter_range, Nat.primesLE_eq_filter_range, sum_filter, sum_filter,
    sum_filter, sum_filter, sum_range_succ (n := n + 1), sum_range_succ (n := n + 1),
    add_sub_cancel_left, add_sub_cancel_left]
  split_ifs
  · have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have : log ((n : ℝ) + 1) ≠ 0 := (log_pos (by linarith)).ne'
    push_cast
    field_simp
  · simp

/-- The partial-summation error `∑_{p ≤ n} 1/p − (∑_{p ≤ n} log p / p) / log n − log log n`. -/
private noncomputable def error (n : ℕ) : ℝ :=
  ∑ p ∈ Nat.primesLE n, (1 : ℝ) / p - (∑ p ∈ Nat.primesLE n, log p / p) / log n - log (log n)

/-- `|G(n + 1) − G(n)| ≤ 4 (1 / log n − 1 / log (n + 1))`. -/
private lemma abs_error_succ_sub_le {n : ℕ} (hn : 2 ≤ n) :
    |error (n + 1) - error n| ≤ 4 * (1 / log n - 1 / log (n + 1)) := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hstep := sum_primesLE_succ_inv_sub (by omega : 1 ≤ n)
  have hS := abs_sum_primesLE_log_div_sub_log_le n
  set S := ∑ p ∈ Nat.primesLE n, log p / p
  set S' := ∑ p ∈ Nat.primesLE (n + 1), log p / p
  set u := log (n : ℝ)
  set v := log ((n : ℝ) + 1)
  have hu : 0 < u := log_pos (by linarith)
  have huv : u < v := log_lt_log (by linarith) (by linarith)
  have hv : 0 < v := hu.trans huv
  -- `v − u = log (1 + 1/n) ≤ 1/n ≤ 1`
  have hvu : v - u ≤ 1 := by
    have h : v - u ≤ (n + 1) / n - 1 := by
      rw [← log_div (by positivity) (by positivity)]
      exact log_le_sub_one_of_pos (by positivity)
    have h' : ((n : ℝ) + 1) / n - 1 = 1 / n := by field_simp; ring
    rw [h'] at h
    linarith [(div_le_one (by positivity : (0 : ℝ) < n)).mpr (by linarith : (1 : ℝ) ≤ n)]
  -- `1 − u/v ≤ log v − log u ≤ v/u − 1`
  have h₁ : 1 - u / v ≤ log v - log u := by
    rw [← log_div hv.ne' hu.ne', ← inv_div]
    exact one_sub_inv_le_log_of_pos (by positivity)
  have h₂ : log v - log u ≤ v / u - 1 := by
    rw [← log_div hv.ne' hu.ne']
    exact log_le_sub_one_of_pos (by positivity)
  set w := 1 / u - 1 / v
  have hw : 0 ≤ w := sub_nonneg.mpr (one_div_le_one_div_of_le hu huv.le)
  have he₁ : error (n + 1) = ∑ p ∈ Nat.primesLE (n + 1), (1 : ℝ) / p - S' / v - log v := by
    simp only [error, S', v]
    push_cast
    rfl
  have he₀ : error n = ∑ p ∈ Nat.primesLE n, (1 : ℝ) / p - S / u - log u := rfl
  have hdiff : error (n + 1) - error n = (S - u) * w + (1 - u / v - (log v - log u)) := by
    have h : (S - u) * w + (1 - u / v - (log v - log u)) = S / u - S / v - (log v - log u) := by
      simp only [w]
      field_simp
      ring
    rw [h, he₁, he₀]
    linear_combination hstep
  -- `log v − log u − (1 − u/v) ≤ (v/u − 1) − (1 − u/v) = (v − u) w ≤ w`
  have hgap : v / u - 1 - (1 - u / v) = (v - u) * w := by
    simp only [w]
    field_simp
  have hgap' : (v - u) * w ≤ w := by nlinarith
  have hSw : |(S - u) * w| ≤ 3 * w := by
    rw [abs_mul, abs_of_nonneg hw]
    exact mul_le_mul_of_nonneg_right hS hw
  rw [hdiff]
  rw [abs_le] at hSw ⊢
  constructor <;> linarith

/-- `|G(n) − G(2)| ≤ 4 (1 / log 2 − 1 / log n)`. -/
private lemma abs_error_sub_error_two_le {n : ℕ} (hn : 2 ≤ n) :
    |error n - error 2| ≤ 4 * (1 / log 2 - 1 / log n) := by
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    have h := abs_error_succ_sub_le hn
    push_cast at h ⊢
    calc |error (n + 1) - error 2|
        ≤ |error (n + 1) - error n| + |error n - error 2| := abs_sub_le _ _ _
      _ ≤ 4 * (1 / log n - 1 / log (n + 1)) + 4 * (1 / log 2 - 1 / log n) := add_le_add h ih
      _ = 4 * (1 / log 2 - 1 / log (n + 1)) := by ring

/-- Mertens' second theorem: `∑_{p ≤ x} 1/p = log log x + O(1)`. -/
theorem exists_abs_sum_inv_prime_sub_log_log_le : ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x →
    |∑ p ∈ (Finset.Iic ⌊x⌋₊).filter Nat.Prime, (1 : ℝ) / p - Real.log (Real.log x)| ≤ C := by
  have hlog2 : 0 < log (2 : ℝ) := log_pos one_lt_two
  refine ⟨|error 2| + 4 / log 2 + (1 + 3 / log 2) + log 2, fun x hx ↦ ?_⟩
  set n := ⌊x⌋₊
  have hn : 2 ≤ n := Nat.le_floor (by exact_mod_cast hx)
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hprimes : (Finset.Iic n).filter Nat.Prime = Nat.primesLE n := by
    ext p
    simp [Nat.mem_primesLE]
  rw [hprimes]
  set S := ∑ p ∈ Nat.primesLE n, log p / p
  set u := log (n : ℝ)
  have hu : log 2 ≤ u := log_le_log two_pos hn'
  have hu₀ : 0 < u := hlog2.trans_le hu
  -- `|G(n)| ≤ |G(2)| + 4 / log 2`
  have hG : |error n| ≤ |error 2| + 4 / log 2 := by
    have h := abs_error_sub_error_two_le hn
    have : 0 ≤ 1 / u := by positivity
    have h' : 4 * (1 / log 2 - 1 / u) ≤ 4 / log 2 := by
      rw [mul_sub, mul_one_div]
      linarith [mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) this]
    linarith [abs_sub_abs_le_abs_sub (error n) (error 2)]
  -- `|S(n) / log n| ≤ 1 + 3 / log 2`
  have hSu : |S / u| ≤ 1 + 3 / log 2 := by
    have h : S / u = 1 + (S - u) / u := by field_simp; ring
    rw [h]
    calc |1 + (S - u) / u| ≤ |(1 : ℝ)| + |(S - u) / u| := abs_add_le _ _
      _ ≤ 1 + 3 / log 2 := by
        rw [abs_one, abs_div, abs_of_pos hu₀]
        gcongr
        · exact abs_sum_primesLE_log_div_sub_log_le n
  -- `log log n ≤ log log x ≤ log 2 + log log n`, since `n ≤ x < n + 1 ≤ 2n`
  have hx₀ : (n : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hx₁ : x ≤ 2 * n := by linarith [Nat.lt_floor_add_one x]
  have hlogx : u ≤ log x := log_le_log (by linarith) hx₀
  have hlogx' : log x ≤ 2 * u := by
    calc log x ≤ log (2 * n) := log_le_log (by linarith) hx₁
      _ = log 2 + u := log_mul two_ne_zero (by positivity)
      _ ≤ 2 * u := by linarith
  have hll : log u ≤ log (log x) := log_le_log hu₀ hlogx
  have hll' : log (log x) ≤ log 2 + log u := by
    rw [← log_mul two_ne_zero hu₀.ne']
    exact log_le_log (by linarith) hlogx'
  have heq : ∑ p ∈ Nat.primesLE n, (1 : ℝ) / p - log (log x) =
      error n + S / u + (log u - log (log x)) := by
    simp only [error, S, u]
    ring
  rw [heq]
  rw [abs_le] at hG hSu ⊢
  constructor <;> linarith [abs_nonneg (error 2)]

end Erdos420
