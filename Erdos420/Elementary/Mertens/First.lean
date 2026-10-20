module

public import Mathlib.Data.Nat.Choose.Factorization
public import Mathlib.Data.Nat.Prime.Factorial
public import Mathlib.NumberTheory.Chebyshev

/-!
# Mertens' first theorem

`|∑_{p ≤ n} log p / p − log n| ≤ 3`, from Legendre's formula `log n! = ∑_{p ≤ n} v_p(n!) log p`.

* Upper bound: `∑_{p ≤ n} ⌊n / p⌋ log p ≤ log n! ≤ n log n`, and the floors cost
  `θ(n) ≤ n log 4`.
* Lower bound: `v_p(n!) ≤ n / (p − 1)` and `n log n − n ≤ log n!` give
  `log n − 1 ≤ ∑_{p ≤ n} log p / (p − 1)`, and `∑_p log p / (p (p − 1)) ≤ 2` telescopes against
  `(log n + 2) / n`.
-/

@[expose] public section

namespace Erdos420

open Finset Real
open scoped Nat

/-! ### Upper bound -/

/-- `∑_{p ≤ n} ⌊n / p⌋ log p ≤ log n!`. -/
private lemma sum_primesLE_div_mul_log_le (n : ℕ) :
    ∑ p ∈ Nat.primesLE n, ((n / p : ℕ) : ℝ) * log p ≤ log (n ! : ℕ) := by
  rw [log_nat_eq_sum_factorization, Finsupp.sum, Nat.support_factorization]
  calc ∑ p ∈ Nat.primesLE n, ((n / p : ℕ) : ℝ) * log p
      ≤ ∑ p ∈ Nat.primesLE n, ((n !).factorization p : ℝ) * log p := by
        refine sum_le_sum fun p hp ↦ ?_
        have hp' := (Nat.mem_primesLE.mp hp).2
        refine mul_le_mul_of_nonneg_right ?_ (log_nonneg (by exact_mod_cast hp'.one_lt.le))
        rw [Nat.factorization_factorial hp' (b := Nat.log p n + 2) (by omega)]
        calc ((n / p : ℕ) : ℝ) = ((n / p ^ 1 : ℕ) : ℝ) := by rw [pow_one]
          _ ≤ ((∑ i ∈ Ico 1 (Nat.log p n + 2), n / p ^ i : ℕ) : ℝ) := by
            exact_mod_cast (single_le_sum (f := fun i ↦ n / p ^ i) (fun _ _ ↦ Nat.zero_le _)
              (mem_Ico.mpr ⟨le_rfl, by omega⟩) : n / p ^ 1 ≤ _)
    _ ≤ ∑ p ∈ (n !).primeFactors, ((n !).factorization p : ℝ) * log p := by
        refine sum_le_sum_of_subset_of_nonneg (fun p hp ↦ ?_) fun p hp _ ↦ ?_
        · have hp' := Nat.mem_primesLE.mp hp
          exact Nat.mem_primeFactors.mpr
            ⟨hp'.2, (Nat.Prime.dvd_factorial hp'.2).mpr hp'.1, Nat.factorial_ne_zero n⟩
        · exact mul_nonneg (Nat.cast_nonneg _)
            (log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt.le))

/-- Mertens' first theorem in Chebyshev's form: `∑_{p ≤ n} log p / p ≤ log n + log 4`. -/
theorem sum_primesLE_log_div_le {n : ℕ} (hn : 1 ≤ n) :
    ∑ p ∈ Nat.primesLE n, log p / p ≤ log n + log 4 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hfloor : ∀ p ∈ Nat.primesLE n, (n : ℝ) * (log p / p) ≤ ((n / p : ℕ) + 1) * log p := by
    intro p hp
    have hp' := (Nat.mem_primesLE.mp hp).2
    have hp₀ : (0 : ℝ) < p := by exact_mod_cast hp'.pos
    have hlt : (n : ℝ) < ((n / p : ℕ) + 1) * p := by
      have := Nat.lt_div_mul_add (a := n) hp'.pos
      rw [add_mul, one_mul]
      exact_mod_cast this
    rw [← mul_div_assoc, div_le_iff₀ hp₀, mul_right_comm]
    exact mul_le_mul_of_nonneg_right hlt.le (log_nonneg (by exact_mod_cast hp'.one_lt.le))
  have hlogfac : log (n ! : ℕ) ≤ n * log n := by
    rw [← log_pow]
    exact log_le_log (by exact_mod_cast Nat.factorial_pos n)
      (by exact_mod_cast Nat.factorial_le_pow n)
  have htheta := Chebyshev.theta_le_log4_mul_x hn'.le
  rw [Chebyshev.theta_eq_sum_primesLE_log] at htheta
  have h : (n : ℝ) * ∑ p ∈ Nat.primesLE n, log p / p ≤ n * (log n + log 4) := by
    calc (n : ℝ) * ∑ p ∈ Nat.primesLE n, log p / p
        ≤ ∑ p ∈ Nat.primesLE n, ((n / p : ℕ) + 1) * log p := by
          rw [mul_sum]
          exact sum_le_sum hfloor
      _ = ∑ p ∈ Nat.primesLE n, ((n / p : ℕ) : ℝ) * log p + ∑ p ∈ Nat.primesLE n, log p := by
          rw [← sum_add_distrib]
          exact sum_congr rfl fun p _ ↦ by ring
      _ ≤ n * log n + log 4 * n :=
          add_le_add ((sum_primesLE_div_mul_log_le n).trans hlogfac) htheta
      _ = n * (log n + log 4) := by ring
  exact le_of_mul_le_mul_left h hn'

/-! ### Lower bound -/

/-- `∑_{p ≤ n} log p / (p (p − 1)) ≤ 2 − (log n + 2) / n`. -/
private lemma sum_primesLE_log_div_mul_sub_one_le' {n : ℕ} (hn : 1 ≤ n) :
    ∑ p ∈ Nat.primesLE n, log p / (p * (p - 1)) ≤ 2 - (log n + 2) / n := by
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hterm : (if n + 1 ∈ Nat.primesLE (n + 1) then
        log ((n + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) * ((n + 1 : ℕ) - 1)) else 0) ≤
        log (n + 1) / ((n + 1) * n) := by
      split_ifs
      · push_cast
        rw [add_sub_cancel_right]
      · exact div_nonneg (log_nonneg (by linarith)) (by positivity)
    have hsplit : ∑ p ∈ Nat.primesLE (n + 1), log p / (p * (p - 1)) =
        ∑ p ∈ Nat.primesLE n, log p / (p * (p - 1)) +
          if n + 1 ∈ Nat.primesLE (n + 1) then
            log ((n + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) * ((n + 1 : ℕ) - 1)) else 0 := by
      rw [Nat.primesLE_eq_filter_range, Nat.primesLE_eq_filter_range, sum_filter, sum_filter,
        sum_range_succ (n := n + 1)]
      simp
    -- `(n + 1) (log (n + 1) − log n) ≤ (n + 1) / n ≤ 2`
    have hlog : (n + 1) * (log (n + 1) - log n) ≤ 2 := by
      have h₁ : log (n + 1) - log n ≤ (n + 1) / n - 1 := by
        rw [← log_div (by positivity) (by positivity)]
        exact log_le_sub_one_of_pos (by positivity)
      have h₂ : ((n : ℝ) + 1) / n - 1 = 1 / n := by field_simp; ring
      rw [h₂] at h₁
      calc (n + 1) * (log (n + 1) - log n) ≤ (n + 1) * (1 / n) :=
            mul_le_mul_of_nonneg_left h₁ (by positivity)
        _ = 1 + 1 / n := by field_simp
        _ ≤ 2 := by linarith [(div_le_one (by positivity : (0 : ℝ) < n)).mpr hn']
    rw [hsplit]
    push_cast
    calc ∑ p ∈ Nat.primesLE n, log p / (p * (p - 1)) + _
        ≤ 2 - (log n + 2) / n + log (n + 1) / ((n + 1) * n) :=
          add_le_add ih (by exact_mod_cast hterm)
      _ ≤ 2 - (log (n + 1) + 2) / (n + 1) := by
        have h : (log n + 2) / n - (log (n + 1) + 2) / (n + 1) - log (n + 1) / ((n + 1) * n) =
            (2 - (n + 1) * (log (n + 1) - log n)) / (n * (n + 1)) := by
          field_simp
          ring
        have := div_nonneg (sub_nonneg.mpr hlog) (by positivity : (0 : ℝ) ≤ n * (n + 1))
        linarith

/-- `∑_{p ≤ n} log p / (p (p − 1)) ≤ 2`. -/
lemma sum_primesLE_log_div_mul_sub_one_le (n : ℕ) :
    ∑ p ∈ Nat.primesLE n, log p / (p * (p - 1)) ≤ 2 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  refine (sum_primesLE_log_div_mul_sub_one_le' hn).trans ?_
  have : (0 : ℝ) ≤ (log n + 2) / n :=
    div_nonneg (by linarith [log_natCast_nonneg n]) (Nat.cast_nonneg n)
  linarith

/-- `log n − 3 ≤ ∑_{p ≤ n} log p / p`. -/
private lemma log_sub_three_le_sum_primesLE_log_div {n : ℕ} (hn : 1 ≤ n) :
    log n - 3 ≤ ∑ p ∈ Nat.primesLE n, log p / p := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  -- `n log n − n ≤ log n!`, from `n^n / n! ≤ e^n`
  have hfac : n * log n - n ≤ log (n ! : ℕ) := by
    have h := Real.pow_div_factorial_le_exp (x := (n : ℝ)) hn'.le n
    have hfac₀ : (0 : ℝ) < (n ! : ℕ) := by exact_mod_cast Nat.factorial_pos n
    rw [← log_le_log_iff (by positivity) (exp_pos _), log_exp, log_div (by positivity)
      hfac₀.ne', log_pow] at h
    linarith
  -- `log n! ≤ ∑_{p ≤ n} n / (p − 1) · log p`, from `v_p(n!) ≤ n / (p − 1)`
  have hlog : log (n ! : ℕ) ≤ ∑ p ∈ Nat.primesLE n, n / (p - 1) * log p := by
    rw [log_nat_eq_sum_factorization, Finsupp.sum, Nat.support_factorization]
    calc ∑ p ∈ (n !).primeFactors, ((n !).factorization p : ℝ) * log p
        ≤ ∑ p ∈ Nat.primesLE n, ((n !).factorization p : ℝ) * log p := by
          refine sum_le_sum_of_subset_of_nonneg (fun p hp ↦ ?_) fun p hp _ ↦ ?_
          · have hp' := Nat.mem_primeFactors.mp hp
            exact Nat.mem_primesLE.mpr ⟨(Nat.Prime.dvd_factorial hp'.1).mp hp'.2.1, hp'.1⟩
          · exact mul_nonneg (Nat.cast_nonneg _)
              (log_nonneg (by exact_mod_cast (Nat.mem_primesLE.mp hp).2.one_lt.le))
      _ ≤ ∑ p ∈ Nat.primesLE n, n / (p - 1) * log p := by
          refine sum_le_sum fun p hp ↦ ?_
          have hp' := (Nat.mem_primesLE.mp hp).2
          refine mul_le_mul_of_nonneg_right ?_ (log_nonneg (by exact_mod_cast hp'.one_lt.le))
          calc ((n !).factorization p : ℝ) ≤ ((n / (p - 1) : ℕ) : ℝ) := by
                exact_mod_cast Nat.factorization_factorial_le_div_pred hp' n
            _ ≤ (n : ℝ) / ((p - 1 : ℕ) : ℝ) := Nat.cast_div_le
            _ = n / (p - 1) := by rw [Nat.cast_sub hp'.one_le, Nat.cast_one]
  -- `n / (p − 1) = n / p + n / (p (p − 1))`
  have hsplit : ∑ p ∈ Nat.primesLE n, n / (p - 1) * log p =
      n * (∑ p ∈ Nat.primesLE n, log p / p + ∑ p ∈ Nat.primesLE n, log p / (p * (p - 1))) := by
    rw [← sum_add_distrib, mul_sum]
    refine sum_congr rfl fun p hp ↦ ?_
    have hp' := (Nat.mem_primesLE.mp hp).2
    have hp₀ : (p : ℝ) ≠ 0 := by exact_mod_cast hp'.ne_zero
    have hp₁ : (p : ℝ) - 1 ≠ 0 := by
      have : (2 : ℝ) ≤ p := by exact_mod_cast hp'.two_le
      linarith
    field_simp
    ring
  have h := (hfac.trans hlog).trans_eq hsplit
  have h₂ := mul_le_mul_of_nonneg_left (sum_primesLE_log_div_mul_sub_one_le n) hn'.le
  have h₃ : (n : ℝ) * (log n - 3) ≤ n * ∑ p ∈ Nat.primesLE n, log p / p := by nlinarith
  exact le_of_mul_le_mul_left h₃ hn'

/-! ### Mertens' first theorem -/

/-- Mertens' first theorem: `|∑_{p ≤ n} log p / p − log n| ≤ 3`. -/
theorem abs_sum_primesLE_log_div_sub_log_le (n : ℕ) :
    |∑ p ∈ Nat.primesLE n, log p / p - log n| ≤ 3 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have h₁ := sum_primesLE_log_div_le hn
  have h₂ := log_sub_three_le_sum_primesLE_log_div hn
  have h₄ : log (4 : ℝ) ≤ 2 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num, log_mul two_ne_zero two_ne_zero]
    linarith [log_le_sub_one_of_pos (two_pos : (0 : ℝ) < 2)]
  rw [abs_le]
  constructor <;> linarith

end Erdos420
