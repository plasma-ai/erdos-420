/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsTheory.Arithmetic.Mertens.CoprimeHarmonic

/-!
# Divisor power sums

The divisor sum `∑_{d ∣ m} d ^ s` of a squarefree `m` as the Euler product `∏_{p ∣ m} (1 + p ^ s)`,
and its size at `s = σ - 1` with `σ = 1 / log y`, when every prime factor of `m` is at most `y`.
These sums replace the divisor count `τ(m)` in the error terms of the coprime harmonic sum and of
the `H` asymptotic.

## Main results

* `sum_divisors_rpow_eq_prod`: The Euler product of the divisor power sum.
* `sum_divisors_rpow_le_cube`: `∑_{d ∣ m} d ^ (1 / log y - 1) ≤ (m / φ(m)) ^ 3`.
-/

@[expose] public section

open scoped Finset

namespace PrimeGaps

/-- For squarefree `m`, `∑_{d ∣ m} d ^ s = ∏_{p ∣ m} (1 + p ^ s)`. -/
theorem sum_divisors_rpow_eq_prod (m : ℕ) (hsf : Squarefree m) (s : ℝ) :
    ∑ d ∈ m.divisors, (d : ℝ) ^ s = ∏ p ∈ m.primeFactors, (1 + (p : ℝ) ^ s) := by
  rw [Nat.divisors_sum_powerset m hsf, ← Finset.sum_powerset_prod]
  refine Finset.sum_congr rfl fun t _ ↦ ?_
  push_cast
  exact (Real.finsetProd_rpow t _ (fun p _ ↦ Nat.cast_nonneg p) s).symm

/-- The divisor power sum is multiplicative on coprime squarefree arguments. -/
theorem sum_divisors_rpow_mul {m n : ℕ} (hmn : m.Coprime n) (hm : Squarefree m)
    (hn : Squarefree n) (s : ℝ) :
    ∑ d ∈ (m * n).divisors, (d : ℝ) ^ s =
      (∑ d ∈ m.divisors, (d : ℝ) ^ s) * ∑ d ∈ n.divisors, (d : ℝ) ^ s := by
  rw [sum_divisors_rpow_eq_prod _ (Nat.squarefree_mul_iff.mpr ⟨hmn, hm, hn⟩),
    sum_divisors_rpow_eq_prod m hm, sum_divisors_rpow_eq_prod n hn,
    Nat.Coprime.primeFactors_mul hmn,
    Finset.prod_union (Nat.Coprime.disjoint_primeFactors hmn)]

/-- The divisor power sum of `m ≠ 0` is at least its `d = 1` term. -/
theorem one_le_sum_divisors_rpow {m : ℕ} (hm : m ≠ 0) (s : ℝ) :
    1 ≤ ∑ d ∈ m.divisors, (d : ℝ) ^ s := by
  have h1 := Finset.single_le_sum (f := fun d : ℕ ↦ (d : ℝ) ^ s)
    (fun d _ ↦ Real.rpow_nonneg (Nat.cast_nonneg d) s) (Nat.one_mem_divisors.mpr hm)
  simpa using h1

/-- For `s ≤ 0` the divisor power sum is at most the divisor count. -/
theorem sum_divisors_rpow_le_card (m : ℕ) {s : ℝ} (hs : s ≤ 0) :
    ∑ d ∈ m.divisors, (d : ℝ) ^ s ≤ (#m.divisors : ℝ) := by
  rw [← nsmul_one, ← Finset.sum_const]
  refine Finset.sum_le_sum fun d hd ↦ ?_
  exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast Nat.pos_of_mem_divisors hd) hs

/-- `m / φ(m) = ∏_{p ∣ m} (1 - 1/p)⁻¹`. -/
theorem self_div_totient_eq_prod (m : ℕ) (hm : 1 ≤ m) :
    (m : ℝ) / (m.totient : ℝ) = ∏ p ∈ m.primeFactors, (1 - 1 / (p : ℝ))⁻¹ := by
  have hφ : (m.totient : ℝ) = m * ∏ p ∈ m.primeFactors, (1 - 1 / (p : ℝ)) := by
    have h := congrArg (fun q : ℚ ↦ (q : ℝ)) (Nat.totient_eq_mul_prod_factors m)
    push_cast at h
    simpa only [one_div] using h
  rw [hφ, Finset.prod_inv_distrib]
  have hne : ∏ p ∈ m.primeFactors, (1 - 1 / (p : ℝ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun p hp ↦ by
      have hp1 : (1 : ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
      have : 1 / (p : ℝ) < 1 := by rw [div_lt_one (by linarith)]; exact hp1
      linarith
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  field_simp

/-- **Size of the divisor power sum.** If every prime factor of the squarefree `m ≥ 1` is at most
`y > 1`, then at `σ = 1 / log y`, `∑_{d ∣ m} d ^ (σ - 1) ≤ (m / φ(m)) ^ 3`: each Euler factor
`1 + p ^ σ / p ≤ 1 + 3 / p` is at most `(1 - 1/p)⁻³`. -/
theorem sum_divisors_rpow_le_cube (m : ℕ) (hm : 1 ≤ m) (hsf : Squarefree m) {y : ℝ}
    (hy : 1 < y) (hpy : ∀ p ∈ m.primeFactors, (p : ℝ) ≤ y) :
    ∑ d ∈ m.divisors, (d : ℝ) ^ (1 / Real.log y - 1) ≤ ((m : ℝ) / (m.totient : ℝ)) ^ 3 := by
  rw [sum_divisors_rpow_eq_prod m hsf, self_div_totient_eq_prod m hm, ← Finset.prod_pow]
  refine Finset.prod_le_prod₀ (fun p _ ↦ by positivity) fun p hp ↦ ?_
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
  have hp0 : (0 : ℝ) < p := by linarith
  have hlogy : 0 < Real.log y := Real.log_pos hy
  -- `p ^ (1 / log y) ≤ e ≤ 3`.
  have hpow : (p : ℝ) ^ (1 / Real.log y) ≤ 3 := by
    rw [Real.rpow_def_of_pos hp0]
    have : Real.log p * (1 / Real.log y) ≤ 1 := by
      rw [mul_one_div, div_le_one hlogy]
      exact Real.log_le_log hp0 (hpy p hp)
    calc Real.exp (Real.log p * (1 / Real.log y)) ≤ Real.exp 1 := Real.exp_le_exp.mpr this
      _ ≤ 3 := Real.exp_one_lt_d9.le.trans (by norm_num)
  have hsplit : (p : ℝ) ^ (1 / Real.log y - 1) = (p : ℝ) ^ (1 / Real.log y) * (1 / p) := by
    rw [Real.rpow_sub hp0, Real.rpow_one]; ring
  -- `1 + 3x ≤ (1 - x)⁻³` for `x = 1/p ∈ (0, 1/2]`.
  set x : ℝ := 1 / (p : ℝ) with hx
  have hx0 : 0 < x := by positivity
  have hx1 : x ≤ 1 / 2 := by rw [hx]; gcongr
  have h1x : 0 < 1 - x := by linarith
  calc 1 + (p : ℝ) ^ (1 / Real.log y - 1) ≤ 1 + 3 * x := by
        rw [hsplit]; gcongr
    _ ≤ ((1 - x)⁻¹) ^ 3 := by
        rw [inv_pow, le_inv_comm₀ (by positivity) (by positivity), inv_eq_one_div,
          le_div_iff₀ (by positivity)]
        nlinarith [sq_nonneg x, mul_pos hx0 hx0, pow_pos hx0 3, pow_pos hx0 4]

end PrimeGaps
