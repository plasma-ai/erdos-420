module

public import Erdos420.Elementary.Mertens.First
public import Erdos420.Sieve.Selberg.LambdaSquared
public import Mathlib.Data.Nat.Prime.Factorial
public import Mathlib.NumberTheory.Chebyshev

/-!
# A lower bound for Selberg's `G(y)`

* `G(y) ≥ ∏_{p ∣ P} (1 + g(p)) / 2` once `∑_{p ∣ P} g(p) log p ≤ (log y) / 2`. The full sum
  `∑_{l ∣ P} g(l)` is the Euler product, and by Markov's inequality the part with `l > y` is at
  most `∑_{l ∣ P} g(l) log l / log y ≤ (∑_{p ∣ P} g(p) log p / log y) ∏_{p ∣ P} (1 + g(p))`.
* `∏_{p ∣ P} (1 + g(p)) = ∏_{p ∣ P} (1 − ν(p))⁻¹ ≥ exp (∑_{p ∣ P} ν(p))`.
-/

@[expose] public section

namespace Erdos420

open Finset Real BoundingSieve
open ArithmeticFunction hiding log
open scoped Nat

/-! ### Rankin's trick -/

variable {s : BoundingSieve}

/-- `∑_{p ∣ l ∣ P} g(l) ≤ g(p) ∑_{m ∣ P} g(m)`. -/
lemma sum_filter_dvd_selbergTerms_le {p : ℕ} (hp : p.Prime) (hpP : p ∣ s.prodPrimes) :
    ∑ l ∈ s.prodPrimes.divisors with p ∣ l, s.selbergTerms l ≤
      s.selbergTerms p * ∑ m ∈ s.prodPrimes.divisors, s.selbergTerms m := by
  have hp₀ := hp.pos
  calc ∑ l ∈ s.prodPrimes.divisors with p ∣ l, s.selbergTerms l
      = ∑ l ∈ s.prodPrimes.divisors with p ∣ l, s.selbergTerms p * s.selbergTerms (l / p) := by
        refine sum_congr rfl fun l hl ↦ ?_
        simp only [mem_filter] at hl
        have hsq := squarefree_of_mem_divisors_prodPrimes hl.1
        rw [← Nat.mul_div_cancel' hl.2] at hsq
        rw [← selbergTerms_isMultiplicative.map_mul_of_coprime (Nat.coprime_of_squarefree_mul hsq),
          Nat.mul_div_cancel' hl.2]
    _ = s.selbergTerms p * ∑ m ∈ {l ∈ s.prodPrimes.divisors | p ∣ l}.image (· / p),
          s.selbergTerms m := by
        rw [← mul_sum, sum_image]
        intro l hl l' hl' h
        simp only [coe_filter, Set.mem_ofPred_eq] at hl hl'
        simp only at h
        rw [← Nat.mul_div_cancel' hl.2, ← Nat.mul_div_cancel' hl'.2, h]
    _ ≤ s.selbergTerms p * ∑ m ∈ s.prodPrimes.divisors, s.selbergTerms m := by
        refine mul_le_mul_of_nonneg_left ?_ (selbergTerms_pos hpP).le
        refine sum_le_sum_of_subset_of_nonneg (fun m hm ↦ ?_) fun m hm _ ↦
          (selbergTerms_pos (Nat.dvd_of_mem_divisors hm)).le
        obtain ⟨l, hl, rfl⟩ := mem_image.mp hm
        simp only [mem_filter, Nat.mem_divisors] at hl
        exact Nat.mem_divisors.mpr ⟨(Nat.div_dvd_of_dvd hl.2).trans hl.1.1, hl.1.2⟩

/-- `log l = ∑_{p ∣ l} log p` for squarefree `l`. -/
private lemma log_eq_sum_primeFactors {l : ℕ} (hl : Squarefree l) :
    log l = ∑ p ∈ l.primeFactors, log p := by
  conv_lhs => rw [← Nat.prod_primeFactors_of_squarefree hl]
  rw [Nat.cast_prod, log_prod]
  intro p hp
  exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero

/-- `∑_{l ∣ P} g(l) log l ≤ (∑_{p ∣ P} g(p) log p) ∑_{l ∣ P} g(l)`. -/
lemma sum_selbergTerms_mul_log_le :
    ∑ l ∈ s.prodPrimes.divisors, s.selbergTerms l * log l ≤
      (∑ p ∈ s.prodPrimes.primeFactors, s.selbergTerms p * log p) *
        ∑ l ∈ s.prodPrimes.divisors, s.selbergTerms l := by
  calc ∑ l ∈ s.prodPrimes.divisors, s.selbergTerms l * log l
      = ∑ l ∈ s.prodPrimes.divisors, ∑ p ∈ s.prodPrimes.primeFactors,
          if p ∣ l then s.selbergTerms l * log p else 0 := by
        refine sum_congr rfl fun l hl ↦ ?_
        rw [log_eq_sum_primeFactors (squarefree_of_mem_divisors_prodPrimes hl), mul_sum,
          ← sum_filter]
        have hl' := Nat.mem_divisors.mp hl
        congr 1
        ext p
        simp only [mem_filter, Nat.mem_primeFactors]
        constructor
        · rintro ⟨hp, hpl, hl₀⟩
          exact ⟨⟨hp, hpl.trans hl'.1, hl'.2⟩, hpl⟩
        · rintro ⟨⟨hp, -, -⟩, hpl⟩
          exact ⟨hp, hpl, (Nat.pos_of_mem_divisors hl).ne'⟩
    _ = ∑ p ∈ s.prodPrimes.primeFactors,
          log p * ∑ l ∈ s.prodPrimes.divisors with p ∣ l, s.selbergTerms l := by
        rw [sum_comm]
        refine sum_congr rfl fun p _ ↦ ?_
        rw [mul_sum, sum_filter]
        exact sum_congr rfl fun l _ ↦ by split_ifs <;> ring
    _ ≤ ∑ p ∈ s.prodPrimes.primeFactors,
          log p * (s.selbergTerms p * ∑ m ∈ s.prodPrimes.divisors, s.selbergTerms m) := by
        refine sum_le_sum fun p hp ↦ ?_
        have hp' := Nat.mem_primeFactors.mp hp
        exact mul_le_mul_of_nonneg_left (sum_filter_dvd_selbergTerms_le hp'.1 hp'.2.1)
          (log_nonneg (by exact_mod_cast hp'.1.one_lt.le))
    _ = (∑ p ∈ s.prodPrimes.primeFactors, s.selbergTerms p * log p) *
          ∑ l ∈ s.prodPrimes.divisors, s.selbergTerms l := by
        rw [sum_mul]
        exact sum_congr rfl fun p _ ↦ by ring

/-- `∏_{p ∣ P} (1 + g(p)) ≤ 2 G(y)` once `∑_{p ∣ P} g(p) log p ≤ (log y) / 2`. -/
theorem prod_one_add_selbergTerms_le {y : ℝ} (hy : 1 < y)
    (h : ∑ p ∈ s.prodPrimes.primeFactors, s.selbergTerms p * log p ≤ log y / 2) :
    ∏ p ∈ s.prodPrimes.primeFactors, (1 + s.selbergTerms p) ≤ 2 * selbergMass s y := by
  have hlogy : 0 < log y := log_pos hy
  rw [selbergTerms_isMultiplicative.prodPrimeFactors_one_add_of_squarefree
    s.prodPrimes_squarefree]
  set F := ∑ l ∈ s.prodPrimes.divisors, s.selbergTerms l with hF_def
  have hg : ∀ l ∈ s.prodPrimes.divisors, 0 ≤ s.selbergTerms l :=
    fun l hl ↦ (selbergTerms_pos (Nat.dvd_of_mem_divisors hl)).le
  have hF : 0 ≤ F := sum_nonneg hg
  -- Markov's inequality for `log l`
  have htail : ∑ l ∈ s.prodPrimes.divisors with ¬((l : ℕ) : ℝ) ≤ y, s.selbergTerms l ≤ F / 2 := by
    calc ∑ l ∈ s.prodPrimes.divisors with ¬((l : ℕ) : ℝ) ≤ y, s.selbergTerms l
        ≤ ∑ l ∈ s.prodPrimes.divisors with ¬((l : ℕ) : ℝ) ≤ y,
            s.selbergTerms l * log l / log y := by
          refine sum_le_sum fun l hl ↦ ?_
          simp only [mem_filter, not_le] at hl
          rw [mul_div_assoc]
          refine le_mul_of_one_le_right (hg l hl.1) ?_
          rw [one_le_div hlogy]
          exact log_le_log (by linarith) hl.2.le
      _ ≤ ∑ l ∈ s.prodPrimes.divisors, s.selbergTerms l * log l / log y := by
          refine sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun l hl _ ↦ ?_
          exact div_nonneg (mul_nonneg (hg l hl)
            (log_nonneg (Nat.one_le_cast.mpr (Nat.pos_of_mem_divisors hl)))) hlogy.le
      _ ≤ log y / 2 * F / log y := by
          rw [← sum_div]
          gcongr
          exact sum_selbergTerms_mul_log_le.trans (mul_le_mul_of_nonneg_right h hF)
      _ = F / 2 := by field_simp
  have hsplit := sum_filter_add_sum_filter_not s.prodPrimes.divisors
    (fun l : ℕ ↦ ((l : ℕ) : ℝ) ≤ y) s.selbergTerms
  rw [← selbergMass, ← hF_def] at hsplit
  linarith

/-- `1 + g(p) = (1 − ν(p))⁻¹`. -/
lemma one_add_selbergTerms_of_prime {p : ℕ} (hp : p.Prime) (hpP : p ∣ s.prodPrimes) :
    1 + s.selbergTerms p = (1 - s.nu p)⁻¹ := by
  have h := s.nu_lt_one_of_prime p hp hpP
  have h' : 1 - s.nu p ≠ 0 := by linarith
  rw [selbergTerms_apply, hp.primeFactors, prod_singleton]
  field_simp
  ring

/-- `exp (∑_{p ∣ P} ν(p)) ≤ ∏_{p ∣ P} (1 + g(p))`. -/
lemma exp_sum_nu_le_prod :
    exp (∑ p ∈ s.prodPrimes.primeFactors, s.nu p) ≤
      ∏ p ∈ s.prodPrimes.primeFactors, (1 + s.selbergTerms p) := by
  rw [exp_sum]
  refine prod_le_prod₀ (fun p _ ↦ (exp_pos _).le) fun p hp ↦ ?_
  have hp' := Nat.mem_primeFactors.mp hp
  have h := s.nu_lt_one_of_prime p hp'.1 hp'.2.1
  rw [one_add_selbergTerms_of_prime hp'.1 hp'.2.1, le_inv_comm₀ (exp_pos _) (by linarith),
    ← exp_neg]
  linarith [add_one_le_exp (-s.nu p)]

end Erdos420
