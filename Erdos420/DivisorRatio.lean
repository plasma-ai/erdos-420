module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Nat.Choose.Factorization
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.NumberTheory.Divisors

/-!
# The divisor ratio of shifted factorials

This is the form of Theorem 2 of Erdős, Graham, Ivić, and Pomerance
(*On the number of divisors of n!*, 1996) used here. Write
`τ((n + h)!) / τ(n!) = ∏_p (v_p((n + h)!) + 1) / (v_p(n!) + 1)`. A prime `p`
with `p² > n + h` has `v_p(m!) = ⌊m / p⌋` for `m ≤ n + h`, so its factor
telescopes to `∏ (1 + p / x)` over the multiples `x` of `p` in `(n, n + h]`.
When `h² ≤ n`, a prime with `p² ≤ n + h` has `p ≤ 2 √n ≤ 2 v_p(n!) + 2`, so its
factor has logarithm at most `2 (v_p((n + h)!) − v_p(n!)) / √n`. Weighting by
`log p ≥ log 2` and comparing with `log ((n + h)! / n!) ≤ h log (n + h)`, these
primes together contribute at most `4 h log (n + h) / √n`.
-/

@[expose] public section

namespace Erdos420

open Finset

/-! ### One prime at a time -/

/-- Legendre's formula for `m < p²`: `v_p(m!) = ⌊m / p⌋`. -/
private lemma factorization_factorial_of_lt_sq {p m : ℕ} (hp : p.Prime) (hm : m < p ^ 2) :
    m.factorial.factorization p = m / p := by
  rw [Nat.factorization_factorial hp (Nat.log_lt_of_lt_pow' two_ne_zero hm)]
  simp

/-- `v_p(m!) ≥ ⌊m / p⌋`. -/
private lemma div_le_factorization_factorial {p : ℕ} (hp : p.Prime) (m : ℕ) :
    m / p ≤ m.factorial.factorization p := by
  rw [Nat.factorization_factorial hp (by omega : Nat.log p m < Nat.log p m + 2)]
  have h₁ : 1 ∈ Ico 1 (Nat.log p m + 2) := by simp
  simpa using single_le_sum (f := fun i ↦ m / p ^ i) (fun _ _ ↦ Nat.zero_le _) h₁

/-- `∑_{q < k ≤ Q} log (1 + 1 / k) = log ((Q + 1) / (q + 1))`. -/
private lemma sum_Ioc_log_one_add_inv {q Q : ℕ} (hqQ : q ≤ Q) :
    ∑ k ∈ Ioc q Q, Real.log (1 + 1 / k) = Real.log ((Q + 1 : ℝ) / (q + 1)) := by
  induction Q, hqQ using Nat.le_induction with
  | base => simp
  | succ Q hqQ ih =>
    rw [sum_Ioc_succ_top hqQ, ih, ← Real.log_mul (by positivity) (by positivity)]
    congr 1
    push_cast
    field_simp

/-- For a prime `p` with `p² > n + h`, the factor of `p` in `τ((n + h)!) / τ(n!)` is
`∏ (1 + p / x)` over the multiples `x` of `p` in `(n, n + h]`. -/
private lemma log_factor_eq_sum {n h p : ℕ} (hp : p.Prime) (hpN : n + h < p ^ 2) :
    Real.log ((((n + h).factorial.factorization p : ℕ) + 1 : ℝ) /
        ((n.factorial.factorization p : ℕ) + 1)) =
      ∑ x ∈ Ioc n (n + h) with p ∣ x, Real.log (1 + p / x) := by
  rw [factorization_factorial_of_lt_sq hp hpN,
    factorization_factorial_of_lt_sq hp ((Nat.le_add_right n h).trans_lt hpN),
    ← sum_Ioc_log_one_add_inv (Nat.div_le_div_right (Nat.le_add_right n h))]
  -- the multiples of `p` in `(n, n + h]` are `p k` with `n / p < k ≤ (n + h) / p`
  have himage : {x ∈ Ioc n (n + h) | p ∣ x} = (Ioc (n / p) ((n + h) / p)).image (p * ·) := by
    ext x
    simp only [mem_filter, mem_Ioc, mem_image]
    constructor
    · rintro ⟨⟨h₁, h₂⟩, k, rfl⟩
      exact ⟨k, ⟨(Nat.div_lt_iff_lt_mul hp.pos).2 (by linarith),
        (Nat.le_div_iff_mul_le hp.pos).2 (by linarith)⟩, rfl⟩
    · rintro ⟨k, ⟨h₁, h₂⟩, rfl⟩
      have h₃ := (Nat.div_lt_iff_lt_mul hp.pos).1 h₁
      have h₄ := (Nat.le_div_iff_mul_le hp.pos).1 h₂
      exact ⟨⟨by linarith, by linarith⟩, dvd_mul_right p k⟩
  rw [himage, sum_image fun _ _ _ _ h ↦ Nat.eq_of_mul_eq_mul_left hp.pos h]
  refine sum_congr rfl fun k _ ↦ ?_
  have hp₀ : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  push_cast
  rw [div_mul_cancel_left₀ hp₀, one_div]

/-- For a prime `p ≤ 2 √n` with `v_p(n!) = a ≤ A`, the factor `(A + 1) / (a + 1)` has
logarithm at most `2 (A − a) / √n`. -/
private lemma log_factor_le {n A a p : ℕ} (hn : 1 ≤ n) (hp : p.Prime)
    (hpn : (p : ℝ) ≤ 2 * Real.sqrt n) (haA : a ≤ A) (ha : n / p ≤ a) :
    Real.log (((A : ℝ) + 1) / (a + 1)) ≤ ((A : ℝ) - a) * (2 / Real.sqrt n) := by
  have hn₀ : (0 : ℝ) < n := by exact_mod_cast hn
  have hsqrt : 0 < Real.sqrt n := Real.sqrt_pos.2 hn₀
  -- `n < (⌊n / p⌋ + 1) p ≤ (a + 1) p ≤ 2 (a + 1) √n`
  have h₁ : n < (a + 1) * p := by
    have := Nat.lt_div_mul_add (a := n) hp.pos
    nlinarith
  have h₂ : Real.sqrt n ≤ 2 * (a + 1) := by
    have h₃ : (n : ℝ) ≤ (a + 1) * p := by exact_mod_cast h₁.le
    have h₄ := Real.mul_self_sqrt hn₀.le
    nlinarith
  have hA : (a : ℝ) ≤ A := by exact_mod_cast haA
  calc Real.log (((A : ℝ) + 1) / (a + 1)) ≤ ((A : ℝ) + 1) / (a + 1) - 1 :=
        Real.log_le_sub_one_of_pos (by positivity)
    _ = ((A : ℝ) - a) * (1 / (a + 1)) := by field_simp; ring
    _ ≤ ((A : ℝ) - a) * (2 / Real.sqrt n) := by
        refine mul_le_mul_of_nonneg_left ?_ (by linarith)
        rw [div_le_div_iff₀ (by positivity) hsqrt]
        linarith

/-- `log (n + h)! ≤ log n! + h log (n + h)`. -/
private lemma log_factorial_add_le (n h : ℕ) :
    Real.log ((n + h).factorial : ℝ) ≤
      Real.log (n.factorial : ℝ) + h * Real.log ((n + h : ℕ) : ℝ) := by
  rcases Nat.eq_zero_or_pos (n + h) with hN | hN
  · obtain ⟨rfl, rfl⟩ : n = 0 ∧ h = 0 := by omega
    simp
  have h₁ : (n + h).factorial ≤ n.factorial * (n + h) ^ h := by
    rw [← Nat.factorial_mul_descFactorial (Nat.le_add_left h n), Nat.add_sub_cancel]
    exact Nat.mul_le_mul_left _ (Nat.descFactorial_le_pow _ _)
  rw [← Real.log_pow, ← Real.log_mul (by positivity) (by positivity)]
  exact Real.log_le_log (by positivity) (by exact_mod_cast h₁)

/-! ### The divisor ratio -/

/-- `log (τ((n + h)!) / τ(n!))` is `∑_{n < x ≤ n + h} ∑_{p ∣ x, p² > n + h} log (1 + p / x)`
up to a nonnegative error `O(h log (n + h) / √n)`. -/
theorem exists_log_divisor_ratio_bounds : ∃ C : ℝ, ∀ n h : ℕ, 1 ≤ n → h ^ 2 ≤ n →
    (∑ x ∈ Ioc n (n + h), ∑ p ∈ x.primeFactors with n + h < p ^ 2,
        Real.log (1 + p / x)) ≤
      Real.log (((n + h).factorial.divisors.card : ℝ) / n.factorial.divisors.card) ∧
    Real.log (((n + h).factorial.divisors.card : ℝ) / n.factorial.divisors.card) ≤
      (∑ x ∈ Ioc n (n + h), ∑ p ∈ x.primeFactors with n + h < p ^ 2,
        Real.log (1 + p / x)) + C * h * Real.log (n + h) / Real.sqrt n := by
  refine ⟨4, fun n h hn hh ↦ ?_⟩
  set P := (n + h).factorial.primeFactors with hP
  set f : ℕ → ℝ := fun p ↦ Real.log ((((n + h).factorial.factorization p : ℕ) + 1 : ℝ) /
    ((n.factorial.factorization p : ℕ) + 1))
  have hsub : n.factorial.primeFactors ⊆ P :=
    Nat.primeFactors_mono (Nat.factorial_dvd_factorial (Nat.le_add_right n h))
      (Nat.factorial_ne_zero _)
  have hle : ∀ p, n.factorial.factorization p ≤ (n + h).factorial.factorization p :=
    (Nat.factorization_le_iff_dvd (Nat.factorial_ne_zero n) (Nat.factorial_ne_zero _)).2
      (Nat.factorial_dvd_factorial (Nat.le_add_right n h))
  -- `log (τ((n + h)!) / τ(n!)) = ∑_p log ((v_p((n + h)!) + 1) / (v_p(n!) + 1))`
  have hlog : Real.log (((n + h).factorial.divisors.card : ℝ) / n.factorial.divisors.card) =
      ∑ p ∈ P, f p := by
    have hτn : ∏ p ∈ n.factorial.primeFactors, ((n.factorial.factorization p : ℕ) + 1 : ℝ) =
        ∏ p ∈ P, ((n.factorial.factorization p : ℕ) + 1 : ℝ) := by
      refine prod_subset hsub fun p _ hp ↦ ?_
      rw [← Nat.support_factorization, Finsupp.notMem_support_iff] at hp
      simp [hp]
    rw [Nat.card_divisors (Nat.factorial_ne_zero _),
      Nat.card_divisors (Nat.factorial_ne_zero _)]
    push_cast
    rw [hτn, ← prod_div_distrib, Real.log_prod fun p _ ↦ by positivity]
  have hf₀ : ∀ p, 0 ≤ f p := fun p ↦
    Real.log_nonneg ((one_le_div (by positivity)).2 (by gcongr; exact_mod_cast hle p))
  -- the primes with `p² > n + h` give exactly the double sum
  have hbig : ∑ p ∈ P with n + h < p ^ 2, f p = ∑ x ∈ Ioc n (n + h),
      ∑ p ∈ x.primeFactors with n + h < p ^ 2, Real.log (1 + p / x) := by
    symm
    rw [sum_comm' (t' := {p ∈ P | n + h < p ^ 2})
      (s' := fun p ↦ {x ∈ Ioc n (n + h) | p ∣ x})]
    · refine sum_congr rfl fun p hp ↦ ?_
      simp only [mem_filter, hP, Nat.mem_primeFactors] at hp
      exact (log_factor_eq_sum hp.1.1 hp.2).symm
    · intro x p
      simp only [mem_filter, mem_Ioc, hP, Nat.mem_primeFactors]
      constructor
      · rintro ⟨⟨hx₁, hx₂⟩, ⟨hp, hpx, hx₀⟩, hpN⟩
        exact ⟨⟨⟨hx₁, hx₂⟩, hpx⟩, ⟨hp,
          Nat.dvd_factorial hp.pos ((Nat.le_of_dvd (by omega) hpx).trans hx₂),
          Nat.factorial_ne_zero _⟩, hpN⟩
      · rintro ⟨⟨⟨hx₁, hx₂⟩, hpx⟩, ⟨hp, -, -⟩, hpN⟩
        exact ⟨⟨hx₁, hx₂⟩, ⟨hp, hpx, by omega⟩, hpN⟩
  -- the primes with `p² ≤ n + h` give at most `4 h log (n + h) / √n`
  have hsmall : ∑ p ∈ P with ¬n + h < p ^ 2, f p ≤
      4 * h * Real.log (n + h) / Real.sqrt n := by
    have hn₀ : (0 : ℝ) < n := by exact_mod_cast hn
    have hhn : h ≤ n := by nlinarith
    have hN : ((n + h : ℕ) : ℝ) = n + h := by push_cast; ring
    have hlogN : 0 ≤ Real.log (n + h) := Real.log_nonneg (by
      have : (1 : ℝ) ≤ n := by exact_mod_cast hn
      linarith [(Nat.cast_nonneg h : (0 : ℝ) ≤ h)])
    -- `∑_p (v_p((n + h)!) − v_p(n!)) log p = log (n + h)! − log n!`
    have hsum : ∑ p ∈ P, (((n + h).factorial.factorization p : ℝ) -
        n.factorial.factorization p) * Real.log p =
          Real.log ((n + h).factorial : ℝ) - Real.log (n.factorial : ℝ) := by
      rw [Real.log_nat_eq_sum_factorization, Real.log_nat_eq_sum_factorization n.factorial,
        Finsupp.sum, Nat.support_factorization,
        Finsupp.sum_of_support_subset _ (s := P) (by rwa [Nat.support_factorization]) _
          fun _ _ ↦ by simp]
      simp only [sub_mul, sum_sub_distrib, hP]
    -- so `(∑_p (v_p((n + h)!) − v_p(n!))) log 2 ≤ h log (n + h)`
    have htot : ∑ p ∈ P, (((n + h).factorial.factorization p : ℝ) -
        n.factorial.factorization p) ≤ 2 * (h * Real.log (n + h)) := by
      have hlog₂ : (1 : ℝ) / 2 ≤ Real.log 2 := by
        have := Real.one_sub_inv_le_log_of_pos (two_pos : (0 : ℝ) < 2)
        norm_num at this ⊢
        linarith
      have hd : ∀ p, (0 : ℝ) ≤ ((n + h).factorial.factorization p : ℝ) -
          n.factorial.factorization p := fun p ↦ sub_nonneg.2 (by exact_mod_cast hle p)
      have h₁ : (∑ p ∈ P, (((n + h).factorial.factorization p : ℝ) -
          n.factorial.factorization p)) * Real.log 2 ≤ h * Real.log (n + h) :=
        calc (∑ p ∈ P, (((n + h).factorial.factorization p : ℝ) -
            n.factorial.factorization p)) * Real.log 2
            ≤ ∑ p ∈ P, (((n + h).factorial.factorization p : ℝ) -
                n.factorial.factorization p) * Real.log p := by
              rw [sum_mul]
              refine sum_le_sum fun p hp ↦ mul_le_mul_of_nonneg_left ?_ (hd p)
              exact Real.log_le_log two_pos
                (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le)
          _ ≤ h * Real.log (n + h) := by
              have := log_factorial_add_le n h
              rw [hN] at this
              linarith
      have h₂ := sum_nonneg fun p (_ : p ∈ P) ↦ hd p
      nlinarith
    calc ∑ p ∈ P with ¬n + h < p ^ 2, f p
        ≤ ∑ p ∈ P with ¬n + h < p ^ 2, (((n + h).factorial.factorization p : ℝ) -
            n.factorial.factorization p) * (2 / Real.sqrt n) := by
          refine sum_le_sum fun p hp ↦ ?_
          simp only [mem_filter, hP, Nat.mem_primeFactors, not_lt] at hp
          -- `p² ≤ n + h ≤ 4 n`, so `p ≤ 2 √n`
          have hpn : (p : ℝ) ≤ 2 * Real.sqrt n := by
            have h₁ : (p : ℝ) ^ 2 ≤ 4 * n := by
              have : (p : ℝ) ^ 2 ≤ n + h := by exact_mod_cast hp.2
              have : (h : ℝ) ≤ n := by exact_mod_cast hhn
              linarith
            nlinarith [Real.sq_sqrt hn₀.le, Real.sqrt_nonneg n]
          exact log_factor_le hn hp.1.1 hpn (hle p) (div_le_factorization_factorial hp.1.1 n)
      _ ≤ ∑ p ∈ P, (((n + h).factorial.factorization p : ℝ) -
            n.factorial.factorization p) * (2 / Real.sqrt n) :=
          sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun p _ _ ↦
            mul_nonneg (sub_nonneg.2 (by exact_mod_cast hle p)) (by positivity)
      _ ≤ 2 * (h * Real.log (n + h)) * (2 / Real.sqrt n) := by
          rw [← sum_mul]
          gcongr
      _ = 4 * h * Real.log (n + h) / Real.sqrt n := by ring
  rw [hlog, ← sum_filter_add_sum_filter_not P fun p ↦ n + h < p ^ 2, hbig]
  exact ⟨le_add_of_nonneg_right (sum_nonneg fun p _ ↦ hf₀ p), by gcongr⟩

end Erdos420
