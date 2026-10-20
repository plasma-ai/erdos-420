/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.NumberTheory.Chebyshev
public import PrimeGapsTheory.Sieve.PermissibleSupport.FunctionD0
import PrimeGapsTheory.Tactic.PaperTag

/-! # The sieve modulus `W`

The modulus used in the `W`-trick: the product of all primes up to `D₀ N`, together with its
basic divisibility properties and the size bound `W N ≤ (log (log N)) ^ 2`.

## Main definitions

* `PrimeGaps.sieveModulus` — the modulus `W N = ∏_{p ≤ D₀ N} p`, with scoped notation `W`.

## Main results

* `PrimeGaps.lem_W_size` — eventually in `N`, `W N ≤ (log (log N)) ^ 2`.
-/

@[expose] public section

namespace PrimeGaps

variable {N : ℕ}

open Real Chebyshev Finset

/-- `W` is shorthand for $$\prod_{p \le D_0,\ p \text{ prime}} p$$.

To enable `W` notation, do `open scoped PrimeGaps.sieveModulus`. -/
@[pg_tag "bg246" "def_W_trick"]
noncomputable abbrev sieveModulus (N : ℕ) : ℕ := primorial ⌊D₀ N⌋₊

@[inherit_doc] scoped[PrimeGaps.sieveModulus] notation "W" => sieveModulus

open sieveModulus

lemma W_def : W = primorial ∘ Nat.floor ∘ D₀ ∘ Nat.cast := rfl

lemma W_eq_primorial_D₀ : W N = primorial ⌊D₀ N⌋₊ := rfl

lemma W_eq_prod_primes_le : W N = ∏ p ∈ range (⌊D₀ N⌋₊ + 1) with p.Prime, p := rfl

lemma W_eq_prod_Icc_two_D₀ : W N = ∏ p ∈ Finset.Icc 2 ⌊D₀ N⌋₊ with p.Prime, p := by
  rw [W_eq_prod_primes_le]
  congr 1
  ext p
  simp only [mem_filter, mem_range, Order.lt_add_one_iff, mem_Icc, and_congr_left_iff, iff_and_self]
  exact fun hp _ ↦ hp.two_le

lemma W_zero : W 0 = 1 := by simp [W_eq_prod_primes_le, Nat.not_prime_zero, D₀]

lemma W_pos : 0 < W N := primorial_pos ⌊D₀ N⌋₊

lemma W_ne_zero : W N ≠ 0 := Nat.pos_iff_ne_zero.mp W_pos

lemma one_le_totient_W : (1 : ℝ) ≤ ((W N).totient : ℝ) := mod_cast Nat.totient_pos.mpr W_pos

lemma totient_W_pos : (0 : ℝ) < ((W N).totient : ℝ) := zero_lt_one.trans_le one_le_totient_W

lemma _root_.Nat.Prime.dvd_W_iff_le_D₀ {p : ℕ} (hp : p.Prime) : p ∣ W N ↔ p ≤ D₀ N := by
  rw [W_eq_primorial_D₀, hp.dvd_primorial_iff]
  exact Nat.le_floor_iff' hp.ne_zero

lemma real_log_W_eq_theta_D₀ : Real.log (W N) = θ (D₀ N) := by
  rw [theta_eq_log_primorial, W_eq_primorial_D₀]

lemma W_squarefree : Squarefree (W N) := squarefree_primorial ⌊D₀ N⌋₊

@[grind .]
private lemma _root_.Real.log_four_le_two : log 4 ≤ 2 := by
  have h4 : (4 : ℝ) = 2 * 2 := by norm_num
  rw [log_le_iff_le_exp (by positivity), h4]
  exact two_mul_le_exp (x := 2)

attribute [local grind =] log_exp log_rpow log_pow in
attribute [local grind .] exp_pos log_nonneg MulPosMono.mul_le_mul_of_nonneg_right in
@[pg_tag "bg246" "lem_W_size"]
theorem lem_W_size : ∀ᶠ N in Filter.atTop, (W N : ℝ) ≤ (log (log N)) ^ 2 := by
  -- The bound holds once `log (log N) ≥ 1`, i.e. `N ≥ exp (exp 1)`.
  filter_upwards [Filter.eventually_ge_atTop ⌈rexp (rexp 1)⌉₊] with N hN
  rw [Nat.ceil_le] at hN
  have ht1 : (1 : ℝ) ≤ log (log N) := by grind [log_le_log (by grind) (log_le_log (exp_pos _) hN)]
  have hD₀ : (0 : ℝ) ≤ D₀ N := by unfold D₀; exact Real.log_nonneg ht1
  grw [W_eq_primorial_D₀, ← rpow_natCast, primorial_le_four_pow, Nat.cast_pow, ← rpow_natCast,
      rpow_le_rpow_of_exponent_le (by grind) (Nat.floor_le hD₀), rpow_natCast,
      ← log_le_log_iff (by positivity) (pow_pos (by positivity) 2)]
  unfold D₀
  grind [mul_comm]

/-- Hypotheses on a general sieve modulus `Q` at scale `N`, with constants `CQ` and `η`: `Q` is
squarefree and divisible by every prime `p ≤ D₀ N`, `Q ≤ N ^ η`, `Q / φ(Q) ≤ CQ log log N`, every
prime factor of `Q` is at most `log N`, and `ℓ_Q = ∑_{p ∣ Q} log p / (p - 1) ≤ CQ log log N`.
The sieve asymptotics hold uniformly over all `Q` satisfying them at a given `N`. -/
structure ModulusHyp (CQ η N : ℝ) (Q : ℕ) : Prop where
  squarefree : Squarefree Q
  primorial_dvd : primorial ⌊D₀ N⌋₊ ∣ Q
  le_rpow : (Q : ℝ) ≤ N ^ η
  le_totient : (Q : ℝ) ≤ CQ * log (log N) * Q.totient
  primeFactors_le : ∀ p ∈ Q.primeFactors, (p : ℝ) ≤ log N
  sum_log_div_le : ∑ p ∈ Q.primeFactors, log p / (p - 1) ≤ CQ * log (log N)

namespace ModulusHyp

variable {CQ η N : ℝ} {Q : ℕ}

lemma pos (hQ : ModulusHyp CQ η N Q) : 0 < Q := hQ.squarefree.ne_zero.bot_lt

lemma ne_zero (hQ : ModulusHyp CQ η N Q) : Q ≠ 0 := hQ.squarefree.ne_zero

lemma one_le_totient (hQ : ModulusHyp CQ η N Q) : (1 : ℝ) ≤ (Q.totient : ℝ) :=
  mod_cast Nat.totient_pos.mpr hQ.pos

lemma totient_pos (hQ : ModulusHyp CQ η N Q) : (0 : ℝ) < (Q.totient : ℝ) :=
  zero_lt_one.trans_le hQ.one_le_totient

lemma prime_dvd_of_le_D₀ (hQ : ModulusHyp CQ η N Q) {p : ℕ} (hp : p.Prime) (hpD : p ≤ D₀ N) :
    p ∣ Q :=
  ((hp.dvd_primorial_iff (n := ⌊D₀ N⌋₊)).mpr (Nat.le_floor hpD)).trans hQ.primorial_dvd

lemma two_dvd (hQ : ModulusHyp CQ η N Q) (hD : 2 ≤ D₀ N) : 2 ∣ Q :=
  hQ.prime_dvd_of_le_D₀ Nat.prime_two (by exact_mod_cast hD)

end ModulusHyp

end PrimeGaps
