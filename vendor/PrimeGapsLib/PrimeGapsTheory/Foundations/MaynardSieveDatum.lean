/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsTheory.Arithmetic.GammaLogSum

import PrimeGapsTheory.Tactic.PaperTag

/-!
# The Maynard sieve datum

Constructs the sieve datum associated with the Maynard gamma function and a squarefree even
modulus `Q`.

## Main definitions

* `maynardGamma`: The multiplicative Maynard gamma function.
* `maynardSieveDatum`: The sieve datum determined by the Maynard gamma function.

## Main results

* `maynardSieveDatum_γ_prime`: Evaluates the gamma function of the datum at primes.
-/

@[expose] public section

open scoped BigOperators

namespace PrimeGaps

/-- The prime values of Maynard's `γ_g`: `0` if `p ∣ V`, else `p/(p-1)`. -/
noncomputable def maynardGammaPrime (V : ℕ) (p : ℕ) : ℝ :=
  if p ∣ V then 0 else (p : ℝ) / ((p : ℝ) - 1)

/-- Maynard's `γ_g`, the totally-multiplicative extension of `maynardGammaPrime V` via prime
factorization: `γ_g(n) = ∏_{p^k ‖ n} (γ_g(p))^k`.
-/
noncomputable def maynardGamma (V : ℕ) (n : ℕ) : ℝ :=
  n.factorization.prod fun p k ↦ maynardGammaPrime V p ^ k

/-- `maynardGammaPrime V p ≥ 0` for all `V, p`. -/
theorem maynardGammaPrime_nonneg (V p : ℕ) : 0 ≤ maynardGammaPrime V p := by
  unfold maynardGammaPrime
  split_ifs with h
  · rfl
  · rcases lt_or_ge p 2 with hp | hp
    · interval_cases p <;> simp
    · have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
      have h1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
      positivity

/-- Maynard's `γ_g` is always nonneg. -/
theorem maynardGamma_nonneg (V n : ℕ) : 0 ≤ maynardGamma V n := by
  unfold maynardGamma
  exact Finset.prod_nonneg fun p _ ↦ pow_nonneg (maynardGammaPrime_nonneg V p) _

/-- `maynardGamma V 1 = 1`. -/
theorem maynardGamma_one (V : ℕ) : maynardGamma V 1 = 1 := by
  simp [maynardGamma]

/-- Total multiplicativity of `maynardGamma V` on positive coprime arguments. -/
theorem maynardGamma_mul_of_ne_zero (V m n : ℕ) (hm : m ≠ 0) (hn : n ≠ 0) :
    maynardGamma V (m * n) = maynardGamma V m * maynardGamma V n := by
  unfold maynardGamma
  rw [Nat.factorization_mul hm hn,
    Finsupp.prod_add_index' (by intro p; rw [pow_zero]) (by intro p a b; rw [pow_add])]

/-- `maynardGamma V` is coprime-multiplicative (the axiom needed by `SieveDatum`). -/
theorem maynardGamma_mul (V m n : ℕ) (hmn : Nat.Coprime m n) :
    maynardGamma V (m * n) = maynardGamma V m * maynardGamma V n := by
  by_cases hm : m = 0
  · subst hm
    obtain rfl : n = 1 := (Nat.coprime_zero_left n).mp hmn
    simp [maynardGamma_one]
  by_cases hn : n = 0
  · subst hn
    obtain rfl : m = 1 := (Nat.coprime_zero_right m).mp hmn
    simp [maynardGamma_one]
  exact maynardGamma_mul_of_ne_zero V m n hm hn

/-- `maynardGamma V` at a prime `p` equals `maynardGammaPrime V p`. -/
theorem maynardGamma_prime (V : ℕ) (p : ℕ) (hp : p.Prime) :
    maynardGamma V p = maynardGammaPrime V p := by
  unfold maynardGamma
  rw [Nat.Prime.factorization hp, Finsupp.prod_single_index (by rw [pow_zero]), pow_one]

/-- The Maynard density stays below the prime. If `2 ∣ V` then `maynardGamma V p < p` for every
prime `p`: primes dividing `V` are killed outright, and the divisibility hypothesis rules out
`p = 2` among the survivors, leaving `p ≥ 3` where `p / (p - 1) < p`. -/
lemma maynardGamma_prime_lt {V : ℕ} (hV : 2 ∣ V) {p : ℕ} (hp : p.Prime) :
    maynardGamma V p < (p : ℝ) := by
  rw [maynardGamma_prime V p hp]
  unfold maynardGammaPrime
  by_cases hpV : p ∣ V
  · rw [if_pos hpV]
    have : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
    linarith
  · rw [if_neg hpV]
    have hp3 : (3 : ℕ) ≤ p := by
      rcases hp.two_le.eq_or_lt with h | h
      · exact absurd (h ▸ hV) hpV
      · omega
    have hpR : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3
    have h1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    rw [div_lt_iff₀ h1]
    nlinarith

/-- The Maynard density is a unit up to `O(1/p)` on the surviving primes: for a prime `p` not
dividing `V`, `|maynardGamma V p - 1| ≤ 2 / p`. -/
lemma abs_maynardGamma_prime_sub_one_le {V p : ℕ} (hp : p.Prime) (hpV : ¬ p ∣ V) :
    |maynardGamma V p - 1| ≤ 2 / (p : ℝ) := by
  rw [maynardGamma_prime V p hp]
  unfold maynardGammaPrime
  rw [if_neg hpV]
  have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have h1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hppos : (0 : ℝ) < (p : ℝ) := by linarith
  have hstep : (p : ℝ) / ((p : ℝ) - 1) - 1 = 1 / ((p : ℝ) - 1) := by
    field_simp; ring
  rw [hstep, abs_of_pos (by positivity), div_le_div_iff₀ h1 hppos]
  nlinarith

/-- **Uniform Mertens bounds for the Maynard density.** There are absolute constants `A₂ > 0`
and `M ≥ 0` such that for every `V ≠ 0` and all `2 ≤ w ≤ z`,
`-(M + ∑_{p ∣ V} log p / p) ≤ Δ (maynardGamma V) w z ≤ A₂`. -/
theorem maynardGamma_mertens : ∃ A₂ M : ℝ, 0 < A₂ ∧ 0 ≤ M ∧ ∀ V : ℕ, V ≠ 0 →
    ∀ w z : ℝ, 2 ≤ w → w ≤ z →
      -(M + ∑ p ∈ V.primeFactors, Real.log p / p) ≤ Δ (maynardGamma V) w z ∧
        Δ (maynardGamma V) w z ≤ A₂ := by
  obtain ⟨M, B, hM0, hB0, hkd⟩ := killed_density_mertens
  refine ⟨M + 2 * B + 1, M, by positivity, hM0, fun V hV w z hw hwz ↦ ?_⟩
  have hkill : ∀ p, Nat.Prime p → p ∣ V → maynardGamma V p = 0 := fun p hp hpV ↦ by
    rw [maynardGamma_prime V p hp, maynardGammaPrime, if_pos hpV]
  have hunit : ∀ p, Nat.Prime p → ¬ p ∣ V →
      1 ≤ maynardGamma V p ∧ maynardGamma V p ≤ 1 + 2 / p := fun p hp hpV ↦ by
    have habs := abs_le.mp (abs_maynardGamma_prime_sub_one_le hp hpV)
    refine ⟨?_, by linarith [habs.2]⟩
    rw [maynardGamma_prime V p hp, maynardGammaPrime, if_neg hpV]
    have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
    rw [le_div_iff₀ (by linarith)]
    linarith
  obtain ⟨hlo, hhi⟩ := hkd V hV (maynardGamma V) 2 (by norm_num) hkill hunit w z hw hwz
  exact ⟨hlo, by linarith⟩

/-- The absolute upper Mertens constant `A₂` of `maynardGamma_mertens`. -/
noncomputable def maynardA₂ : ℝ := Classical.choose maynardGamma_mertens

/-- The absolute Mertens constant `M` of `maynardGamma_mertens`. -/
noncomputable def maynardM : ℝ := Classical.choose (Classical.choose_spec maynardGamma_mertens)

/-- `A₂ > 0`. -/
theorem maynardA₂_pos : 0 < maynardA₂ :=
  (Classical.choose_spec (Classical.choose_spec maynardGamma_mertens)).1

/-- `M ≥ 0`. -/
theorem maynardM_nonneg : 0 ≤ maynardM :=
  (Classical.choose_spec (Classical.choose_spec maynardGamma_mertens)).2.1

/-- The Mertens bounds of `maynardGamma_mertens` with the chosen constants. -/
theorem maynardGamma_mertens_bound (V : ℕ) (hV : V ≠ 0) (w z : ℝ) (hw : 2 ≤ w) (hwz : w ≤ z) :
    -(maynardM + ∑ p ∈ V.primeFactors, Real.log p / p) ≤ Δ (maynardGamma V) w z ∧
      Δ (maynardGamma V) w z ≤ maynardA₂ :=
  (Classical.choose_spec (Classical.choose_spec maynardGamma_mertens)).2.2 V hV w z hw hwz

/-- For a squarefree modulus `Q` with `2 ∣ Q`, we bundle `γ := maynardGamma Q` (`γ_g` on primes,
totally multiplicative), `V := Q`, `A₁ := 1/2`, `A₃ := 2` and `L := M + ∑_{p ∣ Q} log p / p`
into a `SieveDatum`. The hypothesis `2 ∣ Q` is what forces every prime `p ∤ V` to satisfy
`p ≥ 3`, which the `γ_lt` and `γ_density` axioms need at `p = 2`.
-/
@[pg_tag "bg246" "def_maynard_sieve_datum"]
noncomputable def maynardSieveDatum (Q : ℕ) (h2 : 2 ∣ Q) (hQ : Squarefree Q) :
    SieveDatum where
  γ := maynardGamma Q
  A₁ := 1 / 2
  V := Q
  A₃ := 2
  γ_nonneg n := maynardGamma_nonneg Q n
  γ_one := maynardGamma_one Q
  γ_mul m n hmn := maynardGamma_mul Q m n hmn
  γ_lt p hp := maynardGamma_prime_lt h2 hp
  A₁_pos := by norm_num
  A₁_lt_one := by norm_num
  γ_density p hp := by
    rw [maynardGamma_prime Q p hp]
    unfold maynardGammaPrime
    have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
    by_cases hpW : p ∣ Q
    · rw [if_pos hpW, zero_div]
      norm_num
    · rw [if_neg hpW]
      have hp3 : (3 : ℕ) ≤ p := by
        rcases hp.two_le.eq_or_lt with h | h
        · exact absurd (h ▸ h2) hpW
        · omega
      have hpR : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3
      have h1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
      rw [div_div, div_le_iff₀ (by positivity)]
      nlinarith
  V_pos := hQ.ne_zero.bot_lt
  V_squarefree := hQ
  A₃_nonneg := by norm_num
  γ_zero_of_dvd p hp hpV := by
    rw [maynardGamma_prime Q p hp, maynardGammaPrime]
    exact if_pos hpV
  γ_approx p hp hpV := abs_maynardGamma_prime_sub_one_le hp hpV
  A₂ := maynardA₂
  L := maynardM + ∑ p ∈ Q.primeFactors, Real.log p / p
  A₂_pos := maynardA₂_pos
  L_nonneg := add_nonneg maynardM_nonneg (Finset.sum_nonneg fun p _ ↦ by positivity)
  mertens_bound w z hw hwz := maynardGamma_mertens_bound Q hQ.ne_zero w z hw hwz

/-- The `γ` field of `maynardSieveDatum` is `maynardGamma Q`. -/
@[simp]
theorem maynardSieveDatum_γ (Q : ℕ) (h2 : 2 ∣ Q) (hQ : Squarefree Q) :
    (maynardSieveDatum Q h2 hQ).γ = maynardGamma Q := rfl

/-- The `V` field of `maynardSieveDatum` is `Q`. -/
@[simp]
theorem maynardSieveDatum_V (Q : ℕ) (h2 : 2 ∣ Q) (hQ : Squarefree Q) :
    (maynardSieveDatum Q h2 hQ).V = Q := rfl

/-- The `A₁` field of `maynardSieveDatum` is `1/2`. -/
@[simp]
theorem maynardSieveDatum_A₁ (Q : ℕ) (h2 : 2 ∣ Q) (hQ : Squarefree Q) :
    (maynardSieveDatum Q h2 hQ).A₁ = 1 / 2 := rfl

/-- The `A₃` field of `maynardSieveDatum` is `2`. -/
@[simp]
theorem maynardSieveDatum_A₃ (Q : ℕ) (h2 : 2 ∣ Q) (hQ : Squarefree Q) :
    (maynardSieveDatum Q h2 hQ).A₃ = 2 := rfl

/-- Value of `maynardSieveDatum`'s `γ` at a prime `p`: `0` if
`p ∣ Q`, else `p / (p - 1)`. -/
theorem maynardSieveDatum_γ_prime (Q : ℕ) (h2 : 2 ∣ Q) (hQ : Squarefree Q)
    (p : ℕ) (hp : p.Prime) :
    (maynardSieveDatum Q h2 hQ).γ p =
      if p ∣ Q then 0 else (p : ℝ) / ((p : ℝ) - 1) := by
  rw [maynardSieveDatum_γ, maynardGamma_prime Q p hp, maynardGammaPrime]

end PrimeGaps

end
