import Erdos420.Maynard.SharpLambda
import PrimeGapsTheory.Endgame.MainProp

/-!
# Pointwise bounds for Maynard's weights

The weight of `n` is `w(n) = (∑_{dᵢ ∣ n + hᵢ} λ_d)²`. If every `n + hᵢ` has all its
prime factors above `X^ρ` and is at most `X²`, it has at most `2^{2/ρ}` divisors, so
`w(n) ≤ 2^{4k/ρ} max_d λ_d²`. With `|λ_d| ≪ ((φ(Q)/Q) log R)^k` from
`Erdos420.exists_abs_l₀_le`, this bounds the normalized weights on rough `n`.
-/

namespace Erdos420

open Finset

/-- A number `0 < n ≤ X²` whose prime factors all exceed `X^ρ` has at most `2^{2/ρ}`
divisors. -/
lemma card_divisors_le_of_rough {n X : ℕ} {ρ : ℝ} (hρ : 0 < ρ) (hX : 2 ≤ X) (hn : 0 < n)
    (hnX : n ≤ X ^ 2) (hrough : ∀ p : ℕ, p.Prime → p ∣ n → (X : ℝ) ^ ρ < p) :
    (#n.divisors : ℝ) ≤ 2 ^ (2 / ρ) := by
  have hn₀ : n ≠ 0 := hn.ne'
  have hX₁ : (1 : ℝ) < X := by exact_mod_cast hX
  -- `τ(n) = ∏ (e_p + 1) ≤ 2^Ω(n)`
  have h₁ : #n.divisors ≤ 2 ^ ∑ p ∈ n.primeFactors, n.factorization p := by
    rw [Nat.card_divisors hn₀, ← prod_pow_eq_pow_sum]
    exact prod_le_prod fun p _ ↦ Nat.lt_two_pow_self
  -- `X^{ρ Ω(n)} ≤ ∏ p^{e_p} = n ≤ X²`
  have h₂ : (X : ℝ) ^ (ρ * ∑ p ∈ n.primeFactors, n.factorization p) ≤ n := by
    have hn' := Nat.prod_factorization_pow_eq_self hn₀
    rw [Finsupp.prod, Nat.support_factorization] at hn'
    calc (X : ℝ) ^ (ρ * ∑ p ∈ n.primeFactors, n.factorization p)
        = ∏ p ∈ n.primeFactors, ((X : ℝ) ^ ρ) ^ n.factorization p := by
          rw [prod_pow_eq_pow_sum, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      _ ≤ ∏ p ∈ n.primeFactors, (p : ℝ) ^ n.factorization p :=
          prod_le_prod₀ (fun p _ ↦ by positivity) fun p hp ↦ pow_le_pow_left₀ (by positivity)
            (hrough p (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp)).le _
      _ = n := by exact_mod_cast hn'
  have h₃ : ρ * ∑ p ∈ n.primeFactors, n.factorization p ≤ 2 := by
    refine (Real.rpow_le_rpow_left_iff hX₁).mp (h₂.trans ?_)
    rw [Real.rpow_two]
    exact_mod_cast hnX
  calc (#n.divisors : ℝ) ≤ (2 : ℝ) ^ (∑ p ∈ n.primeFactors, n.factorization p) := by
        exact_mod_cast h₁
    _ = (2 : ℝ) ^ ((∑ p ∈ n.primeFactors, n.factorization p : ℕ) : ℝ) :=
        (Real.rpow_natCast _ _).symm
    _ ≤ 2 ^ (2 / ρ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by
        rw [le_div_iff₀ hρ]
        linarith)

/-- If every `|λ_d| ≤ Λ` and every `n + hᵢ` has at most `T` divisors, then
`w(n) ≤ (T^k Λ)²`. -/
lemma weight_le_of_abs_le {k : ℕ} (h : Fin k → ℕ) (l : (Fin k → ℕ) → ℝ) (n : ℕ) {Λ T : ℝ}
    (hl : ∀ d, |l d| ≤ Λ) (hT : ∀ i, (#(n + h i).divisors : ℝ) ≤ T) :
    PrimeGaps.weight h l n ≤ (T ^ k * Λ) ^ 2 := by
  have hΛ : 0 ≤ Λ := (abs_nonneg _).trans (hl 0)
  have hsum : |∑ d ∈ Fintype.piFinset fun i ↦ (n + h i).divisors, l d| ≤ T ^ k * Λ := by
    calc |∑ d ∈ Fintype.piFinset fun i ↦ (n + h i).divisors, l d|
        ≤ ∑ d ∈ Fintype.piFinset fun i ↦ (n + h i).divisors, |l d| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ d ∈ Fintype.piFinset fun i ↦ (n + h i).divisors, Λ := sum_le_sum fun d _ ↦ hl d
      _ = (∏ i, (#(n + h i).divisors : ℝ)) * Λ := by
          rw [sum_const, Fintype.card_piFinset, nsmul_eq_mul]
          push_cast
          rfl
      _ ≤ (∏ _i : Fin k, T) * Λ :=
          mul_le_mul_of_nonneg_right (prod_le_prod₀ (fun i _ ↦ Nat.cast_nonneg _) fun i _ ↦ hT i) hΛ
      _ = T ^ k * Λ := by rw [prod_const, card_univ, Fintype.card_fin]
  rw [PrimeGaps.weight, ← sq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) hsum 2

end Erdos420
