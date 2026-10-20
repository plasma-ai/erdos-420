import Erdos420.Asymptotics
import Erdos420.Elementary.Mertens.First

/-!
# Two sums over primes

* `∑_{p ≤ M} (log p)² / p ≤ log M (log M + log 4)`, from Mertens' first theorem.
* `∑_{p ∈ S} 1 / p² ≤ 2 / (K + 1)` when every element of `S` exceeds `K`, by
  `Erdos420.sum_one_div_sq_le_of_lt`.
* Their combination `∑_p B_p² / p ≤ 4 L² X² / ℓ² + 16 a² F₀² / (K + 1)` for
  `B_p = L log p / ℓ + a F₀ / (p − 1)` over primes `K < p ≤ M` with `log 4 ≤ X`, `log M ≤ X`.
-/

namespace Erdos420

open Finset Real

/-- `∑_{p ≤ M} (log p)² / p ≤ log M (log M + log 4)`. -/
private lemma sum_primesLE_log_sq_div_le {M : ℕ} (hM : 1 ≤ M) :
    ∑ p ∈ Nat.primesLE M, log p ^ 2 / p ≤ log M * (log M + log 4) := by
  have hlogM : 0 ≤ log M := log_nonneg (by exact_mod_cast hM)
  calc ∑ p ∈ Nat.primesLE M, log p ^ 2 / p
      ≤ ∑ p ∈ Nat.primesLE M, log M * (log p / p) := by
        refine sum_le_sum fun p hp ↦ ?_
        obtain ⟨hpM, hp'⟩ := Nat.mem_primesLE.mp hp
        have hp0 : (0 : ℝ) < p := by exact_mod_cast hp'.pos
        have hlogp : 0 ≤ log p := log_nonneg (by exact_mod_cast hp'.one_le)
        have hle : log p ≤ log M := log_le_log hp0 (by exact_mod_cast hpM)
        rw [sq, mul_div_assoc]
        exact mul_le_mul_of_nonneg_right hle (by positivity)
    _ = log M * ∑ p ∈ Nat.primesLE M, log p / p := by rw [mul_sum]
    _ ≤ log M * (log M + log 4) :=
        mul_le_mul_of_nonneg_left (sum_primesLE_log_div_le hM) hlogM

/-- `(L t + a F / (p − 1))² / p ≤ 2 L² (t² / p) + 8 a² F² / p²` for `p ≥ 2`. -/
private lemma sq_add_div_le {p : ℝ} (hp : 2 ≤ p) (L t a F : ℝ) :
    (L * t + a / (p - 1) * F) ^ 2 / p ≤
      2 * L ^ 2 * (t ^ 2 / p) + 8 * a ^ 2 * F ^ 2 * (1 / p ^ 2) := by
  have hp0 : 0 < p := by linarith
  have hp1 : 0 < p - 1 := by linarith
  have hX : 0 ≤ (a * F) ^ 2 := sq_nonneg _
  have hpp : p ^ 2 / 4 ≤ (p - 1) ^ 2 * p := by nlinarith
  have h4 : (a / (p - 1) * F) ^ 2 / p ≤ 4 * a ^ 2 * F ^ 2 * (1 / p ^ 2) := by
    calc (a / (p - 1) * F) ^ 2 / p = (a * F) ^ 2 / ((p - 1) ^ 2 * p) := by
          field_simp
      _ ≤ (a * F) ^ 2 / (p ^ 2 / 4) := div_le_div_of_nonneg_left hX (by positivity) hpp
      _ = 4 * a ^ 2 * F ^ 2 * (1 / p ^ 2) := by field_simp
  calc (L * t + a / (p - 1) * F) ^ 2 / p
      ≤ 2 * ((L * t) ^ 2 + (a / (p - 1) * F) ^ 2) / p :=
        div_le_div_of_nonneg_right add_sq_le hp0.le
    _ = 2 * L ^ 2 * (t ^ 2 / p) + 2 * ((a / (p - 1) * F) ^ 2 / p) := by ring
    _ ≤ _ := by linarith

/-- `∑_p B_p² / p ≤ 4 L² X² / ℓ² + 16 a² F₀² / (K + 1)` for `B_p = L log p / ℓ + a F₀ / (p − 1)`
over primes `K < p ≤ M`, when `log M ≤ X` and `log 4 ≤ X`. -/
lemma sum_sq_div_le {P : Finset ℕ} {M K : ℕ} (hPM : P ⊆ Nat.primesLE M) (hPK : ∀ p ∈ P, K < p)
    (hM : 1 ≤ M) (L ℓ a F₀ X : ℝ) (hlogM : log M ≤ X) (hX : log 4 ≤ X) :
    ∑ p ∈ P, (L * (log p / ℓ) + a / (p - 1) * F₀) ^ 2 / p ≤
      4 * L ^ 2 * X ^ 2 / ℓ ^ 2 + 16 * a ^ 2 * F₀ ^ 2 / (K + 1) := by
  have hlogM0 : 0 ≤ log M := log_nonneg (by exact_mod_cast hM)
  have hlogsq : ∑ p ∈ P, log p ^ 2 / p ≤ 2 * X ^ 2 := by
    calc ∑ p ∈ P, log p ^ 2 / p ≤ ∑ p ∈ Nat.primesLE M, log p ^ 2 / p :=
          sum_le_sum_of_subset_of_nonneg hPM fun _ _ _ ↦ by positivity
      _ ≤ log M * (log M + log 4) := sum_primesLE_log_sq_div_le hM
      _ ≤ X * (X + X) := by gcongr; linarith
      _ = 2 * X ^ 2 := by ring
  calc ∑ p ∈ P, (L * (log p / ℓ) + a / (p - 1) * F₀) ^ 2 / p
      ≤ ∑ p ∈ P, (2 * L ^ 2 * ((log p / ℓ) ^ 2 / p) + 8 * a ^ 2 * F₀ ^ 2 * (1 / (p : ℝ) ^ 2)) :=
        sum_le_sum fun p hp ↦ sq_add_div_le
          (by exact_mod_cast (Nat.mem_primesLE.mp (hPM hp)).2.two_le) _ _ _ _
    _ = 2 * L ^ 2 / ℓ ^ 2 * ∑ p ∈ P, log p ^ 2 / p +
          8 * a ^ 2 * F₀ ^ 2 * ∑ p ∈ P, 1 / (p : ℝ) ^ 2 := by
        rw [sum_add_distrib, mul_sum, mul_sum]
        congr 1
        exact sum_congr rfl fun p _ ↦ by ring
    _ ≤ 2 * L ^ 2 / ℓ ^ 2 * (2 * X ^ 2) + 8 * a ^ 2 * F₀ ^ 2 * (2 / ((K : ℝ) + 1)) := by
        gcongr
        exact sum_one_div_sq_le_of_lt hPK
    _ = 4 * L ^ 2 * X ^ 2 / ℓ ^ 2 + 16 * a ^ 2 * F₀ ^ 2 / (K + 1) := by ring

end Erdos420
