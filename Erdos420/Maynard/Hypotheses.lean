import Erdos420.Analytic.PrimeCounting
import Erdos420.Asymptotics
import PrimeGapsTheory.NumberTheory.LevelOfDistribution
import PrimeGapsTheory.NumberTheory.PNT

/-!
# The analytic inputs of Maynard's sieve

The generalized sieve of `vendor/PrimeGapsLib` takes the prime number theorem
`PNT.PrimeCountingEstimate` and a power-saving level of distribution
`Nat.HasPowerSavingLevel θ ϖ` as hypotheses. Both follow from
`Erdos420.exists_abs_primeCountingZMod_sub_le`, whose error `x^{15/16} log² x` is
`O(x^{1 − ϖ})` for every `ϖ < 1/16`, uniformly in `q ≤ x`.
-/

namespace Erdos420

open Real

/-- The prime number theorem `π(N) = N / log N + O(N / log² N)`. -/
theorem primeCountingEstimate : PNT.PrimeCountingEstimate := pnt_primeCounting

/-- The primes have power-saving level of distribution `θ ≤ 1` with saving `ϖ < 1/16`. -/
theorem hasPowerSavingLevel {θ ϖ : ℝ} (hθ : θ ≤ 1) (hϖ : ϖ < 1 / 16) :
    Nat.HasPowerSavingLevel θ ϖ := by
  obtain ⟨K, hK⟩ := exists_abs_primeCountingZMod_sub_le
  set ε := 1 / 16 - ϖ with hε
  have hε₀ : 0 < ε := by linarith
  refine ⟨|K| * (2 / ε) ^ 2, fun x hx q hq hqx a ↦ ?_⟩
  have hx₀ : 0 < x := by linarith
  have hx₁ : 1 ≤ x := by linarith
  -- `q ≤ x^θ ≤ x`
  have hqx' : (q : ℝ) ≤ x :=
    hqx.trans (by simpa using Real.rpow_le_rpow_of_exponent_le hx₁ hθ)
  -- `log² x ≤ (2/ε)² x^ε`
  have hlog₂ : Real.log x ^ 2 ≤ (2 / ε) ^ 2 * x ^ ε := log_sq_le_mul_rpow hx₁ hε₀
  have h := hK x (by linarith) q hq hqx' a
  calc |(π(x; q, a) : ℝ) - π(x) / q.totient|
      ≤ K * x ^ (15 / 16 : ℝ) * Real.log x ^ 2 := h
    _ ≤ |K| * x ^ (15 / 16 : ℝ) * ((2 / ε) ^ 2 * x ^ ε) := by
        gcongr
        exact le_abs_self K
    _ = |K| * (2 / ε) ^ 2 * x ^ (1 - ϖ) := by
        rw [show (1 - ϖ) = 15 / 16 + ε by rw [hε]; ring, Real.rpow_add hx₀]
        ring

end Erdos420
