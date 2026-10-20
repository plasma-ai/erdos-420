import PrimeGapsTheory.Endgame.MainProp

/-!
# The divisor sum of Maynard's weights in the variables `y`

For `λ = yToL y`, i.e. `λ_d = (∏ᵢ μ(dᵢ) dᵢ) ∑_{d ∣ r} y_r / φ(r)`, the divisor sum at
`a = (n + hᵢ)ᵢ` is

  `∑_{dᵢ ∣ aᵢ} λ_d = ∑_r y_r ∏ᵢ κ(rᵢ, aᵢ)`,  `κ(r, a) = φ(r)⁻¹ ∑_{e ∣ (r, a)} μ(e) e`.

The kernel `κ` is multiplicative in `r`, and at a prime `p` it is `−1` if `p ∣ a` and
`1 / (p − 1)` otherwise.
-/

namespace Erdos420

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

/-- The multiplicative function `m ↦ ∑_{e ∣ m} μ(e) e`. -/
noncomputable def moebiusIdSum : ArithmeticFunction ℤ := pmul μ ↑ArithmeticFunction.id * ζ

/-- `m ↦ ∑_{e ∣ m} μ(e) e` is multiplicative. -/
lemma isMultiplicative_moebiusIdSum : moebiusIdSum.IsMultiplicative :=
  (isMultiplicative_moebius.pmul isMultiplicative_id.natCast).mul isMultiplicative_zeta.natCast

/-- `moebiusIdSum m = ∑_{e ∣ m} μ(e) e`. -/
lemma moebiusIdSum_apply (m : ℕ) : moebiusIdSum m = ∑ e ∈ m.divisors, μ e * e := by
  rw [moebiusIdSum, coe_mul_zeta_apply]
  simp [pmul_apply]

/-- The kernel `κ(r, a) = φ(r)⁻¹ ∑_{e ∣ (r, a)} μ(e) e`. -/
noncomputable def divKernel (r a : ℕ) : ℝ := (moebiusIdSum (r.gcd a) : ℝ) / r.totient

/-- `κ(p r, a) = κ(p, a) κ(r, a)` for a prime `p ∤ r`. -/
lemma divKernel_mul {p r : ℕ} (a : ℕ) (hp : p.Prime) (hpr : ¬p ∣ r) :
    divKernel (p * r) a = divKernel p a * divKernel r a := by
  have hcop : p.Coprime r := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpr
  have hgcd : (p * r).gcd a = p.gcd a * r.gcd a := by
    rw [Nat.gcd_comm, Nat.Coprime.gcd_mul a hcop, Nat.gcd_comm a, Nat.gcd_comm a]
  have hcop' : (p.gcd a).Coprime (r.gcd a) :=
    Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_left p a)
      (Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_left r a) hcop)
  rw [divKernel, divKernel, divKernel, hgcd,
    isMultiplicative_moebiusIdSum.map_mul_of_coprime hcop', Nat.totient_mul hcop]
  push_cast
  rw [mul_div_mul_comm]

/-- `κ(p, a) = −1` for a prime `p ∣ a`. -/
lemma divKernel_prime_of_dvd {p a : ℕ} (hp : p.Prime) (hpa : p ∣ a) : divKernel p a = -1 := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  rw [divKernel, Nat.gcd_eq_left hpa, moebiusIdSum_apply, Nat.Prime.sum_divisors hp,
    Nat.totient_prime hp, moebius_apply_prime hp]
  push_cast [hp.one_le, moebius_apply_one]
  rw [div_eq_iff (by linarith)]
  ring

/-- `κ(p, a) = 1 / (p − 1)` for a prime `p ∤ a`. -/
lemma divKernel_prime_of_not_dvd {p a : ℕ} (hp : p.Prime) (hpa : ¬p ∣ a) :
    divKernel p a = 1 / (p - 1) := by
  rw [divKernel, Nat.Coprime.gcd_eq_one ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpa),
    moebiusIdSum_apply, Nat.totient_prime hp]
  push_cast [hp.one_le]
  simp

/-- **The divisor sum in the variables `y`.** For `y` with permissible support and `a` with
nonzero coordinates, `∑_{dᵢ ∣ aᵢ} (yToL y)_d = ∑_r y_r ∏ᵢ κ(rᵢ, aᵢ)`. -/
theorem sum_yToL_eq_sum_divKernel {k R W : ℕ} {y : (Fin k → ℕ) →₀ ℝ}
    (hy : y.HasPermissibleSupport R W) (a : Fin k → ℕ) (ha : ∀ i, a i ≠ 0)
    {T : Finset (Fin k → ℕ)} (hT : y.support ⊆ T) :
    ∑ d ∈ Fintype.piFinset (fun i ↦ (a i).divisors), PrimeGaps.yToL y d =
      ∑ r ∈ T, y r * ∏ i, divKernel (r i) (a i) := by
  classical
  -- `∑_{e ∣ a, e ∣ r} μ(e) e = ∑_{e ∣ (r, a)} μ(e) e`
  have hinner : ∀ r a : ℕ, a ≠ 0 →
      ∑ e ∈ a.divisors, (if e ∣ r then (μ e : ℝ) * e else 0) = moebiusIdSum (r.gcd a) := by
    intro r a ha
    rw [← sum_filter, moebiusIdSum_apply]
    push_cast
    refine sum_congr (Finset.ext fun e ↦ ?_) fun _ _ ↦ rfl
    simp only [mem_filter, Nat.mem_divisors, Nat.dvd_gcd_iff]
    have : r.gcd a ≠ 0 := Nat.gcd_ne_zero_right ha
    tauto
  simp_rw [PrimeGaps.yToL_apply hy]
  rw [Finset.sum_congr rfl fun d _ ↦ by
    rw [Finsupp.sum_of_support_subset y hT _ (fun r _ ↦ by simp), Finset.mul_sum],
    Finset.sum_comm]
  refine sum_congr rfl fun r _ ↦ ?_
  calc ∑ d ∈ Fintype.piFinset (fun i ↦ (a i).divisors),
        ((∏ i, μ (d i) * (d i : ℤ) : ℤ) : ℝ) *
          (if ∀ i, d i ∣ r i then y r / ((∏ i, (r i).totient : ℕ) : ℝ) else 0)
      = y r / ((∏ i, (r i).totient : ℕ) : ℝ) * ∑ d ∈ Fintype.piFinset (fun i ↦ (a i).divisors),
          ∏ i, (if d i ∣ r i then (μ (d i) : ℝ) * d i else 0) := by
        rw [Finset.mul_sum]
        refine sum_congr rfl fun d _ ↦ ?_
        rw [prod_ite_zero]
        simp only [mem_univ, true_imp_iff]
        split_ifs <;> push_cast <;> ring
    _ = y r * ∏ i, divKernel (r i) (a i) := by
        rw [← prod_univ_sum (fun i ↦ (a i).divisors)
          (fun i e ↦ if e ∣ r i then (μ e : ℝ) * e else 0)]
        simp_rw [hinner _ _ (ha _), divKernel, prod_div_distrib]
        push_cast
        ring

end Erdos420
