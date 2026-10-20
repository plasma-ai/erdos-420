import Erdos420.Asymptotics
import Erdos420.Elementary.Mertens
import Mathlib.Analysis.Complex.ExponentialBounds
import PrimeGapsTheory.Sieve.PermissibleSupport.FunctionW

/-!
# The sieve modulus `M W'`

The sieve of `vendor/PrimeGapsLib` runs over `n ≡ w₀ (mod Q)` for a modulus `Q`
with `PrimeGaps.ModulusHyp`: `Q` is squarefree, divisible by every prime
`p ≤ D₀(N) = log log log N`, at most `N^η`, with `Q / φ(Q) ≪ log log N`, prime
factors at most `log N`, and `∑_{p ∣ Q} log p / (p − 1) ≪ log log N`.

For a squarefree `M ≤ X^{1/64}` whose prime factors are at most `log X / 2`, and
`N ∈ [X/2, 2X]`, the modulus `Q = M W'` with `W'` the product of the primes
`p ≤ D₀(N)` not dividing `M` is such a modulus for any `η > 1/64`. Its prime
factors are at most `log X / 2 ≤ log N`, so Mertens' theorems bound
`Q / φ(Q) ≤ ∏_{p ≤ log N} p / (p − 1) ≪ log log N` and
`∑_{p ≤ log N} log p / (p − 1) ≤ log log N + O(1)`.
-/

namespace Erdos420

open Filter Finset

/-- The product of the primes `p ≤ D₀(N)` not dividing `M`. -/
noncomputable def sieveCofactor (M : ℕ) (N : ℝ) : ℕ :=
  ∏ p ∈ (range (⌊PrimeGaps.D₀ N⌋₊ + 1)).filter (fun p ↦ p.Prime ∧ ¬p ∣ M), p

/-- `W'` divides the primorial of `D₀(N)`. -/
lemma sieveCofactor_dvd_primorial (M : ℕ) (N : ℝ) :
    sieveCofactor M N ∣ primorial ⌊PrimeGaps.D₀ N⌋₊ :=
  prod_dvd_prod_of_subset _ _ _ fun p hp ↦ by
    simp only [mem_filter] at hp ⊢
    exact ⟨hp.1, hp.2.1⟩

/-- `M` is coprime to `W'`. -/
lemma coprime_sieveCofactor (M : ℕ) (N : ℝ) : M.Coprime (sieveCofactor M N) :=
  Nat.Coprime.prod_right fun p hp ↦ by
    rw [mem_filter] at hp
    exact Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp.2.1).mpr hp.2.2)

/-- `W'` is squarefree. -/
lemma squarefree_sieveCofactor (M : ℕ) (N : ℝ) : Squarefree (sieveCofactor M N) :=
  Squarefree.squarefree_of_dvd (sieveCofactor_dvd_primorial M N) (squarefree_primorial _)

/-- Every prime `p ≤ D₀(N)` divides `M` or `W'`. -/
lemma primorial_dvd_mul_sieveCofactor (M : ℕ) (N : ℝ) :
    primorial ⌊PrimeGaps.D₀ N⌋₊ ∣ M * sieveCofactor M N := by
  rw [primorial, ← prod_filter_mul_prod_filter_not _ (· ∣ M)]
  simp only [filter_filter]
  refine mul_dvd_mul (prod_primes_dvd M (fun p hp ↦ ?_) fun p hp ↦ (mem_filter.mp hp).2.2) ?_
  · exact (mem_filter.mp hp).2.1.prime
  · exact dvd_rfl

/-- `Q / φ(Q) = ∏_{p ∣ Q} p / (p − 1)`. -/
lemma natCast_eq_totient_mul_prod_primeFactors (Q : ℕ) :
    (Q : ℝ) = Q.totient * ∏ p ∈ Q.primeFactors, (p : ℝ) / (p - 1) := by
  have h := congrArg (Nat.cast (R := ℝ)) (Nat.totient_mul_prod_primeFactors Q)
  have hp : ∀ p ∈ Q.primeFactors, (0 : ℝ) < (p : ℝ) - 1 := fun p hp ↦ by
    have := (Nat.prime_of_mem_primeFactors hp).two_le
    have : (2 : ℝ) ≤ p := by exact_mod_cast this
    linarith
  have hpos : (0 : ℝ) < ∏ p ∈ Q.primeFactors, ((p : ℝ) - 1) := prod_pos hp
  have hsub : ∏ p ∈ Q.primeFactors, ((p - 1 : ℕ) : ℝ) = ∏ p ∈ Q.primeFactors, ((p : ℝ) - 1) :=
    prod_congr rfl fun p hp ↦ by
      rw [Nat.cast_sub (Nat.prime_of_mem_primeFactors hp).one_le, Nat.cast_one]
  push_cast [Nat.cast_prod] at h
  rw [hsub] at h
  rw [prod_div_distrib, ← mul_div_assoc, h, mul_div_assoc, div_self hpos.ne', mul_one]

/-- For large `X`, `M W'` is a sieve modulus at every scale `N ∈ [X/2, 2X]`, for every
squarefree `M ≤ X^{1/64}` with prime factors at most `log X / 2`. -/
theorem exists_modulusHyp : ∃ CQ : ℝ, ∀ η > (1 / 64 : ℝ), ∀ᶠ X : ℕ in atTop, ∀ M : ℕ, ∀ N : ℝ,
    Squarefree M → (M : ℝ) ≤ (X : ℝ) ^ (1 / 64 : ℝ) →
    (∀ p : ℕ, p.Prime → p ∣ M → (p : ℝ) ≤ Real.log X / 2) → (X : ℝ) / 2 ≤ N → N ≤ 2 * X →
      PrimeGaps.ModulusHyp CQ η N (M * sieveCofactor M N) := by
  obtain ⟨C, hC⟩ := exists_abs_sum_inv_prime_sub_log_log_le
  refine ⟨max 5 (Real.exp (C + 4)), fun η hη ↦ ?_⟩
  set ε := η - 1 / 64 with hε
  have hε₀ : 0 < ε := by linarith
  have hlog4 := log_four_lt_two
  have hlog4₀ : 0 < Real.log 4 := Real.log_pos (by norm_num)
  -- the scale conditions, eventually in `N`: `log log N ≥ 2`, and `4^{D₀(N)} 2^{1/64} ≤ N^ε`
  -- since `log log N = o(log N)`
  have hev : ∀ᶠ N : ℝ in atTop, 2 ≤ Real.log (Real.log N) ∧
      (4 : ℝ) ^ PrimeGaps.D₀ N * 2 ^ (1 / 64 : ℝ) ≤ N ^ ε := by
    have hlo := (Real.isLittleO_log_id_atTop.comp_tendsto Real.tendsto_log_atTop).bound
      (c := ε / (2 * Real.log 4)) (by positivity)
    filter_upwards [(Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop 2,
      hlo, Real.tendsto_log_atTop.eventually_ge_atTop (Real.log 2 / 64 / (ε / 2)),
      eventually_gt_atTop 1] with N hLL hN hN₂ hN₁
    refine ⟨hLL, ?_⟩
    simp only [Function.comp_apply, id, Real.norm_eq_abs] at hN hLL
    have hL : 0 < Real.log N := Real.log_pos hN₁
    have hLL₀ : 0 < Real.log (Real.log N) := by linarith
    rw [abs_of_pos hLL₀, abs_of_pos hL] at hN
    -- `D₀(N) log 4 + log 2 / 64 ≤ ε log N`
    have hD₀ : PrimeGaps.D₀ N ≤ Real.log (Real.log N) := by
      rw [PrimeGaps.D₀]
      linarith [Real.log_le_sub_one_of_pos hLL₀]
    have h₁ : PrimeGaps.D₀ N * Real.log 4 ≤ ε / 2 * Real.log N := by
      calc PrimeGaps.D₀ N * Real.log 4 ≤ Real.log (Real.log N) * Real.log 4 := by gcongr
        _ ≤ ε / (2 * Real.log 4) * Real.log N * Real.log 4 := by gcongr
        _ = ε / 2 * Real.log N := by field_simp
    have h₂ : Real.log 2 / 64 ≤ ε / 2 * Real.log N := by
      rw [div_le_iff₀ (by positivity)] at hN₂
      linarith
    rw [Real.rpow_def_of_pos (by norm_num), Real.rpow_def_of_pos (by norm_num),
      Real.rpow_def_of_pos (by linarith), ← Real.exp_add, Real.exp_le_exp]
    linarith
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hev
  have hX : Tendsto (fun X : ℕ ↦ (X : ℝ) / 2) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_div_const two_pos
  filter_upwards [hX.eventually_ge_atTop (max N₀ 4)] with X hX
  intro M N hM hMX hMp hN₁ hN₂
  rw [max_le_iff] at hX
  obtain ⟨hLL, hpow⟩ := hN₀ N (hX.1.trans hN₁)
  set W' := sieveCofactor M N with hW'
  have hX₈ : (8 : ℝ) ≤ X := by linarith [hX.2]
  have hX₀ : (0 : ℝ) < X := by linarith
  have hN₀' : (0 : ℝ) < N := by linarith
  have hN₄ : (4 : ℝ) ≤ N := hX.2.trans hN₁
  have hL : 0 < Real.log N := Real.log_pos (by linarith)
  have hLL₀ : 0 < Real.log (Real.log N) := by linarith
  -- `log N ≥ e² ≥ 3`
  have hL₃ : 3 ≤ Real.log N := by
    have h₁ := (Real.le_log_iff_exp_le hL).mp hLL
    linarith [Real.add_one_le_exp (2 : ℝ)]
  -- `log X / 2 = log √X ≤ log N`
  have hlogXN : Real.log X / 2 ≤ Real.log N := by
    have h₁ : Real.sqrt X * Real.sqrt X = X := Real.mul_self_sqrt hX₀.le
    have h₂ : 2 ≤ Real.sqrt X := by
      have h := Real.sqrt_le_sqrt (show (4 : ℝ) ≤ X by linarith)
      rwa [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)] at h
    have hs : Real.sqrt X ≤ N := by nlinarith
    calc Real.log X / 2 = Real.log (Real.sqrt X) := by rw [Real.log_sqrt hX₀.le]
      _ ≤ Real.log N := Real.log_le_log (by positivity) hs
  have hD₀ : PrimeGaps.D₀ N ≤ Real.log N := by
    rw [PrimeGaps.D₀]
    linarith [Real.log_le_sub_one_of_pos hLL₀, Real.log_le_sub_one_of_pos hL]
  have hD₀₀ : 0 ≤ PrimeGaps.D₀ N := by
    rw [PrimeGaps.D₀]
    exact Real.log_nonneg (by linarith)
  -- the prime factors of `M W'` are primes `p ≤ log N`
  set T := (Iic ⌊Real.log N⌋₊).filter Nat.Prime with hT
  have hpf : ∀ p ∈ (M * W').primeFactors, (p : ℝ) ≤ Real.log N := by
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    rcases (Nat.Prime.dvd_mul hpp).mp (Nat.dvd_of_mem_primeFactors hp) with h | h
    · exact (hMp p hpp h).trans hlogXN
    · have h₁ := hpp.dvd_primorial_iff.mp (h.trans (sieveCofactor_dvd_primorial M N))
      exact ((Nat.cast_le.mpr h₁).trans (Nat.floor_le hD₀₀)).trans hD₀
  have hpfT : (M * W').primeFactors ⊆ T := fun p hp ↦ by
    rw [hT, mem_filter, mem_Iic]
    exact ⟨Nat.le_floor (hpf p hp), Nat.prime_of_mem_primeFactors hp⟩
  have hTLE : T = Nat.primesLE ⌊Real.log N⌋₊ := by
    rw [hT, Nat.primesLE_eq_filter_range, Nat.range_succ_eq_Iic]
  have hT₁ : 1 ≤ ⌊Real.log N⌋₊ := Nat.le_floor (by push_cast; linarith)
  have hTp : ∀ p ∈ T, (2 : ℝ) ≤ p := fun p hp ↦ by
    exact_mod_cast (mem_filter.mp hp).2.two_le
  -- `∑_{p ∈ T} log p / (p (p − 1)) ≤ 2`, so `∑_{p ∈ T} 1 / (p (p − 1)) ≤ 4`
  have hT₂ : ∑ p ∈ T, Real.log p / (p * (p - 1)) ≤ 2 := by
    rw [hTLE]
    exact sum_primesLE_log_div_mul_sub_one_le _
  have hT₄ : ∑ p ∈ T, (1 : ℝ) / (p * (p - 1)) ≤ 4 := by
    calc ∑ p ∈ T, (1 : ℝ) / (p * (p - 1)) ≤ ∑ p ∈ T, 2 * (Real.log p / (p * (p - 1))) := by
          refine sum_le_sum fun p hp ↦ ?_
          have h₂ := hTp p hp
          have hlog : 1 ≤ 2 * Real.log p := by
            have h := Real.log_le_log (by norm_num) h₂
            linarith [Real.log_two_gt_d9]
          rw [mul_div_assoc']
          exact div_le_div_of_nonneg_right hlog (by nlinarith)
      _ ≤ 4 := by rw [← mul_sum]; linarith
  have hlog4' : Real.log 4 ≤ 2 := hlog4.le
  refine ⟨Nat.squarefree_mul_iff.mpr ⟨coprime_sieveCofactor M N, hM, squarefree_sieveCofactor M N⟩,
    primorial_dvd_mul_sieveCofactor M N, ?_, ?_, hpf, ?_⟩
  · -- `M W' ≤ (2N)^{1/64} 4^{D₀(N)} ≤ N^η`
    have hW'4 : (W' : ℝ) ≤ (4 : ℝ) ^ PrimeGaps.D₀ N := by
      calc (W' : ℝ) ≤ (primorial ⌊PrimeGaps.D₀ N⌋₊ : ℕ) :=
            Nat.cast_le.mpr (Nat.le_of_dvd (primorial_pos _) (sieveCofactor_dvd_primorial M N))
        _ ≤ ((4 ^ ⌊PrimeGaps.D₀ N⌋₊ : ℕ) : ℝ) := Nat.cast_le.mpr (primorial_le_four_pow _)
        _ = (4 : ℝ) ^ (⌊PrimeGaps.D₀ N⌋₊ : ℝ) := by push_cast; rw [Real.rpow_natCast]
        _ ≤ (4 : ℝ) ^ PrimeGaps.D₀ N :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.floor_le hD₀₀)
    have hMN : (M : ℝ) ≤ (2 : ℝ) ^ (1 / 64 : ℝ) * N ^ (1 / 64 : ℝ) := by
      rw [← Real.mul_rpow (by norm_num) hN₀'.le]
      exact hMX.trans (Real.rpow_le_rpow hX₀.le (by linarith) (by norm_num))
    calc ((M * W' : ℕ) : ℝ) = M * W' := by push_cast; ring
      _ ≤ (2 : ℝ) ^ (1 / 64 : ℝ) * N ^ (1 / 64 : ℝ) * (4 : ℝ) ^ PrimeGaps.D₀ N := by gcongr
      _ = N ^ (1 / 64 : ℝ) * ((4 : ℝ) ^ PrimeGaps.D₀ N * 2 ^ (1 / 64 : ℝ)) := by ring
      _ ≤ N ^ (1 / 64 : ℝ) * N ^ ε := by gcongr
      _ = N ^ η := by rw [← Real.rpow_add hN₀', hε]; ring_nf
  · -- `M W' / φ(M W') = ∏_{p ∣ M W'} p / (p − 1) ≤ exp (∑_{p ≤ log N} 1 / (p − 1))`
    have hprod : ∏ p ∈ (M * W').primeFactors, (p : ℝ) / (p - 1) ≤
        Real.exp (C + 4) * Real.log (Real.log N) := by
      have hT1 : ∀ p ∈ T, (1 : ℝ) / (p - 1) = 1 / p + 1 / (p * (p - 1)) := fun p hp ↦ by
        have := hTp p hp
        have h₁ : (p : ℝ) - 1 ≠ 0 := by linarith
        have h₂ : (p : ℝ) ≠ 0 := by linarith
        field_simp
        ring
      have hmert := (abs_le.mp (hC (Real.log N) (by linarith))).2
      calc ∏ p ∈ (M * W').primeFactors, (p : ℝ) / (p - 1)
          ≤ ∏ p ∈ T, (p : ℝ) / (p - 1) := by
            refine prod_le_prod_of_subset_of_one_le₀ hpfT (fun p hp ↦ ?_) fun p hp _ ↦ ?_
            · have := hTp p (hpfT hp)
              exact div_nonneg (by linarith) (by linarith)
            · have := hTp p hp
              rw [one_le_div (by linarith)]
              linarith
        _ ≤ ∏ p ∈ T, Real.exp (1 / (p - 1)) := by
            refine prod_le_prod₀ (fun p hp ↦ ?_) fun p hp ↦ ?_
            · have := hTp p hp
              exact div_nonneg (by linarith) (by linarith)
            · have := hTp p hp
              have h := Real.add_one_le_exp (1 / ((p : ℝ) - 1))
              have h₀ : (p : ℝ) - 1 ≠ 0 := by linarith
              have h₁ : (p : ℝ) / (p - 1) = 1 / (p - 1) + 1 := by
                field_simp
                ring
              linarith
        _ = Real.exp (∑ p ∈ T, (1 / p + 1 / (p * (p - 1)))) := by
            rw [← Real.exp_sum]
            exact congrArg Real.exp (sum_congr rfl hT1)
        _ ≤ Real.exp (Real.log (Real.log (Real.log N)) + (C + 4)) := by
            rw [Real.exp_le_exp, sum_add_distrib]
            linarith
        _ = Real.exp (C + 4) * Real.log (Real.log N) := by
            rw [Real.exp_add, Real.exp_log hLL₀, mul_comm]
    rw [natCast_eq_totient_mul_prod_primeFactors (M * W')]
    have hφ : (0 : ℝ) ≤ ((M * W').totient : ℝ) := Nat.cast_nonneg _
    calc ((M * W').totient : ℝ) * ∏ p ∈ (M * W').primeFactors, (p : ℝ) / (p - 1)
        ≤ ((M * W').totient : ℝ) * (Real.exp (C + 4) * Real.log (Real.log N)) := by gcongr
      _ ≤ ((M * W').totient : ℝ) * (max 5 (Real.exp (C + 4)) * Real.log (Real.log N)) := by
          gcongr
          exact le_max_right _ _
      _ = _ := by ring
  · -- `∑_{p ∣ M W'} log p / (p − 1) ≤ ∑_{p ≤ log N} (log p / p + log p / (p (p − 1)))`
    calc ∑ p ∈ (M * W').primeFactors, Real.log p / (p - 1)
        ≤ ∑ p ∈ T, Real.log p / (p - 1) := by
          refine sum_le_sum_of_subset_of_nonneg hpfT fun p hp _ ↦ ?_
          have := hTp p hp
          exact div_nonneg (Real.log_nonneg (by linarith)) (by linarith)
      _ = ∑ p ∈ T, Real.log p / p + ∑ p ∈ T, Real.log p / (p * (p - 1)) := by
          rw [← sum_add_distrib]
          refine sum_congr rfl fun p hp ↦ ?_
          have := hTp p hp
          have h₁ : (p : ℝ) - 1 ≠ 0 := by linarith
          have h₂ : (p : ℝ) ≠ 0 := by linarith
          field_simp
          ring
      _ ≤ Real.log ⌊Real.log N⌋₊ + Real.log 4 + 2 := by
          rw [hTLE] at hT₂ ⊢
          linarith [sum_primesLE_log_div_le hT₁]
      _ ≤ Real.log (Real.log N) + 4 := by
          have h := Real.log_le_log (by exact_mod_cast hT₁) (Nat.floor_le hL.le)
          linarith
      _ ≤ max 5 (Real.exp (C + 4)) * Real.log (Real.log N) := by
          have h := mul_le_mul_of_nonneg_right (le_max_left 5 (Real.exp (C + 4))) hLL₀.le
          linarith

end Erdos420
