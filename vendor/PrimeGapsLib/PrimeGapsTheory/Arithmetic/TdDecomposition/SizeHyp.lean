/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsTheory.Arithmetic.TdDecomposition.Decomp

import PrimeGapsTheory.Tactic.PaperTag

/-!
# Size hypotheses for the inner sum

Divisor and omega bounds giving the size hypothesis for the inner `w` sum.

## Main results

* `slem_T_d_inner_w_sum`
-/

@[expose] public section

open Real

open scoped Finset

open ArithmeticFunction

namespace PrimeGaps

/-- `n * τ(n) / φ(n) ≤ 4 ^ ω(n)` for squarefree `n ≥ 1`. -/
theorem sqfree_prod_tau_over_phi_le (n : ℕ) (hn : Squarefree n) (h1 : 1 ≤ n) :
    (n : ℝ) * (#n.divisors : ℝ) / (n.totient : ℝ) ≤ 4 ^ #n.primeFactors := by
  have h0 : n ≠ 0 := by omega
  have htau : #n.divisors = 2 ^ #n.primeFactors := by
    rw [Nat.card_divisors h0]
    refine Finset.prod_eq_pow_card fun p hp ↦ ?_
    have := (Nat.prime_of_mem_primeFactors hp).factorization_pos_of_dvd h0
      (Nat.dvd_of_mem_primeFactors hp)
    have := hn.natFactorization_le_one p
    omega
  rw [htau]
  push_cast
  rw [squarefree_eq_prod_primes n hn, totient_eq_prod_sub_one n (by omega) hn,
    ← Finset.prod_const (2 : ℝ), ← Finset.prod_const (4 : ℝ), ← Finset.prod_mul_distrib,
    ← Finset.prod_div_distrib]
  refine Finset.prod_le_prod₀ (fun p hp ↦ ?_) fun p hp ↦ ?_ <;>
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
  · exact div_nonneg (by positivity) (by linarith)
  · rw [div_le_iff₀ (by linarith)]; nlinarith

/-- For `B ≥ 2` and `n ≥ 1`, the number of prime factors of `n` is at most
`π(B) + log n / log B`. -/
theorem omega_le_pi_add_log_div (B n : ℕ) (hB : 2 ≤ B) (hn : 1 ≤ n) :
    (#n.primeFactors : ℝ) ≤ (#((Finset.Icc 2 B).filter Nat.Prime) : ℝ) +
          Real.log n / Real.log B := by
  have hlogB_pos : 0 < Real.log B := Real.log_pos (by exact_mod_cast (by omega : 1 < B))
  set S := n.primeFactors.filter (fun p ↦ p ≤ B) with hS
  set T := n.primeFactors.filter (fun p ↦ ¬ p ≤ B) with hT
  have hScard : #S ≤ #((Finset.Icc 2 B).filter Nat.Prime) := by
    refine Finset.card_le_card fun p hp ↦ ?_
    obtain ⟨hpmem, hple⟩ := Finset.mem_filter.1 (hS ▸ hp)
    have hprime := Nat.prime_of_mem_primeFactors hpmem
    exact Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨hprime.two_le, hple⟩, hprime⟩
  have hBpow_le : B ^ #T ≤ n :=
    calc B ^ #T = ∏ _ ∈ T, B := (Finset.prod_const B).symm
      _ ≤ ∏ p ∈ T, p := Finset.prod_le_prod' fun p hp ↦ by
            have := Finset.mem_filter.1 (hT ▸ hp); omega
      _ ≤ n := Nat.le_of_dvd (by omega)
            ((Finset.prod_dvd_prod_of_subset _ _ _ (hT ▸ Finset.filter_subset _ _)).trans
              (Nat.prod_primeFactors_dvd n))
  have hTdiv : (#T : ℝ) ≤ Real.log n / Real.log B := by
    rw [le_div_iff₀ hlogB_pos, ← Real.log_pow]
    exact Real.log_le_log (by positivity) (by exact_mod_cast hBpow_le)
  have hsplit : (#n.primeFactors : ℝ) = #S + #T := by
    rw [hS, hT, ← Nat.cast_add, Finset.card_filter_add_card_filter_not]
  linarith [hsplit, (Nat.cast_le (α := ℝ)).2 hScard]

open Filter in
/-- **Sub-lemma (W').** Uniform in `n`: for a suitable prime bound `B`, for every
`n ≥ 1`, `4^{ω(n)} ≤ 4^{π(B)} · n^{log 4 / log B}`, with `log 4 / log B` made as
small as we like by choosing `B` large. Consequence of `omega_le_pi_add_log_div`
by exponentiating (`4^x = exp(x·log4)`, `n^y = exp(y·log n)`). -/
theorem four_pow_omega_le_const_mul_rpow (B n : ℕ) (hB : 2 ≤ B) (hn : 1 ≤ n) :
    (4 : ℝ) ^ #n.primeFactors ≤ (4 : ℝ) ^ #((Finset.Icc 2 B).filter Nat.Prime) *
          (n : ℝ) ^ (Real.log 4 / Real.log B) := by
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn
  rw [← Real.rpow_natCast (4 : ℝ) #n.primeFactors,
    ← Real.rpow_natCast (4 : ℝ) #((Finset.Icc 2 B).filter Nat.Prime)]
  simp only [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 4), Real.rpow_def_of_pos hn_pos,
    ← Real.exp_add, Real.exp_le_exp]
  calc Real.log 4 * (#n.primeFactors : ℝ)
      ≤ Real.log 4 * ((#((Finset.Icc 2 B).filter Nat.Prime) : ℝ) + Real.log n / Real.log B) :=
        mul_le_mul_of_nonneg_left (omega_le_pi_add_log_div B n hB hn)
          (Real.log_nonneg (by norm_num))
    _ = _ := by ring

open Filter in
open scoped PrimeGaps.sieveTruncation in
/-- **Crux size lemma (S4).** For `N` large, every modulus `Q` with `ModulusHyp CQ η N Q`
(where `η ≤ 4 (θ / 2 - δ)`, i.e. `Q ≤ R ^ 4`), and whenever `d` is squarefree and coprime to `Q`,
`d ≤ R^{1/2}`, `1 ≤ e`, `e ≤ R^{1/8}`, and `e` is coprime to `d·Q`, the Mertens size hypothesis
holds: `R/(d e²) ≥ 𝒲·τ(𝒲)/φ(𝒲)` with `𝒲 = d·Q`, the paper truncation `R`. -/
theorem slem_T_d_inner_size_hyp (δ θ : ℝ) (hδθ : 0 < δ ∧ δ < θ / 2 ∧ θ < 1) (CQ η : ℝ)
    (hη : η ≤ 4 * (θ / 2 - δ)) :
    ∀ᶠ N : ℕ in atTop, ∀ Q : ℕ, ModulusHyp CQ η N Q →
      ∀ d e : ℕ, Squarefree d → Nat.Coprime d Q → (d : ℝ) ≤ R ^ (1 / 2 : ℝ) →
      1 ≤ e → (e : ℝ) ≤ R ^ (1 / 8 : ℝ) →
      Nat.Coprime e (d * Q) → let 𝒲 := d * Q
        (𝒲 : ℝ) * (#𝒲.divisors : ℝ) / (𝒲.totient : ℝ) ≤ R / (d * e ^ 2) := by
  have hc : 0 < θ / 2 - δ := by linarith [hδθ.2.1]
  obtain ⟨B, hB_def⟩ : ∃ B : ℕ, B = 4 ^ 32 := ⟨_, rfl⟩
  have hB2 : 2 ≤ B := by rw [hB_def]; exact Nat.le_self_pow (by norm_num) _ |>.trans' (by norm_num)
  have hexp : Real.log 4 / Real.log B = 1 / 32 := by
    have h4 : Real.log 4 ≠ 0 := (Real.log_pos (by norm_num)).ne'
    rw [hB_def, Nat.cast_pow, Real.log_pow]
    push_cast
    field_simp
  set K : ℝ := (4 : ℝ) ^ #((Finset.Icc 2 B).filter Nat.Prime) with hK_def
  have hK0 : 0 < K := by positivity
  have hRtend : Tendsto (fun N : ℕ ↦ (N : ℝ) ^ (θ / 2 - δ)) atTop atTop :=
    (tendsto_rpow_atTop hc).comp tendsto_natCast_atTop_atTop
  have hKR : ∀ᶠ N : ℕ in atTop, K ≤ ((N : ℝ) ^ (θ / 2 - δ)) ^ ((7 : ℝ) / 64) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 7 / 64)).comp hRtend).eventually_ge_atTop K
  filter_upwards [hKR, hRtend.eventually_ge_atTop 1, tendsto_natCast_atTop_atTop.eventually_ge_atTop 1]
    with N hKR hR1 hN1 Q hQ d e hd hcop_d hd_le he1 he_le _ 𝒲
  have hR_pos : (0 : ℝ) < R := by linarith
  have hQR : (Q : ℝ) ≤ R ^ (4 : ℝ) := by
    rw [← Real.rpow_mul (by positivity)]
    exact hQ.le_rpow.trans (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN1) (by linarith))
  have hd1 : 1 ≤ d := Nat.one_le_iff_ne_zero.2 hd.ne_zero
  have h𝒲sq : Squarefree 𝒲 := Nat.squarefree_mul_iff.2 ⟨hcop_d, hd, hQ.squarefree⟩
  have h𝒲1 : 1 ≤ 𝒲 := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero hd.ne_zero hQ.ne_zero)
  have h𝒲R : (𝒲 : ℝ) ≤ R ^ ((9 : ℝ) / 2) := by
    simp only [𝒲, Nat.cast_mul]
    calc (d : ℝ) * Q ≤ R ^ (1 / 2 : ℝ) * R ^ (4 : ℝ) := by gcongr
      _ = R ^ ((9 : ℝ) / 2) := by rw [← Real.rpow_add hR_pos]; norm_num
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd1
  have he0 : (0 : ℝ) < e := by exact_mod_cast he1
  -- The right-hand side is at least `R^{1/4}`.
  have hRHS : R ^ ((1 : ℝ) / 4) ≤ R / (d * e ^ 2) := by
    have hde2 : (d : ℝ) * e ^ 2 ≤ R ^ ((3 : ℝ) / 4) :=
      calc (d : ℝ) * e ^ 2 ≤ R ^ (1 / 2 : ℝ) * (R ^ (1 / 8 : ℝ)) ^ 2 := by gcongr
        _ = R ^ ((3 : ℝ) / 4) := by
          rw [← Real.rpow_natCast (R ^ (1 / 8 : ℝ)) 2, ← Real.rpow_mul hR_pos.le,
            ← Real.rpow_add hR_pos]
          norm_num
    rw [le_div_iff₀ (by positivity)]
    calc R ^ ((1 : ℝ) / 4) * ((d : ℝ) * e ^ 2) ≤ R ^ ((1 : ℝ) / 4) * R ^ ((3 : ℝ) / 4) := by
          gcongr
      _ = R := by rw [← Real.rpow_add hR_pos]; norm_num
  calc (𝒲 : ℝ) * (#𝒲.divisors : ℝ) / (𝒲.totient : ℝ) ≤ 4 ^ #𝒲.primeFactors :=
        sqfree_prod_tau_over_phi_le 𝒲 h𝒲sq h𝒲1
    _ ≤ K * (𝒲 : ℝ) ^ ((1 : ℝ) / 32) := by
        simpa only [hexp] using four_pow_omega_le_const_mul_rpow B 𝒲 hB2 h𝒲1
    _ ≤ R ^ ((7 : ℝ) / 64) * (R ^ ((9 : ℝ) / 2)) ^ ((1 : ℝ) / 32) := by gcongr
    _ = R ^ ((1 : ℝ) / 4) := by
        rw [← Real.rpow_mul hR_pos.le, ← Real.rpow_add hR_pos]; norm_num
    _ ≤ R / (d * e ^ 2) := hRHS

open Filter in
open scoped PrimeGaps.sieveTruncation in
/-- Mertens for the inner sum: `∑_{w ≤ R/(d e ^ 2), (w, 𝒲) = 1} 1 / w` equals
`(φ(𝒲) / 𝒲) * (log R - log d - 2 log e)` up to `C * (φ(𝒲) / 𝒲) * (1 + log (log (exp 1 * 𝒲)))`,
where `𝒲 = d * Q`, for every modulus `Q` with `ModulusHyp CQ η N Q`. -/
@[pg_tag "bg246" "slem_T_d_inner_w_sum"]
theorem slem_T_d_inner_w_sum (δ θ : ℝ) (hδθ : 0 < δ ∧ δ < θ / 2 ∧ θ < 1) (CQ η : ℝ)
    (hη : η ≤ 4 * (θ / 2 - δ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop, ∀ Q : ℕ, ModulusHyp CQ η N Q →
      ∀ d e : ℕ, Squarefree d → Nat.Coprime d Q →
      (d : ℝ) ≤ R ^ (1 / 2 : ℝ) →
      1 ≤ e → (e : ℝ) ≤ R ^ (1 / 8 : ℝ) →
      Nat.Coprime e (d * Q) → let 𝒲 := d * Q
        |(∑ w ∈ {w ∈ Finset.Icc 1 ⌊R / (d * e ^ 2)⌋₊ | Nat.Coprime w 𝒲},
              (1 : ℝ) / w) - (𝒲.totient : ℝ) / 𝒲 * (Real.log R - Real.log d - 2 * Real.log e)| ≤
          C * ((𝒲.totient : ℝ) / 𝒲) * (1 + Real.log (Real.log (rexp 1 * 𝒲))) := by
  obtain ⟨C, hC, hmert⟩ := mertens_reciprocal_general
  refine ⟨C, hC, ?_⟩
  filter_upwards [slem_T_d_inner_size_hyp δ θ hδθ CQ η hη,
      R_eventually_ge θ δ hδθ.2.1 256] with N hsize hR256
  intro Q hQ d e hd hcop_d hd_le he1 he_le hcop_e 𝒲
  have hsize' := hsize Q hQ d e hd hcop_d hd_le he1 he_le hcop_e
  simp only at hsize'
  have h𝒲_sqfree : Squarefree 𝒲 := Nat.squarefree_mul_iff.2 ⟨hcop_d, hd, hQ.squarefree⟩
  have h𝒲_pos : 1 ≤ 𝒲 := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero hd.ne_zero hQ.ne_zero)
  have hR_pos : (0 : ℝ) < R := lt_of_lt_of_le (by norm_num) hR256
  have hd_pos : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero hd.ne_zero
  have he_pos : (0 : ℝ) < e := by exact_mod_cast he1
  have hlog : Real.log (R / (d * e ^ 2)) = Real.log R - Real.log d - 2 * Real.log e := by
    rw [Real.log_div hR_pos.ne' (by positivity),
      Real.log_mul hd_pos.ne' (by positivity), Real.log_pow]
    push_cast
    ring
  rw [← hlog]
  exact hmert 𝒲 h𝒲_sqfree h𝒲_pos (R / (d * e ^ 2)) hsize'

end PrimeGaps
