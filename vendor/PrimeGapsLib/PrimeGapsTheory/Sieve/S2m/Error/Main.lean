/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsTheory.Sieve.S2m.Error.TauFourSums

import PrimeGapsTheory.Tactic.PaperTag

/-!
# The S2m error bound

Assembles the modulus sums into the total error contribution bound.

## Main results

* `MaynardS2Error.weighted_modulus_sum_bound`: the modulus sum weighted by `windowError`.
* `MaynardS2Error.exists_totalErrorContribution_le`: the total error contribution is
  `O(y_max ^ 2 * N / (Q log N ^ A))`.
-/

@[expose] public section

open Real

open scoped Finset

namespace MaynardS2Error

open ArithmeticFunction zeta

/-- `∑_{1 ≤ q ≤ N ^ θ} τ (3 * k) q ^ 4 / φ q ≤ Ct4 * Real.log N ^ B4` for all large `N`. -/
lemma tau4_over_totient_sum_bound {k : ℕ} (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    ∃ (Ct4 B4 N₀ : ℝ), 0 < Ct4 ∧ ∀ (N : ℝ), N₀ ≤ N →
      (∑ q ∈ {q ∈ (Finset.range (⌊N ^ θ⌋₊ + 1)) | 1 ≤ q},
        (τ (3 * k) q : ℝ) ^ 4 / (Nat.totient q : ℝ)) ≤ Ct4 * (Real.log N) ^ B4 := by
  have hIcc : ∀ n : ℕ, {q ∈ (Finset.range (n + 1)) | 1 ≤ q} = Finset.Icc 1 n := fun n ↦ by
    ext x
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]; omega
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · subst hk0
    refine ⟨1, 0, 0, one_pos, fun N _ ↦ ?_⟩
    have hval : ∀ q : ℕ, (τ (3 * 0) q : ℝ) ^ 4 / (Nat.totient q : ℝ) = if q = 1 then 1 else 0 :=
      fun q ↦ by by_cases hq1 : q = 1 <;> simp [hq1]
    simp only [hIcc, hval, Finset.sum_ite_eq', Real.rpow_zero, one_mul]
    split <;> norm_num
  · obtain ⟨C, B, hCpos, hbound⟩ := tau4_totient_full_sum_le (3 * k) (by omega)
    refine ⟨C * θ ^ B, B, max 2 (rexp (Real.log 2 / θ)), by positivity, fun N hN ↦ ?_⟩
    have hN2 : (2 : ℝ) ≤ N := (le_max_left _ _).trans hN
    have hb := hbound (N ^ θ) (PrimeGaps.two_le_rpow_of_exp_log_two_div_le hθ0
      ((le_max_right _ _).trans hN))
    rw [Real.log_rpow (by linarith), Real.mul_rpow hθ0.le (Real.log_nonneg (by linarith))] at hb
    rw [hIcc]
    exact hb.trans_eq (by ring)

/-- Under a level of distribution `θ`,
`∑_{1 ≤ q ≤ N ^ θ} τ (3 * k) q ^ 2 * windowError N q ≤ C₄ * N / Real.log N ^ A'` for large `N`. -/
lemma weighted_modulus_sum_bound {k : ℕ} (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hLoD : Nat.HasLevelOfDistribution Set.univ θ 1) (A' : ℝ) (hA' : 1 ≤ A') :
    ∃ (C₄ N₄ : ℝ), 0 < C₄ ∧ ∀ (N : ℝ), N₄ ≤ N →
      (∑ q ∈ {q ∈ (Finset.range (⌊N ^ θ⌋₊ + 1)) | 1 ≤ q},
        (τ (3 * k) q : ℝ) ^ 2 * windowError N q) ≤ C₄ * N / (Real.log N) ^ A' := by
  classical
  obtain ⟨Ct, N01, hCt, h1part⟩ := tau_sq_sum_bound (k := k) θ hθ0 hθ1 A'
  obtain ⟨Cp, hCp, hpoint⟩ := windowDisc_pointwise_bound
  obtain ⟨Ct4, B4raw, N04, hCt4, htau4raw⟩ := tau4_over_totient_sum_bound (k := k) θ hθ0 hθ1
  set B4 := max B4raw 0
  have hB4nn : (0 : ℝ) ≤ B4 := le_max_right _ _
  obtain ⟨Cd, N03, hCd, hEsum⟩ :=
    windowDisc_sum_le_hLoD θ hθ0 hLoD (2 * A' + B4) (by linarith [hB4nn])
  refine ⟨Ct + √(Cp * Ct4 * Cd), max (max (max N01 N04) N03) (rexp 1),
    by positivity, ?_⟩
  intro N hN
  have hN01 : N01 ≤ N :=
    (((le_max_left _ _).trans (le_max_left _ _)).trans (le_max_left _ _)).trans hN
  have hN04 : N04 ≤ N :=
    (((le_max_right _ _).trans (le_max_left _ _)).trans (le_max_left _ _)).trans hN
  have hN03 : N03 ≤ N := ((le_max_right _ _).trans (le_max_left _ _)).trans hN
  have hNe : rexp 1 ≤ N := (le_max_right _ _).trans hN
  have hN1 : (1 : ℝ) ≤ N := le_trans (by linarith [Real.add_one_le_exp (1 : ℝ)]) hNe
  have hN0 : (0 : ℝ) < N := one_pos.trans_le hN1
  have hL1 : (1 : ℝ) ≤ Real.log N := (Real.le_log_iff_exp_le hN0).2 hNe
  have hLpos : (0 : ℝ) < Real.log N := one_pos.trans_le hL1
  set L := Real.log N with hLdef
  set S := {q ∈ (Finset.range (⌊N ^ θ⌋₊ + 1)) | 1 ≤ q} with hSdef
  have hqle : ∀ q ∈ S, (q : ℝ) ≤ N := by
    intro q hq
    rw [hSdef, Finset.mem_filter, Finset.mem_range] at hq
    have h1 : (q : ℝ) ≤ (⌊N ^ θ⌋₊ : ℝ) := by exact_mod_cast Nat.lt_succ_iff.mp hq.1
    have h2 : (⌊N ^ θ⌋₊ : ℝ) ≤ N ^ θ := Nat.floor_le (Real.rpow_nonneg hN0.le θ)
    have h3 : N ^ θ ≤ N := by simpa using Real.rpow_le_rpow_of_exponent_le hN1 hθ1.le
    linarith
  have hq1 : ∀ q ∈ S, 1 ≤ q := fun q hq ↦ (Finset.mem_filter.mp hq).2
  have hEnn : ∀ q, 0 ≤ windowDisc N q := windowDisc_nonneg N
  have hsplit : (∑ q ∈ S, (τ (3 * k) q : ℝ) ^ 2 * windowError N q) =
      (∑ q ∈ S, (τ (3 * k) q : ℝ) ^ 2) +
        (∑ q ∈ S, (τ (3 * k) q : ℝ) ^ 2 * windowDisc N q) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun q _ ↦ by simp only [windowDisc]; ring
  rw [hsplit]
  have hp1 : (∑ q ∈ S, (τ (3 * k) q : ℝ) ^ 2) ≤ Ct * N / L ^ A' := h1part N hN01
  set sq : ℕ → ℝ := fun q ↦ √(windowDisc N q)
  have hsq2 : ∀ q, sq q ^ 2 = windowDisc N q := fun q ↦ Real.sq_sqrt (hEnn q)
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq S (fun q ↦ (τ (3 * k) q : ℝ) ^ 2 * sq q) (fun q ↦ sq q)
  have hCSlhs : (∑ q ∈ S, (τ (3 * k) q : ℝ) ^ 2 * sq q * sq q) =
      ∑ q ∈ S, (τ (3 * k) q : ℝ) ^ 2 * windowDisc N q :=
    Finset.sum_congr rfl fun q _ ↦ by rw [mul_assoc, ← pow_two, hsq2 q]
  have hCSf2 : (∑ q ∈ S, ((τ (3 * k) q : ℝ) ^ 2 * sq q) ^ 2) =
      ∑ q ∈ S, (τ (3 * k) q : ℝ) ^ 4 * windowDisc N q :=
    Finset.sum_congr rfl fun q _ ↦ by rw [mul_pow, hsq2 q]; ring
  have hCSg2 : (∑ q ∈ S, sq q ^ 2) = ∑ q ∈ S, windowDisc N q :=
    Finset.sum_congr rfl fun q _ ↦ hsq2 q
  rw [hCSlhs, hCSf2, hCSg2] at hCS
  have htau4part : (∑ q ∈ S, (τ (3 * k) q : ℝ) ^ 4 * windowDisc N q) ≤ Cp * N * (Ct4 * L ^ B4) := by
    have hstep : (∑ q ∈ S, (τ (3 * k) q : ℝ) ^ 4 * windowDisc N q) ≤
        Cp * N * (∑ q ∈ S, (τ (3 * k) q : ℝ) ^ 4 / (Nat.totient q : ℝ)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun q hq ↦ ?_
      rw [show Cp * N * ((τ (3 * k) q : ℝ) ^ 4 / (Nat.totient q : ℝ)) =
        (τ (3 * k) q : ℝ) ^ 4 * (Cp * N / (Nat.totient q : ℝ)) from by ring]
      exact mul_le_mul_of_nonneg_left (hpoint N hN1 q (hq1 q hq) (hqle q hq)) (by positivity)
    refine hstep.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    exact (htau4raw N hN04).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hL1 (le_max_left _ _)) hCt4.le)
  have hEpart : (∑ q ∈ S, windowDisc N q) ≤ Cd * N / L ^ (2 * A' + B4) := hEsum N hN03
  set D := ∑ q ∈ S, (τ (3 * k) q : ℝ) ^ 2 * windowDisc N q
  have hRHS : D ^ 2 ≤ (Cp * Ct4 * Cd) * N ^ 2 / L ^ (2 * A') := by
    refine (hCS.trans (mul_le_mul htau4part hEpart
      (Finset.sum_nonneg fun q _ ↦ hEnn q) (by positivity))).trans_eq ?_
    rw [Real.rpow_add hLpos]
    field_simp
  have hDbound : D ≤ √(Cp * Ct4 * Cd) * N / L ^ A' := by
    have hL2 : (L ^ A') ^ 2 = L ^ (2 * A') := by
      rw [← Real.rpow_natCast (L ^ A') 2, ← Real.rpow_mul hLpos.le]
      congr 1; push_cast; ring
    have hsqle : D ^ 2 ≤ (√(Cp * Ct4 * Cd) * N / L ^ A') ^ 2 := by
      rwa [div_pow, mul_pow, Real.sq_sqrt (by positivity), hL2]
    exact (abs_le_of_sq_le_sq' hsqle (by positivity)).2
  calc (∑ q ∈ S, (τ (3 * k) q : ℝ) ^ 2) + D
      ≤ Ct * N / L ^ A' + √(Cp * Ct4 * Cd) * N / L ^ A' := add_le_add hp1 hDbound
    _ = (Ct + √(Cp * Ct4 * Cd)) * N / L ^ A' := by ring

/-- Fix `k ≥ 2`, a fixed exponent `A > 0`, and fixed real parameters `θ, δ` with `0 < δ < θ/2`
and `θ < 1/2`. Assume the primes have power-saving level of distribution `θ` with saving `ϖ > θ`,
and let `Q` be a modulus with `ModulusHyp CQ η N Q`, `η < 2 δ`. Then the total contribution of the
`O(E(N,q))` error terms in the CRT expansion of `S_2^{(m)}` is `O(y_max² N / (Q (log N)^A))` as
`N → ∞`, with an implied constant `C` (and threshold `N₀`) depending on all the fixed data but not
on `N` or `Q`. Every modulus `q = Q ∏ [dᵢ, eᵢ]` is a multiple of `Q` below `N ^ θ`. -/
@[pg_tag "bg246" "lem_S2m_error"]
theorem exists_totalErrorContribution_le (k : ℕ) (hk : 2 ≤ k) (A : ℝ) (hA : 0 < A)
    (θ δ CQ η ϖ : ℝ) (hδ0 : 0 < δ) (hδθ : δ < θ / 2) (hθ : θ < 1 / 2) (hη : η < 2 * δ)
    (hPS : Nat.HasPowerSavingLevel θ ϖ) (hϖ : θ < ϖ) :
    ∃ (C N₀ : ℝ), 0 < C ∧ ∀ (N : ℝ), N₀ ≤ N → ∀ Q : ℕ, PrimeGaps.ModulusHyp CQ η N Q →
        ∀ (w : SieveWeights k N θ δ Q), totalErrorContribution w ≤
            C * (Finsupp.maxRealAbs (PrimeGaps.lToY w.lam)) ^ 2 * N / (Q * (Real.log N) ^ A) := by
  -- Each of the `≪ R² (log N) ^ (2k)` pairs `(d, e)` has `|λ_d λ_e| ≪ y² (log N) ^ (2k)` and,
  -- by `hPS` at the modulus `q = qMod Q d e < N ^ θ`, `windowError N q ≪ N ^ (1 - ϖ')`, with
  -- `ϖ' = min ϖ 1`. As `R² = N ^ (θ - 2δ)` and `Q ≤ N ^ η`, the total times `Q (log N) ^ A` is
  -- `≪ y² N ^ (1 - ε) (log N) ^ (4k + A) ≤ y² N`, where `ε = ϖ' - θ + (2δ - η) > 0`.
  classical
  have hθ0 : 0 < θ := by linarith
  set ϖ' := min ϖ 1
  have hϖ'ϖ : ϖ' ≤ ϖ := min_le_left _ _
  have hϖ'1 : ϖ' ≤ 1 := min_le_right _ _
  have hθϖ' : θ < ϖ' := lt_min hϖ (by linarith)
  set ε := ϖ' - θ + (2 * δ - η) with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  obtain ⟨C₁, N₁, hC₁, hlam⟩ := lambdaMax_bound k hk θ δ hδ0 hδθ (by linarith)
  obtain ⟨Nmod, hmod⟩ := modulus_Rsq_lt_Npow (θ := θ) (δ := δ) (CQ := CQ) hη
  obtain ⟨Cp, hCp⟩ := windowDisc_le_hPS hθ0.le hPS
  obtain ⟨Nlog, hNlog⟩ := Filter.eventually_atTop.mp
    ((isLittleO_log_rpow_rpow_atTop (4 * k + A) hε0).bound one_pos)
  set Cp' := max Cp 0
  have hCp'0 : 0 ≤ Cp' := le_max_right _ _
  refine ⟨C₁ ^ 2 * (2 ^ k) ^ 2 * (1 + 4 * Cp'), max (max N₁ Nmod) (max 3 Nlog),
    by positivity, fun N hN Q hQ w ↦ ?_⟩
  have hN₁ : N₁ ≤ N := ((le_max_left _ _).trans (le_max_left _ _)).trans hN
  have hNmod : Nmod ≤ N := ((le_max_right _ _).trans (le_max_left _ _)).trans hN
  have hN3 : 3 ≤ N := ((le_max_left _ _).trans (le_max_right _ _)).trans hN
  have hNlog' : Nlog ≤ N := ((le_max_right _ _).trans (le_max_right _ _)).trans hN
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hN0 : (0 : ℝ) < N := by linarith
  set L := Real.log N with hL
  have hL1 : 1 ≤ L := by
    rw [hL, Real.le_log_iff_exp_le hN0]
    linarith [Real.exp_one_lt_d9]
  have hL0 : 0 < L := one_pos.trans_le hL1
  set y := Finsupp.maxRealAbs (PrimeGaps.lToY w.lam)
  have hy0 : 0 ≤ y := Finsupp.maxRealAbs_nonneg
  set M := C₁ * y * L ^ k with hM
  have hM0 : 0 ≤ M := by positivity
  set R := N ^ (θ / 2 - δ) with hR
  have hR1 : 1 ≤ R := Real.one_le_rpow hN1 (by linarith)
  have hRN : R ≤ N :=
    (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith : θ / 2 - δ ≤ 1)).trans_eq (Real.rpow_one N)
  set B := ⌊R⌋₊
  have hB1 : 1 ≤ B := Nat.le_floor (by exact_mod_cast hR1)
  have hBR : (B : ℝ) ≤ R := Nat.floor_le (by linarith)
  set S := w.lam.support
  -- the support of `λ` has at most `R (2 log N) ^ k` points
  have hcard : (#S : ℝ) ≤ R * (2 * L) ^ k := by
    have hsub : S ⊆ Finset.filter (fun d : Fin k → ℕ ↦ (∀ i, 1 ≤ d i) ∧ (∏ i, d i) ≤ B)
        (Fintype.piFinset (fun _ : Fin k ↦ Finset.Icc 1 B)) := by
      intro d hd
      have hdmem := Finset.mem_permissibleSupport_iff.mp (w.support hd)
      have hpos : ∀ i, 1 ≤ d i := fun i ↦ Nat.one_le_iff_ne_zero.mpr
        ((Finset.prod_ne_zero_iff.mp hdmem.2.2.ne_zero) i (Finset.mem_univ i))
      rw [Finset.mem_filter, Fintype.mem_piFinset]
      exact ⟨fun i ↦ Finset.mem_Icc.mpr ⟨hpos i,
        (Finset.single_le_prod (fun j _ ↦ hpos j) (Finset.mem_univ i)).trans hdmem.1⟩,
        hpos, hdmem.1⟩
    have hHnn : (0 : ℝ) ≤ ∑ a ∈ Finset.Icc 1 B, (a : ℝ)⁻¹ :=
      Finset.sum_nonneg fun a _ ↦ by positivity
    have hH : (∑ a ∈ Finset.Icc 1 B, (a : ℝ)⁻¹) ≤ 2 * L := by
      rw [show (∑ a ∈ Finset.Icc 1 B, (a : ℝ)⁻¹) = (harmonic B : ℝ) by
        rw [harmonic_eq_sum_Icc]; push_cast; rfl]
      have hlogB : Real.log B ≤ L :=
        Real.log_le_log (by exact_mod_cast hB1) (hBR.trans hRN)
      linarith [harmonic_le_one_add_log B]
    calc (#S : ℝ)
        ≤ #(Finset.filter (fun d : Fin k → ℕ ↦ (∀ i, 1 ≤ d i) ∧ (∏ i, d i) ≤ B)
            (Fintype.piFinset (fun _ : Fin k ↦ Finset.Icc 1 B))) := by
          exact_mod_cast Finset.card_le_card hsub
      _ ≤ (B : ℝ) * (∑ a ∈ Finset.Icc 1 B, (a : ℝ)⁻¹) ^ k := PrimeGaps.divisor_count_le k B
      _ ≤ R * (2 * L) ^ k :=
          mul_le_mul hBR (pow_le_pow_left₀ hHnn hH k) (by positivity) (by positivity)
  -- `windowError N q ≤ (1 + 4 Cp') N ^ (1 - ϖ')` at every modulus `q = qMod Q d e`
  have hEbd : 1 + Cp' * ((2 * N) ^ (1 - ϖ) + N ^ (1 - ϖ)) ≤ (1 + 4 * Cp') * N ^ (1 - ϖ') := by
    have hp1 : 1 ≤ N ^ (1 - ϖ') := Real.one_le_rpow hN1 (by linarith)
    have hp2 : (2 * N) ^ (1 - ϖ) ≤ 2 * N ^ (1 - ϖ') :=
      calc (2 * N) ^ (1 - ϖ)
          ≤ (2 * N) ^ (1 - ϖ') := Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
        _ = 2 ^ (1 - ϖ') * N ^ (1 - ϖ') := Real.mul_rpow (by norm_num) hN0.le
        _ ≤ 2 * N ^ (1 - ϖ') := by
          gcongr
          exact (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)).trans_eq
            (Real.rpow_one 2)
    have hp3 : N ^ (1 - ϖ) ≤ 2 * N ^ (1 - ϖ') :=
      (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith : 1 - ϖ ≤ 1 - ϖ')).trans (by linarith)
    calc 1 + Cp' * ((2 * N) ^ (1 - ϖ) + N ^ (1 - ϖ))
        ≤ 1 + Cp' * (4 * N ^ (1 - ϖ')) := by gcongr; linarith
      _ ≤ (1 + 4 * Cp') * N ^ (1 - ϖ') := by nlinarith
  have hE : ∀ d ∈ S, ∀ e ∈ S,
      windowError N (PrimeGaps.qMod Q d e) ≤ (1 + 4 * Cp') * N ^ (1 - ϖ') := by
    intro d hd e he
    have hdmem := w.support hd
    have hemem := w.support he
    have hd1 : ∀ i, 0 < d i := fun i ↦
      Nat.pos_of_ne_zero (Finset.squarefree_of_mem_permissibleSupport hdmem i).ne_zero
    have he1 : ∀ i, 0 < e i := fun i ↦
      Nat.pos_of_ne_zero (Finset.squarefree_of_mem_permissibleSupport hemem i).ne_zero
    have hq1 : 1 ≤ PrimeGaps.qMod Q d e := PrimeGaps.lem_qMod_pos Q d e hQ.pos hd1 he1
    have hdR : ((∏ i, d i : ℕ) : ℝ) ≤ R :=
      le_trans (by exact_mod_cast (Finset.mem_permissibleSupport_iff.mp hdmem).1) hBR
    have heR : ((∏ i, e i : ℕ) : ℝ) ≤ R :=
      le_trans (by exact_mod_cast (Finset.mem_permissibleSupport_iff.mp hemem).1) hBR
    have hlcm :
        ((∏ i, Nat.lcm (d i) (e i) : ℕ) : ℝ) ≤ ((∏ i, d i : ℕ) : ℝ) * ((∏ i, e i : ℕ) : ℝ) := by
      rw [← Nat.cast_mul, Nat.cast_le, ← Finset.prod_mul_distrib]
      exact Finset.prod_le_prod₀ (fun _ _ ↦ Nat.zero_le _)
        fun i _ ↦ Nat.lcm_le_mul (hd1 i) (he1 i)
    have hqN : (PrimeGaps.qMod Q d e : ℝ) ≤ N ^ θ := by
      unfold PrimeGaps.qMod
      rw [Nat.cast_mul]
      calc (Q : ℝ) * ((∏ i, Nat.lcm (d i) (e i) : ℕ) : ℝ)
          ≤ (Q : ℝ) * R ^ 2 := by
            gcongr
            rw [pow_two]
            exact hlcm.trans (mul_le_mul hdR heR (by positivity) (by linarith))
        _ ≤ N ^ θ := (hmod N hNmod Q hQ).le
    calc windowError N (PrimeGaps.qMod Q d e)
        = 1 + windowDisc N (PrimeGaps.qMod Q d e) := by rw [windowDisc]; ring
      _ ≤ 1 + Cp' * ((2 * N) ^ (1 - ϖ) + N ^ (1 - ϖ)) := by
          gcongr
          exact (hCp N hN3 _ hq1 hqN).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
            (by positivity))
      _ ≤ (1 + 4 * Cp') * N ^ (1 - ϖ') := hEbd
  -- collapse the double `tsum` to the support and bound it termwise
  have htot : totalErrorContribution w ≤
      (R * (2 * L) ^ k) * ((R * (2 * L) ^ k) * (M * M * ((1 + 4 * Cp') * N ^ (1 - ϖ')))) := by
    have hsum : totalErrorContribution w = ∑ d ∈ S, ∑ e ∈ S,
        |w.lam d| * |w.lam e| * windowError N (PrimeGaps.qMod Q d e) := by
      unfold totalErrorContribution
      rw [tsum_eq_sum (s := S) ?_]
      · refine Finset.sum_congr rfl fun d hd ↦ ?_
        rw [tsum_eq_sum (s := S) ?_]
        · refine Finset.sum_congr rfl fun e he ↦ ?_
          rw [ite_eq_left (mul_ne_zero (Finsupp.mem_support_iff.mp hd)
            (Finsupp.mem_support_iff.mp he))]
        · intro e he
          rw [ite_eq_right (by simp [Finsupp.notMem_support_iff.mp he])]
      · intro d hd
        simp [Finsupp.notMem_support_iff.mp hd]
    rw [hsum]
    calc (∑ d ∈ S, ∑ e ∈ S, |w.lam d| * |w.lam e| * windowError N (PrimeGaps.qMod Q d e))
        ≤ ∑ d ∈ S, ∑ e ∈ S, M * M * ((1 + 4 * Cp') * N ^ (1 - ϖ')) :=
          Finset.sum_le_sum fun d hd ↦ Finset.sum_le_sum fun e he ↦
            mul_le_mul (mul_le_mul (hlam N hN₁ Q w d) (hlam N hN₁ Q w e) (abs_nonneg _) hM0)
              (hE d hd e he) (windowError_nonneg _ _) (mul_nonneg hM0 hM0)
      _ = #S * (#S * (M * M * ((1 + 4 * Cp') * N ^ (1 - ϖ')))) := by
          simp only [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (R * (2 * L) ^ k) * ((R * (2 * L) ^ k) * (M * M * ((1 + 4 * Cp') * N ^ (1 - ϖ')))) := by
          gcongr
  -- the exponent bookkeeping: `R² N ^ (1 - ϖ') (log N) ^ (4k) Q (log N) ^ A ≤ N`
  have hRsq : R ^ 2 = N ^ (θ - 2 * δ) := by
    rw [hR, ← Real.rpow_natCast (N ^ (θ / 2 - δ)) 2, ← Real.rpow_mul hN0.le]
    congr 1; push_cast; ring
  have hLpow : (L ^ k) ^ 4 * L ^ A ≤ N ^ ε := by
    have hlogN := hNlog N hNlog'
    rw [one_mul, Real.norm_of_nonneg (Real.rpow_nonneg hL0.le _),
      Real.norm_of_nonneg (Real.rpow_nonneg hN0.le _)] at hlogN
    refine le_of_eq_of_le ?_ hlogN
    rw [← pow_mul, ← Real.rpow_natCast, ← Real.rpow_add hL0]
    congr 1; push_cast; ring
  have hexp : N ^ (θ - 2 * δ) * N ^ (1 - ϖ') * N ^ η * N ^ ε = N := by
    rw [← Real.rpow_add hN0, ← Real.rpow_add hN0, ← Real.rpow_add hN0,
      show θ - 2 * δ + (1 - ϖ') + η + ε = 1 by rw [hε]; ring, Real.rpow_one]
  have hkey : R ^ 2 * N ^ (1 - ϖ') * (L ^ k) ^ 4 * ((Q : ℝ) * L ^ A) ≤ N :=
    calc R ^ 2 * N ^ (1 - ϖ') * (L ^ k) ^ 4 * ((Q : ℝ) * L ^ A)
        = N ^ (θ - 2 * δ) * N ^ (1 - ϖ') * Q * ((L ^ k) ^ 4 * L ^ A) := by rw [hRsq]; ring
      _ ≤ N ^ (θ - 2 * δ) * N ^ (1 - ϖ') * N ^ η * N ^ ε := by
          gcongr
          exact hQ.le_rpow
      _ = N := hexp
  have hQpos : (0 : ℝ) < Q := by exact_mod_cast hQ.pos
  rw [le_div_iff₀ (by positivity)]
  calc totalErrorContribution w * ((Q : ℝ) * L ^ A)
      ≤ (R * (2 * L) ^ k) * ((R * (2 * L) ^ k) * (M * M * ((1 + 4 * Cp') * N ^ (1 - ϖ')))) *
          ((Q : ℝ) * L ^ A) := by gcongr
    _ = C₁ ^ 2 * (2 ^ k) ^ 2 * (1 + 4 * Cp') * y ^ 2 *
          (R ^ 2 * N ^ (1 - ϖ') * (L ^ k) ^ 4 * ((Q : ℝ) * L ^ A)) := by
        rw [hM, mul_pow]; ring
    _ ≤ C₁ ^ 2 * (2 ^ k) ^ 2 * (1 + 4 * Cp') * y ^ 2 * N := by gcongr

end MaynardS2Error
