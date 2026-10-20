import PrimeGapsTheory.Endgame.MainProp

/-!
# An upper bound for `S₁` at a general modulus

The asymptotic `GPYSieveS1.main_S1_asymptotic` of `vendor/PrimeGapsLib` needs
`PrimeGaps.ModulusHyp` of its modulus, whose prime factors must be at most `log N`. The
roughness bound applies `S₁` at the modulus `Q p` for primes `p ≤ N^ρ`, so it needs a version
for any modulus `W` divisible by every prime `p ≤ D₀(N)`. An upper bound suffices:

  `S₁ ≤ (N / W) ∑'_{d, e} λ_d λ_e / ∏ᵢ [dᵢ, eᵢ] + (∑_d |λ_d|)²`,

where the CRT count `N / (W ∏ [dᵢ, eᵢ]) + O(1)` is the library's. The primed sum is the
library's `yWeightedSum` in the variables `y = lToY λ`, which we bound absolutely by
`(k² − k) y_max² A^k C^{k² − k}` with `A = ∑_{n ≤ R, (n, W) = 1} μ²(n) / φ(n)`: this is the
library's off-diagonal bound `pair_master` at the scale `N = 0`, where `⌊D₀(0)⌋₊ = 0`
imposes no condition on the coupling variables `s_{ij}`.
-/

namespace Erdos420

open Finset
open scoped ArithmeticFunction.Moebius
open GPYSieveS1 PrimeGaps PrimeGaps.LemS1RestrictSij

open Classical in
/-- `lem_per_pair` for a modulus `W` divisible by every prime `p ≤ D₀(N)`, without
`ModulusHyp`. -/
lemma abs_pairCount_sub_le {k : ℕ} (h : Fin k → ℕ) (hHinj : Function.Injective h) (N W : ℕ)
    (hW : 0 < W) (hWD : primorial ⌊D₀ N⌋₊ ∣ W)
    (hthr : ∀ i j : Fin k, i ≠ j → |(h i : ℝ) - (h j : ℝ)| ≤ D₀ N)
    (v0 : ℕ) (d e : Fin k → ℕ) (hd : ∀ i, 0 < d i) (he : ∀ i, 0 < e i)
    (hdcop : Nat.Coprime (∏ i, d i) W) (hecop : Nat.Coprime (∏ i, e i) W) :
    |(pairCount h N W v0 d e : ℝ) -
        (if (∀ i, 0 < d i) ∧ (∀ i, 0 < e i) ∧ PairwiseCoprimeModuli W (fun i ↦
          Nat.lcm (d i) (e i)) then
              N / (qMod W d e : ℝ) else 0)| ≤ 1 := by
  have hpc : pairCount h N W v0 d e = Scount h N W v0 d e := by
    unfold pairCount Scount
    have h2N : ⌊2 * (N : ℝ)⌋ = (2 * N : ℤ) := by
      rw [show (2 : ℝ) * N = ((2 * N : ℕ) : ℝ) from (Nat.cast_mul 2 N).symm, Int.floor_natCast]
      exact Nat.cast_mul 2 N
    rw [Int.floor_natCast, h2N]
    rfl
  have hqm : (qMod W d e : ℝ) = ((qMod W d e : ℕ) : ℝ) := rfl
  by_cases hcond : (∀ i, 0 < d i) ∧ (∀ i, 0 < e i) ∧ PairwiseCoprimeModuli W (fun i ↦
    Nat.lcm (d i) (e i))
  · rw [ite_eq_left hcond, hpc, hqm]
    exact lem_coprime_branch h N W v0 d e hW hd he hcond.2.2
  · rw [ite_eq_right hcond]
    have hbig : ∀ (i : Fin k) (p : ℕ), Nat.Prime p →
        p ∣ Nat.lcm (d i) (e i) → D₀ N < (p : ℝ) := by
      intro i p hp hpl
      rcases hp.dvd_mul.mp (hpl.trans (Nat.lcm_dvd_mul _ _)) with hpd | hpe
      · exact primeFactor_large N (∏ j, d j) p hWD hdcop hp
          (hpd.trans (Finset.dvd_prod_of_mem d (Finset.mem_univ i)))
      · exact primeFactor_large N (∏ j, e j) p hWD hecop hp
          (hpe.trans (Finset.dvd_prod_of_mem e (Finset.mem_univ i)))
    have hzero : Scount h N W v0 d e = 0 :=
      lem_noncoprime_branch h hHinj N W v0 d e hdcop hecop
        hbig hthr fun hp ↦ hcond ⟨hd, he, hp⟩
    rw [hpc, hzero]
    simp

/-- `⌊D₀(0)⌋₊ = 0`, since `log 0 = 0`. -/
lemma floor_D₀_zero : ⌊D₀ ((0 : ℕ) : ℝ)⌋₊ = 0 := by
  simp [D₀]

/-- The decoupled sum in the variables `y = lToY λ` is at most
`(k² − k) y_max² A^k S₀^{k² − k}`, with `A = sumA W R` and `S₀ = ∑_{n ≤ R} μ²(n) / φ(n)²`. -/
lemma abs_yWeightedSum_le {k : ℕ} (hk : 2 ≤ k) (R : ℝ) (W : ℕ) (lam : (Fin k → ℕ) →₀ ℝ)
    (hlam : lam.HasPermissibleSupport ⌊R⌋₊ W) :
    |yWeightedSum lam| ≤ (k ^ 2 - k : ℕ) * (lToY lam).maxRealAbs ^ 2 *
      MaynardOffDiagonal.sumA W R ^ k * S0fin R ^ (k ^ 2 - k) := by
  classical
  have hW : primorial ⌊D₀ ((0 : ℕ) : ℝ)⌋₊ ∣ W := by
    rw [floor_D₀_zero]
    exact Nat.one_dvd W
  have hsum : yWeightedSum lam = ∑' u : Fin k → ℕ, ∑' s : Fin k → Fin k → ℕ,
      (if ((∀ i, 1 ≤ u i) ∧ (∀ i, s i i = 1) ∧ (∀ i j, i ≠ j → 1 ≤ s i j) ∧
            RestrictedCoprime u s ∧
            (∃ i j : Fin k, i ≠ j ∧ ⌊D₀ ((0 : ℕ) : ℝ)⌋₊ < s i j)) then
          (∏ i, (μ (u i) : ℝ) ^ 2 / (Nat.totient (u i) : ℝ)) *
          (∏ p ∈ (Finset.univ.offDiag : Finset (Fin k × Fin k)),
              (μ (s p.1 p.2) : ℝ) / (Nat.totient (s p.1 p.2) : ℝ) ^ 2) *
          lToY lam (boldA u s) * lToY lam (boldB u s)
        else 0) := by
    refine tsum_congr fun u ↦ tsum_congr fun s ↦ if_congr ?_ rfl rfl
    rw [floor_D₀_zero]
    refine ⟨fun hG ↦ ⟨hG.1, hG.2.1, hG.2.2.1, hG.2.2.2, ⟨0, by omega⟩, ⟨1, by omega⟩,
      by simp [Fin.ext_iff], hG.2.2.1 _ _ (by simp [Fin.ext_iff])⟩, fun hG ↦
        ⟨hG.1, hG.2.1, hG.2.2.1, hG.2.2.2.1⟩⟩
  have hS0 : 0 ≤ S0fin R := Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
  have hSij : Sijfin 0 R ≤ S0fin R := by
    unfold Sijfin S0fin
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      fun _ _ _ ↦ abs_nonneg _
  have hpow : S0fin R ^ (k ^ 2 - k - 1) * S0fin R = S0fin R ^ (k ^ 2 - k) := by
    rw [← pow_succ]
    congr 1
    have : 2 * k ≤ k ^ 2 := by nlinarith
    omega
  have hA : 0 ≤ MaynardOffDiagonal.sumA W R :=
    Finset.sum_nonneg fun _ _ ↦ by positivity
  rw [hsum]
  refine (lem_S1_sij_D0_union 0 R W lam hlam).trans ?_
  have hcard : #(Finset.univ.offDiag : Finset (Fin k × Fin k)) = k ^ 2 - k := by
    rw [Finset.offDiag_card, Finset.card_univ, Fintype.card_fin, sq]
  calc _ ≤ ∑ _p ∈ (Finset.univ.offDiag : Finset (Fin k × Fin k)),
        (lToY lam).maxRealAbs ^ 2 * MaynardOffDiagonal.sumA W R ^ k * S0fin R ^ (k ^ 2 - k) :=
        Finset.sum_le_sum fun p hp ↦ by
          refine (pair_master 0 R W hW lam hlam p.1 p.2 (Finset.mem_offDiag.mp hp).2.2).trans ?_
          rw [← hpow, ← mul_assoc]
          gcongr
    _ = _ := by rw [Finset.sum_const, hcard, nsmul_eq_mul]; ring

open scoped PrimeGaps.sieveTruncation in
/-- **Upper bound for `S₁` at a general modulus.** For every modulus `W` divisible by every
prime `p ≤ D₀(N)` and every `λ` with permissible support at `⌊R⌋₊` and `W`,
`S₁ ≤ C (N / W) y_max² A^k + (C y_max R (log R)^{2k})²`, where `y_max` bounds `lToY λ` and
`A = sumA W R`. -/
theorem exists_S₁_le {k : ℕ} (hk : 2 ≤ k) (h : Fin k → ℕ) (hHinj : Function.Injective h)
    (θ δ : ℝ) (hθ : θ ∈ Set.Ioo (0 : ℝ) 1) (hδ : δ ∈ Set.Ioo (0 : ℝ) (θ / 2)) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ N → ∀ W : ℕ, 0 < W →
      primorial ⌊D₀ N⌋₊ ∣ W → ∀ lam : (Fin k → ℕ) →₀ ℝ, lam.HasPermissibleSupport ⌊R⌋₊ W →
      ∀ w₀ : ZMod W, ∀ Y : ℝ, (lToY lam).maxRealAbs ≤ Y →
        S₁ h lam N w₀ ≤ C * (N / W) * Y ^ 2 * MaynardOffDiagonal.sumA W R ^ k +
          (C * Y * R * Real.log R ^ (2 * k)) ^ 2 := by
  classical
  obtain ⟨Cl1, hCl1, Nl1, hl1⟩ := lem_l1_bound hk θ δ hθ hδ
  obtain ⟨C₂, hC₂, hs0⟩ := s0_factor
  obtain ⟨Nthr, hthr⟩ := exists_thresh h
  refine ⟨max Cl1 ((k ^ 2 - k : ℕ) * C₂ ^ (k ^ 2 - k)) + 1, by positivity, max Nl1 Nthr, ?_⟩
  intro N hN W hW hWD lam hlam w₀ Y hY
  have : NeZero W := ⟨hW.ne'⟩
  set C := max Cl1 ((k ^ 2 - k : ℕ) * C₂ ^ (k ^ 2 - k)) + 1
  have hNl1 : Nl1 ≤ N := le_trans (le_max_left _ _) hN
  obtain ⟨-, hthrN⟩ := hthr N (le_trans (le_max_right _ _) hN)
  have hY0 : 0 ≤ Y := Finsupp.maxRealAbs_nonneg.trans hY
  obtain ⟨D, hD, hS1⟩ := lem_S1_expand_swap h lam N W w₀.val (N ^ (θ / 2 - δ)) hlam
  set mp : (Fin k → ℕ) → (Fin k → ℕ) → ℝ := fun d e ↦
    (if (∀ i, 0 < d i) ∧ (∀ i, 0 < e i) ∧ PairwiseCoprimeModuli W (fun i ↦
      Nat.lcm (d i) (e i)) then
        N / (qMod W d e : ℝ) else 0) with hmp
  have hsplit : S1 h lam N W w₀.val - (N / (W : ℝ)) * primedSum W lam =
        ∑ d ∈ D, ∑ e ∈ D, lam d * lam e *
              ((pairCount h N W w₀.val d e : ℝ) - mp d e) := by
    rw [hS1]
    have hmain : ∑ d ∈ D, ∑ e ∈ D, lam d * lam e * mp d e =
        (N / (W : ℝ)) * primedSum W lam := by
      rw [← lem_main_term lam N W D hD, hmp]
      simp only [mul_ite, mul_zero]
    rw [← hmain, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun d _ ↦ ?_
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun e _ ↦ by ring
  -- the CRT error is at most `(∑ |λ|)²`
  have hcrt : |∑ d ∈ D, ∑ e ∈ D, lam d * lam e *
      ((pairCount h N W w₀.val d e : ℝ) - mp d e)| ≤ (∑ d ∈ D, |lam d|) ^ 2 := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [sq, Finset.sum_mul]
    refine Finset.sum_le_sum fun d _ ↦ (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun e _ ↦ ?_
    rw [abs_mul, abs_mul]
    by_cases hld : lam d = 0
    · simp [hld]
    by_cases hle : lam e = 0
    · simp [hle]
    have hpos : ∀ d, lam d ≠ 0 → ∀ i, 0 < d i :=
      fun d hne i ↦ Nat.one_le_iff_ne_zero.mpr (hlam.ne_zero_of_ne_zero hne i)
    simpa using mul_le_mul_of_nonneg_left
      (abs_pairCount_sub_le h hHinj N W hW hWD hthrN w₀.val d e (hpos d hld) (hpos e hle)
        (hlam.coprime_prod_W_of_ne_zero hld) (hlam.coprime_prod_W_of_ne_zero hle))
      (mul_nonneg (abs_nonneg (lam d)) (abs_nonneg (lam e)))
  have hl1' :
      ∑ d ∈ D, |lam d| ≤ C * Y * N ^ (θ / 2 - δ) * Real.log (N ^ (θ / 2 - δ)) ^ (2 * k) := by
    refine (hl1 N hNl1 W lam hlam D hD).trans ?_
    have hR : 0 ≤ (N : ℝ) ^ (θ / 2 - δ) := by positivity
    have hlogR : 0 ≤ Real.log ((N : ℝ) ^ (θ / 2 - δ)) ^ (2 * k) := by
      rw [pow_mul]
      positivity
    have hCl : Cl1 ≤ C := (le_max_left _ _).trans (le_add_of_nonneg_right zero_le_one)
    have hy : 0 ≤ (lToY lam).maxRealAbs := Finsupp.maxRealAbs_nonneg
    gcongr
  have hmainb : (N / (W : ℝ)) * primedSum W lam ≤
      C * (N / W) * Y ^ 2 * MaynardOffDiagonal.sumA W R ^ k := by
    rw [primedSum_eq_yWeightedSum (N ^ (θ / 2 - δ)) W lam hlam]
    have hA : 0 ≤ MaynardOffDiagonal.sumA W R := Finset.sum_nonneg fun _ _ ↦ by positivity
    have hS0 : S0fin R ^ (k ^ 2 - k) ≤ C₂ ^ (k ^ 2 - k) :=
      pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ ↦ abs_nonneg _) (hs0 _) _
    have hCC : ((k ^ 2 - k : ℕ) : ℝ) * C₂ ^ (k ^ 2 - k) ≤ C :=
      (le_max_right _ _).trans (le_add_of_nonneg_right zero_le_one)
    calc (N / (W : ℝ)) * yWeightedSum lam ≤ (N / (W : ℝ)) * |yWeightedSum lam| :=
          mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity)
      _ ≤ (N / (W : ℝ)) * ((k ^ 2 - k : ℕ) * (lToY lam).maxRealAbs ^ 2 *
            MaynardOffDiagonal.sumA W R ^ k * S0fin R ^ (k ^ 2 - k)) :=
          mul_le_mul_of_nonneg_left (abs_yWeightedSum_le hk _ W lam hlam) (by positivity)
      _ ≤ (N / (W : ℝ)) * ((k ^ 2 - k : ℕ) * Y ^ 2 *
            MaynardOffDiagonal.sumA W R ^ k * C₂ ^ (k ^ 2 - k)) := by
          have hS0' : 0 ≤ S0fin R := Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
          gcongr
          exact Finsupp.maxRealAbs_nonneg
      _ = (((k ^ 2 - k : ℕ) : ℝ) * C₂ ^ (k ^ 2 - k)) * (N / W) * Y ^ 2 *
            MaynardOffDiagonal.sumA W R ^ k := by ring
      _ ≤ C * (N / W) * Y ^ 2 * MaynardOffDiagonal.sumA W R ^ k := by gcongr
  rw [MainProp.S1_eq_gpy]
  have hsq : (∑ d ∈ D, |lam d|) ^ 2 ≤ (C * Y * R * Real.log R ^ (2 * k)) ^ 2 :=
    pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ ↦ abs_nonneg _) hl1' 2
  linarith [(abs_le.mp (hsplit ▸ hcrt)).2]

end Erdos420
