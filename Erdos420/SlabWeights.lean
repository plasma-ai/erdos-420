import Erdos420.Basic
import Erdos420.Covering
import Erdos420.Maynard.Weights
import Erdos420.Sieve.PairCount
import Erdos420.SlabTail

/-!
# Weighted anchors with a small slab tail

Fix `k` and `m`. Take Maynard's tuple `b` for `m`, the holes `k b_i`, and
`B = k ∑ b_i`. For large `X` put `u = log X / (64 log 4)`, so that the
covering modulus `M = coverModulus (r + 3) u` is at most `4^u = X^{1/64}`.
Lift the protected covering residue `z` to `a₀ ≡ z / k (mod M)`, and give the
anchors `A_t = k (a₀ + M t)`, `t ∈ [N, 2N)`, Maynard's weights restricted to
rough `t`.

The slab tail `slabTail k B A_t H`, with `H = ⌈log (8 k X)⌉`, is small on
weighted average. A hole whose detector is composite but rough has
largest-prime ratio at most `X^{-ρ}`. For any other `x = A_t + s` in the slab,
write `x = ℓ p` with `p` its largest prime. If `ℓ > (log X)^3`, the ratio is
below `(log X)^{-3}`. Otherwise `p > u`, so the covering prime that divides `x`
divides `ℓ`, and `ℓ ≥ (log u)^{r+3}`. `Erdos420.exists_card_anchor_pair_le`
counts the anchors with a given `(s, ℓ)`. Summing `1/ℓ` over these pairs, with
the bounded weights and the mass `≫ N / (log X)^r`, gives
`≪ (log log X)^{r+1} (log u)^{-(r+3)} + (log log X)^{r+2} / log X`, since only
`(H + B) / g + 1` offsets are compatible with `g = gcd(ℓ, kM) ≤ ℓ`, and
`∑_{ℓ ≤ (log X)^3} 1/ℓ ≪ log log X`. This tends to zero.
-/

namespace Erdos420

open Filter Finset

open scoped Classical in
/-- Each prime detector `a + b_i > k` gives the prime hole `k (a + b_i)` in `(k a, k a + B]`. -/
lemma card_prime_detectors_le {k r B a : ℕ} {b : Fin r → ℕ} (hk : 1 ≤ k) (hka : k < a)
    (hb : Function.Injective b) (hb₀ : ∀ i, 0 < b i) (hbB : ∀ i, k * b i ≤ B) :
    #{i | (a + b i).Prime} ≤ #{x ∈ Ioc (k * a) (k * a + B) | IsPrimeHole k x} := by
  refine card_le_card_of_injOn (fun i ↦ k * (a + b i)) (fun i hi ↦ ?_) fun i _ j _ h ↦ ?_
  · simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hi
    simp only [coe_filter, mem_Ioc, Set.mem_ofPred_eq]
    have := Nat.mul_le_mul_left k (hb₀ i)
    refine ⟨⟨by rw [mul_add]; omega, by rw [mul_add]; exact Nat.add_le_add_left (hbB i) _⟩,
      a + b i, hi, by omega, rfl⟩
  · exact hb (by simpa [Nat.mul_left_cancel_iff (by omega : 0 < k)] using h)

/-- A residue not coprime to `M` shares a prime with `M`. -/
private lemma exists_prime_dvd_of_not_isCoprime {y : ℤ} {M : ℕ} (h : ¬IsCoprime y M) :
    ∃ q : ℕ, q.Prime ∧ q ∣ M ∧ (q : ℤ) ∣ y := by
  have hg : Int.gcd y M ≠ 1 := fun h' ↦ h (Int.isCoprime_iff_gcd_eq_one.mpr h')
  refine ⟨(Int.gcd y M).minFac, Nat.minFac_prime hg, ?_, ?_⟩
  · exact (Nat.minFac_dvd _).trans (Int.natCast_dvd_natCast.mp (Int.gcd_dvd_right y M))
  · exact (Int.natCast_dvd_natCast.mpr (Nat.minFac_dvd _)).trans (Int.gcd_dvd_left y M)

open scoped Classical in
/-- The weighted slab tail at one scale `X`. The anchors `A_t = k (a₀ + M t)`, `t ∈ [N, 2N)`,
have `X ≤ a₀ + M t`, a residue `k a₀ ≡ z (mod M)` whose shifts `z + s` are covered off the
holes, and weights `W ≤ C_W` supported on `X^ρ`-rough anchors with mass `≥ c_M N / (2 (log X)^r)`.
The cofactor counts and their sum are the bounds `hXP` and `hXtail` at `X`. -/
lemma sum_mul_slabTail_le_at {k r B X M a₀ N : ℕ} {b : Fin r → ℕ} {W : ℕ → ℝ} {z j₀ : ℤ}
    {ρ c CW CP η cM L₀ : ℝ} (hk : 1 ≤ k) (hb₀ : ∀ i, 0 < b i) (hM₁ : 1 ≤ M) (hc₈ : c ≤ 1 / 8)
    (hcρ : c ≤ ρ) (hη : 0 < η) (hCW : 0 ≤ CW) (hL₀ : 0 < L₀)
    (hX : (B + 1) ^ 2 + k + 1 ≤ X)
    (hXL : |Real.log (8 * k)| + B + 8 / η + 2 ≤ Real.log X)
    (hXρ : Real.log X ^ 3 ≤ 1 * (X : ℝ) ^ ρ)
    (hX₄ : Real.log X ^ 4 ≤ 1 / 8 * (X : ℝ) ^ (1 / 2 : ℝ))
    (hMp : ∀ p : ℕ, p.Prime → p ∣ M → L₀ ≤ p ∧ (p : ℝ) ≤ Real.log X)
    (hj₀ : k * a₀ - z = M * j₀)
    (hzC : ∀ s : ℤ, -(2 * Real.log X) ≤ s → s ≤ B → (∀ i, s ≠ k * b i) →
      ¬IsCoprime (z + s) (M : ℤ))
    (hMt : ∀ t ∈ Ico N (2 * N), X ≤ a₀ + M * t)
    (hN : (X : ℝ) ^ (63 / 64 : ℝ) ≤ N)
    (hW₀ : ∀ t, 0 ≤ W t) (hWC : ∀ t ∈ Ico N (2 * N), W t ≤ CW)
    (hWr : ∀ t, W t ≠ 0 → ∀ i, ∀ p : ℕ, p.Prime → p ∣ a₀ + M * t + b i → (X : ℝ) ^ ρ < p)
    (hmass : cM * N / Real.log X ^ r / 2 ≤ ∑ t ∈ Ico N (2 * N), W t)
    (hXP : ∀ M a₀ N ℓ : ℕ, ∀ s : ℤ,
      1 ≤ M → (∀ p : ℕ, p.Prime → p ∣ M → (p : ℝ) ≤ Real.log X) →
      1 ≤ ℓ → (ℓ : ℝ) ≤ Real.log X ^ 3 → |(s : ℝ)| ≤ Real.log X ^ 2 →
      (∀ i, s ≠ k * b i) →
      (((Finset.Ico N (2 * N)).filter fun t ↦
          (∀ i, ∀ p : ℕ, p.Prime → p ∣ a₀ + M * t + b i → (X : ℝ) ^ c < p) ∧
          ∃ p : ℕ, p.Prime ∧ (X : ℝ) ^ c < p ∧
            ((k * (a₀ + M * t) : ℕ) : ℤ) + s = ℓ * p).card : ℝ) ≤
        CP * ((N : ℝ) * Nat.gcd ℓ (k * M) / ℓ + 1) *
            (Real.log (Real.log X) / Real.log X) ^ (r + 1) +
          CP * (X : ℝ) ^ (3 * c))
    (hXtail : ∀ (H Lc n : ℕ) (N : ℝ),
      (H : ℝ) ≤ Real.log X + Real.log (8 * k) + 1 → L₀ ≤ Lc →
      (n : ℝ) ≤ Real.log X ^ 3 → (X : ℝ) ^ (63 / 64 : ℝ) ≤ N →
      CW * max CP 0 * ((H + B) * N * (Real.log (Real.log X) / Real.log X) ^ (r + 1) * (2 / Lc) +
        (N * (Real.log (Real.log X) / Real.log X) ^ (r + 1) + (H + B + 1) *
          ((Real.log (Real.log X) / Real.log X) ^ (r + 1) + (X : ℝ) ^ (3 * c))) *
            (1 + Real.log n)) ≤ η / 2 * (cM / 2) * N / Real.log X ^ r) :
    ∑ t ∈ Ico N (2 * N), W t * slabTail k B (k * (a₀ + M * t)) ⌈Real.log (8 * k * X)⌉₊ ≤
      η * ∑ t ∈ Ico N (2 * N), W t := by
  set L := Real.log X with hL
  set H := ⌈Real.log (8 * k * X)⌉₊ with hH_def
  set T := Ico N (2 * N) with hT
  have hX₁ : (1 : ℝ) ≤ X := by exact_mod_cast (by omega : 1 ≤ X)
  have hX₀ : (0 : ℝ) < X := by linarith only [hX₁]
  have hk₁ : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hL₂ : 2 ≤ L := by
    linarith only [hXL, abs_nonneg (Real.log (8 * k)), Nat.cast_nonneg (α := ℝ) B,
      (by positivity : 0 ≤ 8 / η)]
  -- `H ≤ log X + log (8 k) + 1 ≤ 2 log X`
  have hHL : (H : ℝ) ≤ L + Real.log (8 * k) + 1 := by
    have h₁ : (1 : ℝ) ≤ 8 * k * X :=
      one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (by norm_num) hk₁) hX₁
    have h := Nat.ceil_lt_add_one (Real.log_nonneg h₁)
    have h₂ : Real.log (8 * k * X) = Real.log (8 * k) + L := Real.log_mul (by positivity) hX₀.ne'
    linarith only [h, h₂]
  have hHB : (H : ℝ) + B + 1 ≤ 2 * L := by
    linarith only [hHL, hXL, le_abs_self (Real.log (8 * k)), (by positivity : 0 ≤ 8 / η)]
  -- `log X ≤ (log X)^4 ≤ X^{1/2} / 8 ≤ X / 8`
  have hsqrt : (X : ℝ) ^ (1 / 2 : ℝ) ≤ X := by
    simpa using Real.rpow_le_rpow_of_exponent_le hX₁ (by norm_num : (1 / 2 : ℝ) ≤ 1)
  have hL₄ : L ^ 4 ≤ X / 8 := by linarith only [hX₄, hsqrt]
  have hLL₄ : L ≤ L ^ 4 := le_self_pow₀ (by linarith only [hL₂]) (by norm_num)
  have hL₃₄ : L ^ 3 ≤ L ^ 4 := pow_le_pow_right₀ (by linarith only [hL₂]) (by norm_num)
  have hHX : (H : ℝ) ≤ X / 4 := by linarith only [hHB, hLL₄, hL₄, Nat.cast_nonneg (α := ℝ) B]
  set n := ⌊L ^ 3⌋₊ with hn_def
  set Lc := ⌈L₀⌉₊ with hLc_def
  set S := (Ioc (-(H : ℤ)) B).filter fun s ↦ ∀ i, s ≠ (k : ℤ) * b i with hS
  set g : ℕ → ℕ := fun ℓ ↦ Nat.gcd ℓ (k * M) with hg
  set E := (Real.log L / L) ^ (r + 1) with hE
  set Y := (X : ℝ) ^ (3 * c) with hY
  set CP' := max CP 0 with hCP'
  set K : ℤ → ℕ → ℝ := fun s ℓ ↦ if (g ℓ : ℤ) ∣ (k * a₀ : ℤ) + s then
    CP' * (N * g ℓ / ℓ + 1) * E + CP' * Y else 0 with hK
  have hLc : 1 ≤ Lc := Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr hL₀).ne'
  have hE₀ : 0 ≤ E := by
    have : 0 ≤ Real.log L := Real.log_nonneg (by linarith only [hL₂])
    positivity
  have hXcρ : (X : ℝ) ^ c ≤ (X : ℝ) ^ ρ := Real.rpow_le_rpow_of_exponent_le hX₁ hcρ
  have htail := sum_mul_slabTail_le (k := k) (B := B) (H := H) (T := T) (I := Icc Lc n)
    (S := S) (A := fun t ↦ k * (a₀ + M * t)) (W := W) (C := CW)
    (ε := 2 * (H + B) / L ^ 3)
    (fun t s ℓ ↦ ∃ p : ℕ, p.Prime ∧ (X : ℝ) ^ c < p ∧ ((k * (a₀ + M * t) : ℕ) : ℤ) + s = ℓ * p)
    K hCW hW₀ hWC ?_ ?_
  · have hpair := sum_sum_pair_bound_le hLc (n := n) (S := S) (filter_subset _ _) g
      (fun ℓ ↦ Nat.gcd_pos_of_pos_right _ (Nat.mul_pos (by omega) (by omega)))
      (fun ℓ hℓ ↦ Nat.gcd_le_left _ (by omega)) (k * a₀ : ℤ) (N := (N : ℝ)) (E := E) (Y := Y)
      (C := CP') (by positivity) hE₀ (by positivity) (le_max_right _ _)
    have hfin := hXtail H Lc n N hHL (Nat.le_ceil _) (Nat.floor_le (by positivity)) hN
    -- `2 (H + B) / (log X)^3 ≤ η / 2`
    have hε : 2 * (H + B) / L ^ 3 ≤ η / 2 := by
      have hηL : 8 ≤ η * L := by
        rw [← div_le_iff₀' hη]
        linarith only [hXL, abs_nonneg (Real.log (8 * k)), Nat.cast_nonneg (α := ℝ) B]
      rw [div_le_iff₀ (by positivity)]
      calc 2 * ((H : ℝ) + B) ≤ 4 * L := by linarith only [hHB]
        _ ≤ 4 * L * L := le_mul_of_one_le_right (by linarith only [hL₂]) (by linarith only [hL₂])
        _ ≤ η * L / 2 * L * L := by gcongr; linarith only [hηL]
        _ = η / 2 * L ^ 3 := by ring
    have hsumW : 0 ≤ ∑ t ∈ T, W t := sum_nonneg fun t _ ↦ hW₀ t
    have h₁ : 2 * (H + B) / L ^ 3 * ∑ t ∈ T, W t ≤ η / 2 * ∑ t ∈ T, W t :=
      mul_le_mul_of_nonneg_right hε hsumW
    have h₂ : CW * ∑ s ∈ S, ∑ ℓ ∈ Icc Lc n, K s ℓ / (ℓ : ℝ) ≤
        CW * (CP' * ((H + B) * N * E * (2 / Lc) +
          (N * E + (H + B + 1) * (E + Y)) * (1 + Real.log n))) :=
      mul_le_mul_of_nonneg_left hpair hCW
    have h₃ : η / 2 * (cM / 2) * N / L ^ r ≤ η / 2 * ∑ t ∈ T, W t := by
      rw [show η / 2 * (cM / 2) * N / L ^ r = η / 2 * (cM * N / L ^ r / 2) by ring]
      exact mul_le_mul_of_nonneg_left hmass (by positivity)
    rw [← mul_assoc] at h₂
    linarith only [htail, h₁, h₂, h₃, hfin]
  · -- each weighted anchor has rough detectors and a covered slab
    intro t ht hWt
    have hAX : (X : ℝ) ≤ ((k * (a₀ + M * t) : ℕ) : ℝ) := by
      exact_mod_cast (hMt t ht).trans (Nat.le_mul_of_pos_left _ (by omega))
    have hHA : H ≤ k * (a₀ + M * t) := by
      have h : (H : ℝ) ≤ ((k * (a₀ + M * t) : ℕ) : ℝ) := by linarith only [hHX, hAX, hX₀]
      exact_mod_cast h
    have hka : k < a₀ + M * t := by
      have := hMt t ht
      omega
    refine slabTail_le b (u := L) (L₀ := L₀) hk hka hHA (add_sq_lt_add_one_pow_three ?_) hb₀
      (by positivity) (by linarith only [hXρ]) (hWr t hWt) ?_ ?_ ?_
    · have := hMt t ht
      have := Nat.le_mul_of_pos_left (a₀ + M * t) (by omega : 0 < k)
      omega
    · -- the covering prime of `A + s`
      intro s hs₁ hs₂ hs₃
      have hns := hzC s ?_ (by exact_mod_cast hs₂) hs₃
      · have hA : ¬IsCoprime (((k * (a₀ + M * t) : ℕ) : ℤ) + s) M := by
          intro h
          apply hns
          convert h.add_mul_left_left (-(j₀ + k * t)) using 1
          push_cast
          linear_combination -hj₀
        obtain ⟨q, hq, hqM, hqs⟩ := exists_prime_dvd_of_not_isCoprime hA
        exact ⟨q, hq, (hMp q hq hqM).1, (hMp q hq hqM).2, hqs⟩
      · have h₂ : -(H : ℝ) < s := by exact_mod_cast hs₁
        linarith only [h₂, hHB, Nat.cast_nonneg (α := ℝ) B]
    · -- `(log X)^4 ≤ X / 8`
      calc L * L ^ 3 = L ^ 4 := by ring
        _ < (X : ℝ) - H := by linarith only [hL₄, hHX, hX₀]
        _ ≤ ((k * (a₀ + M * t) : ℕ) : ℝ) - H := by linarith only [hAX]
    · -- `X^c (log X)^3 ≤ X^{1/2} (log X)^4 ≤ X / 8`
      have h₁ : (X : ℝ) ^ c ≤ (X : ℝ) ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hX₁ (by linarith only [hc₈])
      have h₂ : (X : ℝ) ^ (1 / 2 : ℝ) * (X : ℝ) ^ (1 / 2 : ℝ) = X := by
        rw [← Real.rpow_add hX₀]
        norm_num
      calc (X : ℝ) ^ c * L ^ 3 ≤ (X : ℝ) ^ (1 / 2 : ℝ) * (1 / 8 * (X : ℝ) ^ (1 / 2 : ℝ)) := by
            gcongr
            linarith only [hX₄, hL₃₄]
        _ = (X : ℝ) / 8 := by rw [← mul_assoc, mul_comm _ (1 / 8 : ℝ), mul_assoc, h₂]; ring
        _ < (X : ℝ) - H := by linarith only [hHX, hX₀]
        _ ≤ ((k * (a₀ + M * t) : ℕ) : ℝ) - H := by linarith only [hAX]
  · -- the cofactor counts vanish unless `gcd(ℓ, k M) ∣ k a₀ + s`
    intro s hs ℓ hℓ
    rw [hS, mem_filter, mem_Ioc] at hs
    rw [mem_Icc] at hℓ
    have hℓ₁ : 1 ≤ ℓ := hLc.trans hℓ.1
    simp only [hK]
    split_ifs with hdiv
    · have hℓL : (ℓ : ℝ) ≤ L ^ 3 :=
        (Nat.cast_le.mpr hℓ.2).trans (Nat.floor_le (by positivity))
      have hsL : |(s : ℝ)| ≤ L ^ 2 := by
        have h₁ : -(H : ℝ) < s := by exact_mod_cast hs.1.1
        have h₂ : (s : ℝ) ≤ B := by exact_mod_cast hs.1.2
        have h₃ : 2 * L ≤ L ^ 2 := by
          rw [sq]
          exact mul_le_mul_of_nonneg_right hL₂ (by linarith only [hL₂])
        rw [abs_le]
        constructor <;> linarith only [h₁, h₂, h₃, hHB, Nat.cast_nonneg (α := ℝ) H,
          Nat.cast_nonneg (α := ℝ) B]
      have hpc := hXP M a₀ N ℓ s hM₁ (fun p hp hpM ↦ (hMp p hp hpM).2) hℓ₁ hℓL hsL hs.2
      have hsub : {t ∈ T | W t ≠ 0 ∧ ∃ p : ℕ, p.Prime ∧ (X : ℝ) ^ c < p ∧
          ((k * (a₀ + M * t) : ℕ) : ℤ) + s = ℓ * p} ⊆
          {t ∈ T | (∀ i, ∀ p : ℕ, p.Prime → p ∣ a₀ + M * t + b i → (X : ℝ) ^ c < p) ∧
            ∃ p : ℕ, p.Prime ∧ (X : ℝ) ^ c < p ∧
              ((k * (a₀ + M * t) : ℕ) : ℤ) + s = ℓ * p} := by
        intro t ht
        rw [mem_filter] at ht ⊢
        exact ⟨ht.1, fun i p hp hpd ↦ hXcρ.trans_lt (hWr t ht.2.1 i p hp hpd), ht.2.2⟩
      calc (#{t ∈ T | W t ≠ 0 ∧ ∃ p : ℕ, p.Prime ∧ (X : ℝ) ^ c < p ∧
            ((k * (a₀ + M * t) : ℕ) : ℤ) + s = ℓ * p} : ℝ)
          ≤ CP * ((N : ℝ) * g ℓ / ℓ + 1) * E + CP * Y :=
            (Nat.cast_le.mpr (card_le_card hsub)).trans hpc
        _ ≤ CP' * ((N : ℝ) * g ℓ / ℓ + 1) * E + CP' * Y := by
            gcongr <;> exact le_max_left _ _
    · rw [Nat.cast_nonpos, card_eq_zero, filter_eq_empty_iff]
      rintro t - ⟨-, p, -, -, hp⟩
      apply hdiv
      have h₁ : (g ℓ : ℤ) ∣ ℓ * p :=
        Dvd.dvd.mul_right (Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_left _ _)) _
      have h₂ : (g ℓ : ℤ) ∣ ((k * M : ℕ) : ℤ) * t :=
        Dvd.dvd.mul_right (Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_right _ _)) _
      convert dvd_sub h₁ h₂ using 1
      rw [← hp]
      push_cast
      ring

open scoped Classical in
/-- For large `X` there are injective anchors `A_t ∈ [X, 8 k X]` and bounded weights,
of mass at least `√X`, with a prime-hole surplus `γ` over `m − 1` in `(A_t, A_t + B]`
and an arbitrarily small weighted slab tail. -/
theorem exists_slab_weights (k m : ℕ) (hk : 1 ≤ k) :
    ∃ B : ℕ, ∃ γ > (0 : ℝ), ∃ C : ℝ, ∀ η > (0 : ℝ), ∀ᶠ X : ℕ in atTop,
      ∃ (T : Finset ℕ) (A : ℕ → ℕ) (W : ℕ → ℝ),
        Set.InjOn A T ∧ (∀ t ∈ T, X ≤ A t ∧ A t ≤ 8 * k * X) ∧
        (∀ t, 0 ≤ W t) ∧ (∀ t ∈ T, W t ≤ C) ∧ Real.sqrt X ≤ ∑ t ∈ T, W t ∧
        γ * ∑ t ∈ T, W t ≤ ∑ t ∈ T, W t *
          ((((Ioc (A t) (A t + B)).filter (IsPrimeHole k)).card : ℝ) - (m - 1)) ∧
        ∑ t ∈ T, W t * slabTail k B (A t) ⌈Real.log (8 * k * X)⌉₊ ≤
          η * ∑ t ∈ T, W t := by
  obtain ⟨r, b, γM, cM, hb, hb₀, hγM, hcM, hMay⟩ := exists_maynard_weights m
  -- the holes `k b_i` lie in `(0, B]`
  set B := k * ∑ i, b i with hB
  have hbB : ∀ i, k * b i ≤ B := fun i ↦
    Nat.mul_le_mul_left k (single_le_sum (fun j _ ↦ Nat.zero_le (b j)) (mem_univ i))
  -- Maynard's weights, with non-rough mass `ηM ≤ γM / (2 (r + 1))`
  set ηM := min (1 / 2) (γM / (2 * (r + 1))) with hηM
  have hηM₀ : 0 < ηM := lt_min (by norm_num) (by positivity)
  obtain ⟨ρ, hρ, CM, hMay⟩ := hMay ηM hηM₀
  refine ⟨B, γM / 2, by positivity, max CM 0, fun η hη ↦ ?_⟩
  -- the cofactor counts, at roughness `X^c` with `c ≤ ρ`
  set c := min (ρ / 2) (1 / 8) with hc
  have hc₀ : 0 < c := lt_min (by positivity) (by norm_num)
  have hcρ : c ≤ ρ := (min_le_left _ _).trans (by linarith)
  have hc₈ : c ≤ 1 / 8 := min_le_right _ _
  obtain ⟨CP, hCP⟩ := exists_card_anchor_pair_le k r 3 hk b hb hc₀ (by linarith)
  -- the protected covering, at `u = log X / (64 log 4)`
  have hcov := eventually_exists_protected_cover (univ.image fun i ↦ k * b i)
    (by simpa using fun i ↦ Nat.mul_pos hk (hb₀ i)) B (by simpa using hbB) (a := r + 3)
    (by omega) (128 * Real.log 4)
  have hu : Tendsto (fun X : ℕ ↦ Real.log X / (64 * Real.log 4)) atTop atTop :=
    tendsto_log_natCast_atTop.atTop_div_const (by positivity)
  filter_upwards [hu.eventually hcov, hMay, hCP,
    eventually_pair_sum_le k r B (K := max CM 0 * max CP 0) (c₁ := η / 2 * (cM / 2))
      (by positivity) (by positivity) hc₀ hc₈,
    tendsto_log_cover_atTop.eventually_ge_atTop (k + 1 : ℝ),
    tendsto_log_natCast_atTop.eventually_ge_atTop (|Real.log (8 * k)| + B + 8 / η + 2),
    tendsto_natCast_atTop_atTop.eventually (eventually_log_pow_le_mul_rpow 3 hρ one_pos),
    tendsto_natCast_atTop_atTop.eventually
      (eventually_log_pow_le_mul_rpow 4 (δ := 1 / 2) (ε := 1 / 8) (by norm_num) (by norm_num)),
    tendsto_natCast_atTop_atTop.eventually
      (eventually_log_pow_le_mul_rpow r (δ := 31 / 64) (ε := cM / 2) (by norm_num) (by positivity)),
    eventually_ge_atTop ((B + 1) ^ 2 + k + 1)]
    with X hXcov hXM hXP hXtail hXu hXL hXρ hX₄ hXr hX
  set L := Real.log X with hL
  set u := L / (64 * Real.log 4) with hu_def
  set M := coverModulus (r + 3) u with hM_def
  have hX₁ : (1 : ℝ) ≤ X := by exact_mod_cast (by omega : 1 ≤ X)
  have hX₀ : (0 : ℝ) < X := by linarith
  have hk₁ : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hL₂ : 2 ≤ L := by
    linarith [abs_nonneg (Real.log (8 * k)), (by positivity : 0 ≤ 8 / η)]
  have hu₀ : 0 ≤ u := by positivity
  have huL : u ≤ L := div_le_self (by linarith) one_lt_sixtyFour_mul_log_four.le
  -- the covering modulus `M ≤ 4^u = X^{1/64}` has its primes in `[(log u)^{r+3}, u]`
  have h4u : (4 : ℝ) ^ u = (X : ℝ) ^ (1 / 64 : ℝ) := by
    rw [Real.rpow_def_of_pos (by norm_num), Real.rpow_def_of_pos hX₀]
    congr 1
    simp only [u, L]
    field_simp
  have hMX : (M : ℝ) ≤ (X : ℝ) ^ (1 / 64 : ℝ) := (coverModulus_le _ hu₀).trans h4u.le
  have hM₁ : 1 ≤ M := coverModulus_pos _ _
  have hMX' : M ≤ X := by
    have h : (M : ℝ) ≤ X := hMX.trans
      (by simpa using Real.rpow_le_rpow_of_exponent_le hX₁ (by norm_num : (1 / 64 : ℝ) ≤ 1))
    exact_mod_cast h
  have hMp : ∀ p : ℕ, p.Prime → p ∣ M → Real.log u ^ (r + 3) ≤ p ∧ (p : ℝ) ≤ u :=
    fun p hp hpM ↦ le_of_prime_dvd_coverModulus hu₀ hp hpM
  have hlogu : (k : ℝ) < Real.log u ^ (r + 3) := by
    have h : Real.log u ≤ Real.log u ^ (r + 3) := le_self_pow₀ (by linarith) (by omega)
    linarith
  have hkM : k.Coprime M := coprime_of_forall_prime_dvd_lt hk fun p hp hpM ↦ by
    exact_mod_cast hlogu.trans_le (hMp p hp hpM).1
  -- lift the covering residue to `a₀ < M` with `k a₀ ≡ z`
  obtain ⟨z, hzH, hzC⟩ := hXcov
  obtain ⟨a₀, ha₀, j₀, hj₀⟩ := exists_lt_dvd_mul_sub hkM hM₁ z
  set N := X / M + 1 with hN_def
  have hMN₁ : X ≤ M * N := (Nat.lt_mul_div_succ X hM₁).le
  have hMN₂ : M * N ≤ 2 * X := by
    rw [hN_def, mul_add, mul_one]
    linarith [Nat.mul_div_le X M]
  have hN : (X : ℝ) ^ (63 / 64 : ℝ) ≤ N := by
    have h₁ : (X : ℝ) ^ (63 / 64 : ℝ) * (X : ℝ) ^ (1 / 64 : ℝ) = X := by
      rw [← Real.rpow_add hX₀]
      norm_num
    have h₂ : (X : ℝ) ≤ M * N := by exact_mod_cast hMN₁
    refine le_of_mul_le_mul_right ?_ (by positivity : (0 : ℝ) < (X : ℝ) ^ (1 / 64 : ℝ))
    rw [h₁, mul_comm (N : ℝ)]
    exact h₂.trans (mul_le_mul_of_nonneg_right hMX (Nat.cast_nonneg _))
  -- the detectors `a₀ + b_i` are coprime to `M`
  have hdet : ∀ i, (a₀ + b i).Coprime M := by
    intro i
    have h₁ := (hzH (k * b i) (mem_image_of_mem _ (mem_univ i))).add_mul_left_left j₀
    have h₂ : IsCoprime ((k : ℤ) * (a₀ + b i)) M := by
      convert h₁ using 1
      push_cast
      linarith
    exact Nat.isCoprime_iff_coprime.mp (by exact_mod_cast h₂.of_mul_left_right)
  -- `M ∣ primorial ⌊u⌋` is squarefree, with prime factors `≤ u ≤ log X / 2`
  have hMsq : Squarefree M := Squarefree.squarefree_of_dvd
    (prod_dvd_prod_of_subset _ _ _ fun q hq ↦ by
      rw [Nat.range_succ_eq_Iic]
      simp only [mem_filter] at hq ⊢
      exact ⟨hq.1, hq.2.1⟩) (squarefree_primorial ⌊u⌋₊)
  have hu₂ : u ≤ L / 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 4)
    exact div_le_div_of_nonneg_left (by linarith) (by norm_num) (by linarith)
  obtain ⟨W₀, hW₀, hsur, hmass, hWC, hnr⟩ := hXM M a₀ N hM₁ hMX hMsq
    (fun p hp hpM ↦ (hMp p hp hpM).2.trans hu₂) ha₀ hMN₁ hMN₂ hdet
  -- keep Maynard's weights on the `X^ρ`-rough anchors
  set rough : ℕ → Prop := fun t ↦
    ∀ i, ∀ p : ℕ, p.Prime → p ∣ a₀ + M * t + b i → (X : ℝ) ^ ρ < p with hrough
  set T := Ico N (2 * N) with hT
  set W : ℕ → ℝ := fun t ↦ if rough t then W₀ t else 0 with hW
  have hW₀' : ∀ t, 0 ≤ W t := fun t ↦ by
    simp only [hW]
    split_ifs
    exacts [hW₀ t, le_rfl]
  have hWC' : ∀ t ∈ T, W t ≤ max CM 0 := fun t _ ↦ by
    simp only [hW]
    split_ifs with h
    exacts [(hWC t h).trans (le_max_left _ _), le_max_right _ _]
  -- every anchor lies in `[X, 8 k X]`, with detectors above `k`
  have hMt : ∀ t ∈ T, X ≤ a₀ + M * t ∧ a₀ + M * t ≤ 4 * X := by
    intro t ht
    rw [mem_Ico] at ht
    have h₁ : M * N ≤ M * t := Nat.mul_le_mul_left M ht.1
    have h₂ : M * (t + 1) ≤ M * (2 * N) := Nat.mul_le_mul_left M ht.2
    rw [mul_add, mul_one, show M * (2 * N) = 2 * (M * N) by ring] at h₂
    constructor <;> omega
  have hka : ∀ t ∈ T, k < a₀ + M * t := fun t ht ↦ by have := (hMt t ht).1; omega
  -- the non-rough anchors carry at most `ηM ∑ W₀`
  have hsplit : ∀ f : ℕ → ℝ, ∑ t ∈ T, W₀ t * f t =
      ∑ t ∈ T, W t * f t + ∑ t ∈ T with ¬rough t, W₀ t * f t := by
    intro f
    rw [← sum_filter_add_sum_filter_not T rough (fun t ↦ W₀ t * f t), sum_filter]
    congr 1
    refine sum_congr rfl fun t _ ↦ ?_
    simp only [hW]
    split_ifs <;> simp
  have hnr' : ∑ t ∈ T with ¬rough t, W₀ t ≤ ηM * ∑ t ∈ T, W₀ t := by
    refine le_trans (le_of_eq (sum_congr (filter_congr fun t _ ↦ ?_) fun _ _ ↦ rfl)) hnr
    simp only [hrough]
    push Not
    rfl
  have hW₀W : ∑ t ∈ T, W₀ t = ∑ t ∈ T, W t + ∑ t ∈ T with ¬rough t, W₀ t := by
    simpa using hsplit fun _ ↦ 1
  have hnr₀ : 0 ≤ ∑ t ∈ T with ¬rough t, W₀ t := sum_nonneg fun t _ ↦ hW₀ t
  have hηM₂ : ηM ≤ 1 / 2 := min_le_left _ _
  have hsumW₀ : 0 ≤ ∑ t ∈ T, W₀ t := sum_nonneg fun t _ ↦ hW₀ t
  have hmassW : (∑ t ∈ T, W₀ t) / 2 ≤ ∑ t ∈ T, W t := by
    have h := mul_le_mul_of_nonneg_right hηM₂ hsumW₀
    linarith only [h, hW₀W, hnr']
  -- the mass is `≥ cM N / (2 (log X)^r)`
  have hLr : 0 < L ^ r := by positivity
  have hmass' : cM * N / L ^ r / 2 ≤ ∑ t ∈ T, W t := by linarith only [hmass, hmassW]
  refine ⟨T, fun t ↦ k * (a₀ + M * t), W, ?_, ?_, hW₀', hWC', ?_, ?_, ?_⟩
  · -- injectivity
    intro t _ t' _ h
    have h₁ := Nat.eq_of_mul_eq_mul_left (by omega : 0 < k) h
    exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < M) (by omega)
  · -- range
    intro t ht
    have h := hMt t ht
    constructor
    · exact h.1.trans (Nat.le_mul_of_pos_left _ (by omega))
    · calc k * (a₀ + M * t) ≤ k * (4 * X) := Nat.mul_le_mul_left k h.2
        _ ≤ 8 * k * X := by
          rw [show k * (4 * X) = 4 * (k * X) by ring, show 8 * k * X = 8 * (k * X) by ring]
          omega
  · -- mass
    have h₁ : (X : ℝ) ^ (1 / 2 : ℝ) * (X : ℝ) ^ (31 / 64 : ℝ) = (X : ℝ) ^ (63 / 64 : ℝ) := by
      rw [← Real.rpow_add hX₀]
      norm_num
    have h₂ : Real.sqrt X * L ^ r ≤ cM / 2 * N := by
      rw [Real.sqrt_eq_rpow]
      calc (X : ℝ) ^ (1 / 2 : ℝ) * L ^ r
          ≤ (X : ℝ) ^ (1 / 2 : ℝ) * (cM / 2 * X ^ (31 / 64 : ℝ)) := by gcongr
        _ = cM / 2 * (X : ℝ) ^ (63 / 64 : ℝ) := by rw [← h₁]; ring
        _ ≤ cM / 2 * N := by gcongr
    have h₃ : Real.sqrt X ≤ cM * N / L ^ r / 2 := by
      rw [div_div, le_div_iff₀ (by positivity)]
      linarith only [h₂]
    linarith only [h₃, hmass']
  · -- the prime-hole surplus
    set f : ℕ → ℝ := fun t ↦ (#{i | (a₀ + M * t + b i).Prime} : ℝ) - (m - 1) with hf
    have hfr : ∀ t, f t ≤ r + 1 := by
      intro t
      have h₁ : #{i | (a₀ + M * t + b i).Prime} ≤ r := (card_filter_le _ _).trans (by simp)
      have h₂ : (#{i | (a₀ + M * t + b i).Prime} : ℝ) ≤ r := by exact_mod_cast h₁
      have h₃ : (0 : ℝ) ≤ m := by positivity
      simp only [hf]
      linarith
    have hnrf : ∑ t ∈ T with ¬rough t, W₀ t * f t ≤ (r + 1) * (ηM * ∑ t ∈ T, W₀ t) := by
      calc ∑ t ∈ T with ¬rough t, W₀ t * f t ≤ ∑ t ∈ T with ¬rough t, W₀ t * (r + 1) :=
            sum_le_sum fun t _ ↦ mul_le_mul_of_nonneg_left (hfr t) (hW₀ t)
        _ = (r + 1) * ∑ t ∈ T with ¬rough t, W₀ t := by rw [← sum_mul, mul_comm]
        _ ≤ (r + 1) * (ηM * ∑ t ∈ T, W₀ t) := by gcongr
    have hηr : (r + 1) * ηM ≤ γM / 2 := by
      calc (r + 1) * ηM ≤ (r + 1) * (γM / (2 * (r + 1))) := by gcongr; exact min_le_right _ _
        _ = γM / 2 := by field_simp
    have hWf : ∑ t ∈ T, W t * f t ≤ ∑ t ∈ T, W t *
        ((#((Ioc (k * (a₀ + M * t)) (k * (a₀ + M * t) + B)).filter (IsPrimeHole k)) : ℝ) -
          (m - 1)) := by
      refine sum_le_sum fun t ht ↦ mul_le_mul_of_nonneg_left ?_ (hW₀' t)
      simp only [hf]
      gcongr
      exact card_prime_detectors_le hk (by have := hka t ht; omega) hb hb₀ hbB
    have h₁ := hsplit f
    have h₂ : γM / 2 * ∑ t ∈ T, W t ≤ γM / 2 * ∑ t ∈ T, W₀ t :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have h₃ := mul_le_mul_of_nonneg_right hηr hsumW₀
    linarith only [h₁, h₂, h₃, hsur, hnrf, hWf, hW₀W, hnr₀]
  · -- the slab tail
    refine sum_mul_slabTail_le_at hk hb₀ hM₁ hc₈ hcρ hη (le_max_right _ _)
      (by linarith only [hlogu, hk₁]) hX hXL hXρ hX₄
      (fun p hp hpM ↦ ⟨(hMp p hp hpM).1, (hMp p hp hpM).2.trans huL⟩) hj₀ ?_
      (fun t ht ↦ (hMt t ht).1) hN hW₀' hWC' ?_ hmass' hXP hXtail
    · intro s hs₁ hs₂ hs₃
      have h₁ : 128 * Real.log 4 * u = 2 * L := by
        simp only [u]
        field_simp
        ring
      refine hzC s (by rwa [h₁]) hs₂ ?_
      intro h hh
      obtain ⟨i, _, rfl⟩ := mem_image.mp hh
      push_cast
      exact hs₃ i
    · intro t hWt
      by_contra h
      exact hWt (ite_eq_right h)

end Erdos420
