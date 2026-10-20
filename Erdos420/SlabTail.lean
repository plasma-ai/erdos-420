module

public import Erdos420.Basic
public import Erdos420.Covering
public import Mathlib.NumberTheory.Harmonic.Bounds
public import Mathlib.NumberTheory.Primorial

/-!
# Bookkeeping for the slab tail

Arithmetic lemmas behind `Erdos420.exists_slab_weights`.

* The covering modulus `M = coverModulus a u` is positive, at most `4^u`, and
  its primes lie in `[(log u)^a, u]`.
* A residue `z` modulo `M` lifts to `a₀ < M` with `k a₀ ≡ z`, when `k` is
  coprime to `M`.
* At most two primes `p ∣ x` have `p² > A`, when `x² < (A + 1)^3`. Each of
  them contributes `p / x = 1 / ℓ` with `ℓ = x / p`, so `bigPrimeRatio A x` is
  at most `2 / Λ` plus the `1 / ℓ` with `ℓ ≤ Λ`.
* For an anchor `A = k a` whose detectors `a + b_i` are rough and whose slab is
  covered off the holes, a hole `k (a + b_i)` with composite detector has every
  cofactor above `Λ`. Off the holes, a cofactor `ℓ ≤ Λ` of `A + s = ℓ p` has
  `p > u`, so the covering prime of `A + s` divides `ℓ` and `ℓ ≥ (log u)^a`.
  Such pairs `(s, ℓ)` are counted by `Erdos420.exists_card_anchor_pair_le`.
* Summed over the weighted anchors, the offsets, and the cofactors, the pair counts
  give `(H + B) N E / L + (N E + (H + B + 1)(E + Y)) log n`: only `(H + B) / g + 1`
  offsets are compatible with `g = gcd(ℓ, kM) ≤ ℓ`.
* This is `o(N / (log X)^r)` for `E = (log log X / log X)^{r+1}`,
  `L ≥ (log u)^{r+3}`, `n ≤ (log X)^3`, `Y = X^{3c}`, and `N ≥ X^{63/64}`.
-/

@[expose] public section

namespace Erdos420

open Finset

/-! ### The covering modulus -/

/-- The covering modulus is positive. -/
lemma coverModulus_pos (a : ℕ) (u : ℝ) : 0 < coverModulus a u :=
  prod_pos fun _ hq ↦ (mem_filter.mp hq).2.1.pos

/-- Every prime of the covering modulus lies in `[(log u)^a, u]`. -/
lemma le_of_prime_dvd_coverModulus {a : ℕ} {u : ℝ} (hu : 0 ≤ u) {p : ℕ} (hp : p.Prime)
    (hpM : p ∣ coverModulus a u) : Real.log u ^ a ≤ p ∧ (p : ℝ) ≤ u := by
  obtain ⟨q, hq, hpq⟩ := (Prime.dvd_finsetProd_iff hp.prime _).mp hpM
  simp only [mem_filter, mem_Iic] at hq
  rw [(Nat.prime_dvd_prime_iff_eq hp hq.2.1).mp hpq]
  exact ⟨hq.2.2, (Nat.cast_le.mpr hq.1).trans (Nat.floor_le hu)⟩

/-- The covering modulus is at most the primorial of `u`, so at most `4^u`. -/
lemma coverModulus_le (a : ℕ) {u : ℝ} (hu : 0 ≤ u) : (coverModulus a u : ℝ) ≤ 4 ^ u := by
  have h₁ : coverModulus a u ≤ primorial ⌊u⌋₊ := by
    refine prod_le_prod_of_subset_of_one_le (fun q hq ↦ ?_) fun q hq _ ↦ ?_
    · simp only [mem_filter, mem_Iic] at hq
      simp only [mem_filter, mem_range]
      exact ⟨by omega, hq.2.1⟩
    · exact (mem_filter.mp hq).2.one_lt.le
  calc (coverModulus a u : ℝ) ≤ ((4 ^ ⌊u⌋₊ : ℕ) : ℝ) := by
        exact_mod_cast h₁.trans (primorial_le_four_pow _)
    _ = (4 : ℝ) ^ (⌊u⌋₊ : ℝ) := by push_cast; rw [Real.rpow_natCast]
    _ ≤ 4 ^ u := Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.floor_le hu)

/-- `k` is coprime to `M` when every prime of `M` exceeds `k`. -/
lemma coprime_of_forall_prime_dvd_lt {k M : ℕ} (hk : 1 ≤ k) (h : ∀ p : ℕ, p.Prime → p ∣ M → k < p) :
    k.Coprime M :=
  (Nat.coprime_of_dvd fun p hp hpM hpk ↦ absurd (Nat.le_of_dvd (by omega) hpk)
    (not_le.mpr (h p hp hpM))).symm

/-- A residue `z` lifts to `a₀ < M` with `k a₀ ≡ z (mod M)`. -/
lemma exists_lt_dvd_mul_sub {k M : ℕ} (hkM : k.Coprime M) (hM : 1 ≤ M) (z : ℤ) :
    ∃ a₀ < M, (M : ℤ) ∣ k * a₀ - z := by
  have : NeZero M := ⟨by omega⟩
  refine ⟨((z : ZMod M) * (k : ZMod M)⁻¹).val, ZMod.val_lt _, ?_⟩
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [ZMod.natCast_zmod_val, mul_left_comm, ZMod.coe_mul_inv_eq_one k hkM, mul_one, sub_self]

/-! ### Large-prime ratios -/

/-- `(A + B)² < (A + 1)³` once `A ≥ (B + 1)²`. -/
lemma add_sq_lt_add_one_pow_three {A B : ℕ} (hA : (B + 1) ^ 2 ≤ A) : (A + B) ^ 2 < (A + 1) ^ 3 :=
  calc (A + B) ^ 2 < ((A + 1) * (B + 1)) ^ 2 := Nat.pow_lt_pow_left (by nlinarith) (by norm_num)
    _ = (A + 1) ^ 2 * (B + 1) ^ 2 := by ring
    _ ≤ (A + 1) ^ 2 * (A + 1) := by gcongr; omega
    _ = (A + 1) ^ 3 := by ring

/-- At most two primes `p ∣ x` have `p² > A`, when `x² < (A + 1)^3`. -/
private lemma card_filter_primeFactors_le_two {A x : ℕ} (hx : x ^ 2 < (A + 1) ^ 3) :
    #{p ∈ x.primeFactors | A < p ^ 2} ≤ 2 := by
  by_contra! h
  have hx₀ : x ≠ 0 := by
    rintro rfl
    simp at h
  have h₁ : ∏ p ∈ x.primeFactors with A < p ^ 2, p ∣ x :=
    (prod_dvd_prod_of_subset _ _ _ (filter_subset _ _)).trans (Nat.prod_primeFactors_dvd x)
  have h₂ : (A + 1) ^ #{p ∈ x.primeFactors | A < p ^ 2} ≤
      ∏ p ∈ x.primeFactors with A < p ^ 2, p ^ 2 :=
    pow_card_le_prod _ _ _ fun p hp ↦ (mem_filter.mp hp).2
  have h₃ : (A + 1) ^ 3 ≤ (A + 1) ^ #{p ∈ x.primeFactors | A < p ^ 2} :=
    Nat.pow_le_pow_right (by omega) h
  rw [prod_pow] at h₂
  have h₄ := Nat.pow_le_pow_left (Nat.le_of_dvd (Nat.pos_of_ne_zero hx₀) h₁) 2
  omega

/-- `bigPrimeRatio A x` is at most `2 / Λ` plus `∑ 1 / ℓ` over the cofactors `ℓ = x / p`
with `ℓ ≤ Λ`, provided each such `ℓ` lies in `I` and satisfies `Q`. -/
lemma bigPrimeRatio_le {A x : ℕ} {Λ : ℝ} (hΛ : 0 < Λ) (hx : x ^ 2 < (A + 1) ^ 3)
    (I : Finset ℕ) (Q : ℕ → Prop) [DecidablePred Q]
    (h : ∀ p ∈ x.primeFactors, A < p ^ 2 → ((x / p : ℕ) : ℝ) ≤ Λ → x / p ∈ I ∧ Q (x / p)) :
    bigPrimeRatio A x ≤ 2 / Λ + ∑ ℓ ∈ I, if Q ℓ then 1 / (ℓ : ℝ) else 0 := by
  -- each term is `p / x = 1 / (x / p)`
  have hterm : ∀ p ∈ x.primeFactors, (p : ℝ) / x = 1 / ((x / p : ℕ) : ℝ) := by
    intro p hp
    have hp' := Nat.mem_primeFactors.mp hp
    rw [Nat.cast_div hp'.2.1 (by exact_mod_cast hp'.1.ne_zero), one_div_div]
  unfold bigPrimeRatio
  rw [← sum_filter_add_sum_filter_not _ fun p ↦ Λ < ((x / p : ℕ) : ℝ)]
  gcongr ?_ + ?_
  · -- at most two terms, each below `1 / Λ`
    calc ∑ p ∈ {p ∈ x.primeFactors | A < p ^ 2} with Λ < ((x / p : ℕ) : ℝ), (p : ℝ) / x
        ≤ ∑ p ∈ {p ∈ x.primeFactors | A < p ^ 2} with Λ < ((x / p : ℕ) : ℝ), 1 / Λ := by
          refine sum_le_sum fun p hp ↦ ?_
          simp only [mem_filter] at hp
          rw [hterm p hp.1.1]
          exact one_div_le_one_div_of_le hΛ hp.2.le
      _ ≤ 2 / Λ := by
          rw [sum_const, nsmul_eq_mul, mul_one_div]
          gcongr
          exact_mod_cast (card_filter_le _ _).trans (card_filter_primeFactors_le_two hx)
  · -- the cofactors `ℓ ≤ Λ` are distinct and lie in `I` with `Q`
    rw [← sum_filter]
    have hinj : Set.InjOn (fun p ↦ x / p)
        ↑{p ∈ {p ∈ x.primeFactors | A < p ^ 2} | ¬Λ < ((x / p : ℕ) : ℝ)} := by
      intro p hp q hq hpq
      simp only [mem_coe, mem_filter, Nat.mem_primeFactors] at hp hq
      simp only at hpq
      rw [← Nat.div_div_self hp.1.1.2.1 hp.1.1.2.2, hpq, Nat.div_div_self hq.1.1.2.1 hq.1.1.2.2]
    calc ∑ p ∈ {p ∈ x.primeFactors | A < p ^ 2} with ¬Λ < ((x / p : ℕ) : ℝ), (p : ℝ) / x
        = ∑ ℓ ∈ image (fun p ↦ x / p)
            {p ∈ {p ∈ x.primeFactors | A < p ^ 2} | ¬Λ < ((x / p : ℕ) : ℝ)}, 1 / (ℓ : ℝ) := by
          rw [sum_image hinj]
          exact sum_congr rfl fun p hp ↦ hterm p (mem_filter.mp (mem_filter.mp hp).1).1
      _ ≤ ∑ ℓ ∈ I with Q ℓ, 1 / (ℓ : ℝ) := by
          refine sum_le_sum_of_subset_of_nonneg (fun ℓ hℓ ↦ ?_) fun _ _ _ ↦ by positivity
          obtain ⟨p, hp, rfl⟩ := mem_image.mp hℓ
          simp only [mem_filter] at hp
          exact mem_filter.mpr (h p hp.1.1 hp.1.2 (not_lt.mp hp.2))

/-! ### The slab of one anchor -/

open scoped Classical in
/-- The slab tail of an anchor `A = k a` with `R`-rough detectors `a + b_i`, whose slab is
covered off the holes by primes in `[L₀, u]`, is at most `2 (H + B) / Λ` plus `∑ 1 / ℓ` over
the non-hole offsets `s` and the cofactors `L₀ ≤ ℓ ≤ Λ` with `A + s = ℓ p`, `p > Z` prime. -/
lemma slabTail_le {k r B H a : ℕ} (b : Fin r → ℕ) {Λ R u Z L₀ : ℝ} (hk : 1 ≤ k) (hka : k < a)
    (hH : H ≤ k * a) (hB : (k * a + B) ^ 2 < (k * a + 1) ^ 3) (hb₀ : ∀ i, 0 < b i)
    (hΛ : 0 < Λ) (hΛR : Λ ≤ R) (hrough : ∀ i, ∀ p : ℕ, p.Prime → p ∣ a + b i → R < p)
    (hcov : ∀ s : ℤ, -(H : ℤ) < s → s ≤ B → (∀ i, s ≠ k * b i) →
      ∃ q : ℕ, q.Prime ∧ L₀ ≤ q ∧ (q : ℝ) ≤ u ∧ (q : ℤ) ∣ ((k * a : ℕ) : ℤ) + s)
    (hu : u * Λ < ((k * a : ℕ) : ℝ) - H) (hZ : Z * Λ < ((k * a : ℕ) : ℝ) - H) :
    slabTail k B (k * a) H ≤ 2 * (H + B) / Λ +
      ∑ s ∈ Ioc (-(H : ℤ)) B with ∀ i, s ≠ (k : ℤ) * b i, ∑ ℓ ∈ Icc ⌈L₀⌉₊ ⌊Λ⌋₊,
        if ∃ p : ℕ, p.Prime ∧ Z < p ∧ ((k * a : ℕ) : ℤ) + s = ℓ * p then 1 / (ℓ : ℝ) else 0 := by
  set A := k * a with hA
  set G : ℤ → ℝ := fun s ↦ if ∀ i, s ≠ k * b i then ∑ ℓ ∈ Icc ⌈L₀⌉₊ ⌊Λ⌋₊,
    (if ∃ p : ℕ, p.Prime ∧ Z < p ∧ (A : ℤ) + s = ℓ * p then 1 / (ℓ : ℝ) else 0) else 0 with hG
  have hG₀ : ∀ s, 0 ≤ G s := by
    intro s
    simp only [hG]
    split_ifs
    · exact sum_nonneg fun _ _ ↦ by split_ifs <;> positivity
    · exact le_rfl
  -- each `x` in the slab, other than a prime hole, is bounded through `G (x - A)`
  have hpt : ∀ x ∈ Ioc (A - H) (A + B), ¬(A < x ∧ IsPrimeHole k x) →
      bigPrimeRatio A x ≤ 2 / Λ + G (x - A) := by
    intro x hx hxh
    rw [mem_Ioc] at hx
    have hx₂ : x ^ 2 < (A + 1) ^ 3 := (Nat.pow_le_pow_left hx.2 2).trans_lt hB
    by_cases hs : ∀ i, (x : ℤ) - A ≠ k * b i
    · -- off the holes, a covering prime `q ≤ u < p` divides the cofactor `ℓ`
      rw [show G (x - A) = _ from ite_eq_left hs]
      refine bigPrimeRatio_le hΛ hx₂ _
        (fun ℓ ↦ ∃ p : ℕ, p.Prime ∧ Z < p ∧ (A : ℤ) + (x - A) = ℓ * p) fun p hp _ hpΛ ↦ ?_
      have hp' := Nat.mem_primeFactors.mp hp
      have hxℓ : x = x / p * p := (Nat.div_mul_cancel hp'.2.1).symm
      obtain ⟨q, hq, hLq, hqu, hqx⟩ := hcov ((x : ℤ) - A) (by omega) (by omega) hs
      have hxH : (A : ℝ) - H < x := by
        have h : ((A - H : ℕ) : ℝ) < x := by exact_mod_cast hx.1
        rwa [Nat.cast_sub hH] at h
      have hxp : (x : ℝ) ≤ Λ * p := by
        rw [hxℓ]
        push_cast
        exact mul_le_mul_of_nonneg_right hpΛ (Nat.cast_nonneg _)
      have hup : u < p := by
        by_contra! h
        nlinarith
      have hZp : Z < p := by
        by_contra! h
        nlinarith
      have hqℓ : q ∣ x / p := by
        have hqx' : q ∣ x := by
          rw [add_sub_cancel] at hqx
          exact_mod_cast hqx
        rw [hxℓ] at hqx'
        refine ((Nat.Prime.dvd_mul hq).mp hqx').resolve_right fun h ↦ ?_
        rw [(Nat.prime_dvd_prime_iff_eq hq hp'.1).mp h] at hqu
        linarith
      have hℓ₀ : 0 < x / p := Nat.div_pos (Nat.le_of_dvd (by omega) hp'.2.1) hp'.1.pos
      refine ⟨mem_Icc.mpr ⟨Nat.ceil_le.mpr (hLq.trans ?_), Nat.le_floor hpΛ⟩,
        p, hp'.1, hZp, ?_⟩
      · exact_mod_cast Nat.le_of_dvd hℓ₀ hqℓ
      · rw [add_sub_cancel]
        exact_mod_cast hxℓ
    · -- at a hole `x = k (a + b_i)` with `a + b_i` composite, every cofactor exceeds `R`
      push Not at hs
      obtain ⟨i, hi⟩ := hs
      have hxi : x = k * (a + b i) := by
        have h : (x : ℤ) = k * (a + b i) := by
          rw [hA] at hi
          push_cast at hi ⊢
          linarith
        exact_mod_cast h
      have hAx : A < x := by
        rw [hxi, hA, mul_add]
        have := hb₀ i
        have := Nat.mul_le_mul_left k this
        omega
      have hnp : ¬(a + b i).Prime := fun hpr ↦ hxh ⟨hAx, a + b i, hpr, by omega, hxi⟩
      have hGx : G (x - A) = 0 := ite_eq_right (not_forall.mpr ⟨i, not_not.mpr hi⟩)
      rw [hGx]
      have h := bigPrimeRatio_le (I := ∅) (Q := fun _ ↦ False) hΛ hx₂ fun p hp hpA hpΛ ↦ ?_
      · simpa using h
      exfalso
      have hp' := Nat.mem_primeFactors.mp hp
      have hpy : p ∣ a + b i := by
        have h := hp'.2.1
        rw [hxi] at h
        refine ((Nat.Prime.dvd_mul hp'.1).mp h).resolve_left fun h ↦ ?_
        have hpk := Nat.le_of_dvd (by omega) h
        have : p ^ 2 ≤ k * a := by nlinarith
        omega
      have hy₁ : (a + b i) / p ≠ 1 := by
        intro h
        apply hnp
        have h' := Nat.div_mul_cancel hpy
        rw [h, one_mul] at h'
        rw [← h']
        exact hp'.1
      have hy₀ : (a + b i) / p ≠ 0 :=
        (Nat.div_pos (Nat.le_of_dvd (by omega) hpy) hp'.1.pos).ne'
      have hR : R < ((a + b i) / p : ℕ) :=
        (hrough i _ (Nat.minFac_prime hy₁) ((Nat.minFac_dvd _).trans (Nat.div_dvd_of_dvd hpy))
          ).trans_le (by exact_mod_cast Nat.minFac_le (Nat.pos_of_ne_zero hy₀))
      have hxp : x / p = k * ((a + b i) / p) := by rw [hxi, Nat.mul_div_assoc _ hpy]
      have h : (((a + b i) / p : ℕ) : ℝ) ≤ ((x / p : ℕ) : ℝ) := by
        rw [hxp]
        exact_mod_cast Nat.le_mul_of_pos_left _ hk
      linarith
  unfold slabTail
  calc ∑ x ∈ Ioc (A - H) (A + B) with ¬(A < x ∧ IsPrimeHole k x), bigPrimeRatio A x
      ≤ ∑ x ∈ Ioc (A - H) (A + B) with ¬(A < x ∧ IsPrimeHole k x), (2 / Λ + G (x - A)) :=
        sum_le_sum fun x hx ↦ hpt x (mem_filter.mp hx).1 (mem_filter.mp hx).2
    _ ≤ ∑ x ∈ Ioc (A - H) (A + B), (2 / Λ + G (x - A)) :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ ↦
          add_nonneg (by positivity) (hG₀ _)
    _ = 2 * (H + B) / Λ + ∑ s ∈ Ioc (-(H : ℤ)) B, G s := by
        rw [sum_add_distrib, sum_const, Nat.card_Ioc, nsmul_eq_mul,
          show A + B - (A - H) = H + B by omega]
        congr 1
        · push_cast
          ring
        · refine sum_nbij' (fun x ↦ (x : ℤ) - A) (fun s ↦ (s + A).toNat) ?_ ?_ ?_ ?_ ?_
          · intro x hx
            simp only [mem_Ioc] at hx ⊢
            omega
          · intro s hs
            simp only [mem_Ioc] at hs ⊢
            omega
          · intro x hx
            simp only [mem_Ioc] at hx
            omega
          · intro s hs
            simp only [mem_Ioc] at hs
            omega
          · intro x _
            rfl
    _ = _ := by rw [sum_filter]

/-! ### Summing over anchors, offsets, and cofactors -/

/-- At most `(H + B) / g + 1` offsets `s ∈ (-H, B]` have `g ∣ c₀ + s`. -/
private lemma card_filter_dvd_add_le (c₀ : ℤ) (H B : ℕ) {g : ℕ} (hg : 0 < g) :
    (#{s ∈ Ioc (-(H : ℤ)) B | (g : ℤ) ∣ c₀ + s} : ℝ) ≤ (H + B) / g + 1 := by
  set lo := (c₀ - H) / (g : ℤ)
  set hi := (c₀ + B) / (g : ℤ)
  have hg' : (0 : ℤ) < g := by exact_mod_cast hg
  have hlo := Int.emod_add_mul_ediv (c₀ - H) g
  have hhi := Int.emod_add_mul_ediv (c₀ + B) g
  have hlo₁ := Int.emod_nonneg (c₀ - H) hg'.ne'
  have hlo₂ := Int.emod_lt_of_pos (c₀ - H) hg'
  have hhi₁ := Int.emod_nonneg (c₀ + B) hg'.ne'
  have hhi₂ := Int.emod_lt_of_pos (c₀ + B) hg'
  -- `s ↦ (c₀ + s) / g` injects the offsets into `(lo, hi]`
  have h₁ : #{s ∈ Ioc (-(H : ℤ)) B | (g : ℤ) ∣ c₀ + s} ≤ #(Ioc lo hi) := by
    refine card_le_card_of_injOn (fun s ↦ (c₀ + s) / g) (fun s hs ↦ ?_) fun s hs s' hs' h ↦ ?_
    · simp only [coe_filter, mem_Ioc, Set.mem_ofPred_eq, mem_coe] at hs ⊢
      obtain ⟨⟨hs₁, hs₂⟩, j, hj⟩ := hs
      rw [hj, Int.mul_ediv_cancel_left _ hg'.ne']
      constructor
      · refine Int.lt_of_mul_lt_mul_left (a := g) ?_ hg'.le
        linarith
      · refine Int.lt_add_one_iff.mp (Int.lt_of_mul_lt_mul_left (a := g) ?_ hg'.le)
        linarith
    · simp only [coe_filter, mem_Ioc, Set.mem_ofPred_eq] at hs hs'
      obtain ⟨_, j, hj⟩ := hs
      obtain ⟨_, j', hj'⟩ := hs'
      simp only [hj, hj', Int.mul_ediv_cancel_left _ hg'.ne'] at h
      rw [h] at hj
      linarith
  -- `(hi - lo) g < H + B + g`
  have h₂ : ((hi - lo).toNat : ℤ) * g ≤ H + B + g := by
    rcases le_or_gt 0 (hi - lo) with h | h
    · rw [Int.toNat_of_nonneg h]
      nlinarith
    · rw [Int.toNat_of_nonpos h.le, Nat.cast_zero, zero_mul]
      positivity
  have h₃ : (((hi - lo).toNat : ℕ) : ℝ) * g ≤ H + B + g := by exact_mod_cast h₂
  rw [Int.card_Ioc] at h₁
  calc (#{s ∈ Ioc (-(H : ℤ)) B | (g : ℤ) ∣ c₀ + s} : ℝ) ≤ (hi - lo).toNat := by
        exact_mod_cast h₁
    _ ≤ (H + B + g) / g := by rw [le_div_iff₀ (by exact_mod_cast hg)]; exact h₃
    _ = (H + B) / g + 1 := by field_simp

/-- `∑_{L ≤ ℓ ≤ n} 1 / ℓ ≤ 1 + log n`. -/
private lemma sum_Icc_one_div_le {L : ℕ} (hL : 1 ≤ L) (n : ℕ) :
    ∑ ℓ ∈ Icc L n, 1 / (ℓ : ℝ) ≤ 1 + Real.log n := by
  calc ∑ ℓ ∈ Icc L n, 1 / (ℓ : ℝ) ≤ ∑ ℓ ∈ Icc 1 n, 1 / (ℓ : ℝ) :=
        sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc_left hL) fun _ _ _ ↦ by positivity
    _ = harmonic n := by
        simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, one_div]
    _ ≤ 1 + Real.log n := harmonic_le_one_add_log n

open scoped Classical in
/-- The weighted slab tail is at most `ε ∑ W` plus `C ∑_{s, ℓ} K(s, ℓ) / ℓ`, when every
weighted anchor has slab tail at most `ε + ∑_{s, ℓ} 1[P t s ℓ] / ℓ` and at most `K(s, ℓ)`
weighted anchors satisfy `P t s ℓ`. -/
lemma sum_mul_slabTail_le {k B H : ℕ} {T I : Finset ℕ} {S : Finset ℤ} {A : ℕ → ℕ}
    {W : ℕ → ℝ} {C ε : ℝ} (P : ℕ → ℤ → ℕ → Prop) (K : ℤ → ℕ → ℝ) (hC : 0 ≤ C)
    (hW₀ : ∀ t, 0 ≤ W t) (hWC : ∀ t ∈ T, W t ≤ C)
    (hslab : ∀ t ∈ T, W t ≠ 0 → slabTail k B (A t) H ≤
      ε + ∑ s ∈ S, ∑ ℓ ∈ I, if P t s ℓ then 1 / (ℓ : ℝ) else 0)
    (hK : ∀ s ∈ S, ∀ ℓ ∈ I, (#{t ∈ T | W t ≠ 0 ∧ P t s ℓ} : ℝ) ≤ K s ℓ) :
    ∑ t ∈ T, W t * slabTail k B (A t) H ≤
      ε * ∑ t ∈ T, W t + C * ∑ s ∈ S, ∑ ℓ ∈ I, K s ℓ / (ℓ : ℝ) := by
  calc ∑ t ∈ T, W t * slabTail k B (A t) H
      ≤ ∑ t ∈ T, W t * (ε + ∑ s ∈ S, ∑ ℓ ∈ I, if P t s ℓ then 1 / (ℓ : ℝ) else 0) := by
        refine sum_le_sum fun t ht ↦ ?_
        by_cases hw : W t = 0
        · simp [hw]
        · exact mul_le_mul_of_nonneg_left (hslab t ht hw) (hW₀ t)
    _ = ε * ∑ t ∈ T, W t + ∑ s ∈ S, ∑ ℓ ∈ I, ∑ t ∈ T,
          W t * (if P t s ℓ then 1 / (ℓ : ℝ) else 0) := by
        simp_rw [mul_add, sum_add_distrib, ← sum_mul, mul_sum]
        rw [mul_comm _ ε, sum_comm]
        rw [mul_sum]
        congr 1
        refine sum_congr rfl fun _ _ ↦ ?_
        exact sum_comm
    _ ≤ ε * ∑ t ∈ T, W t + ∑ s ∈ S, ∑ ℓ ∈ I, C * (K s ℓ / (ℓ : ℝ)) := by
        gcongr with s hs ℓ hℓ
        calc ∑ t ∈ T, W t * (if P t s ℓ then 1 / (ℓ : ℝ) else 0)
            ≤ ∑ t ∈ T, if W t ≠ 0 ∧ P t s ℓ then C / (ℓ : ℝ) else 0 := by
              refine sum_le_sum fun t ht ↦ ?_
              by_cases hw : W t = 0
              · simp only [hw, zero_mul]
                split_ifs <;> positivity
              · by_cases hp : P t s ℓ
                · simp only [hp, ne_eq, hw, not_false_eq_true, and_self, ite_true]
                  rw [mul_one_div]
                  gcongr
                  exact hWC t ht
                · simp [hp]
          _ = #{t ∈ T | W t ≠ 0 ∧ P t s ℓ} * (C / ℓ) := by
              rw [← sum_filter, sum_const, nsmul_eq_mul]
          _ ≤ K s ℓ * (C / ℓ) := by gcongr; exact hK s hs ℓ hℓ
          _ = C * (K s ℓ / (ℓ : ℝ)) := by ring
    _ = ε * ∑ t ∈ T, W t + C * ∑ s ∈ S, ∑ ℓ ∈ I, K s ℓ / (ℓ : ℝ) := by
        simp_rw [mul_sum]

/-- Summing the compatible pair bounds `C ((N g / ℓ + 1) E + Y)` against `1 / ℓ` over the
offsets `s ∈ (-H, B]` and the cofactors `ℓ ∈ [L, n]`. -/
lemma sum_sum_pair_bound_le {H B L n : ℕ} (hL : 1 ≤ L) {S : Finset ℤ}
    (hS : S ⊆ Ioc (-(H : ℤ)) B) (g : ℕ → ℕ) (hg₁ : ∀ ℓ, 1 ≤ g ℓ) (hg : ∀ ℓ, 1 ≤ ℓ → g ℓ ≤ ℓ)
    (c₀ : ℤ) {N E Y C : ℝ} (hN : 0 ≤ N) (hE : 0 ≤ E) (hY : 0 ≤ Y) (hC : 0 ≤ C) :
    ∑ s ∈ S, ∑ ℓ ∈ Icc L n,
        (if (g ℓ : ℤ) ∣ c₀ + s then C * (N * g ℓ / ℓ + 1) * E + C * Y else 0) / ℓ ≤
      C * ((H + B) * N * E * (2 / L) + (N * E + (H + B + 1) * (E + Y)) * (1 + Real.log n)) := by
  set F : ℕ → ℝ := fun ℓ ↦ C * (N * g ℓ / ℓ + 1) * E + C * Y with hF
  have hF₀ : ∀ ℓ, 0 ≤ F ℓ := fun ℓ ↦ by positivity
  rw [sum_comm]
  calc ∑ ℓ ∈ Icc L n, ∑ s ∈ S, (if (g ℓ : ℤ) ∣ c₀ + s then F ℓ else 0) / ℓ
      ≤ ∑ ℓ ∈ Icc L n, C * ((H + B) * N * E * (1 / (ℓ : ℝ) ^ 2) +
          (N * E + (H + B + 1) * (E + Y)) * (1 / (ℓ : ℝ))) := by
        refine sum_le_sum fun ℓ hℓ ↦ ?_
        have hℓ₁ : (1 : ℝ) ≤ ℓ := by exact_mod_cast hL.trans (mem_Icc.mp hℓ).1
        have hg₁' : (1 : ℝ) ≤ g ℓ := by exact_mod_cast hg₁ ℓ
        have hg' : (g ℓ : ℝ) ≤ ℓ := by exact_mod_cast hg ℓ (hL.trans (mem_Icc.mp hℓ).1)
        calc ∑ s ∈ S, (if (g ℓ : ℤ) ∣ c₀ + s then F ℓ else 0) / ℓ
            ≤ ∑ s ∈ Ioc (-(H : ℤ)) B, (if (g ℓ : ℤ) ∣ c₀ + s then F ℓ else 0) / ℓ :=
              sum_le_sum_of_subset_of_nonneg hS fun _ _ _ ↦ by split_ifs <;> positivity
          _ = #{s ∈ Ioc (-(H : ℤ)) B | (g ℓ : ℤ) ∣ c₀ + s} * F ℓ / ℓ := by
              rw [← sum_div, ← sum_filter, sum_const, nsmul_eq_mul]
          _ ≤ ((H + B) / g ℓ + 1) * F ℓ / ℓ := by
              gcongr
              exact card_filter_dvd_add_le c₀ H B (hg₁ ℓ)
          _ = C * ((H + B) * N * E * (1 / (ℓ : ℝ) ^ 2) + (H + B) / g ℓ * (E + Y) / ℓ +
                N * E * (g ℓ / ℓ) / ℓ + (E + Y) / ℓ) := by
              simp only [hF]
              field_simp
              ring
          _ ≤ C * ((H + B) * N * E * (1 / (ℓ : ℝ) ^ 2) + (H + B) * (E + Y) / ℓ +
                N * E * 1 / ℓ + (E + Y) / ℓ) := by
              gcongr
              · exact div_le_self (by positivity) hg₁'
              · exact (div_le_one (by positivity)).mpr hg'
          _ = C * ((H + B) * N * E * (1 / (ℓ : ℝ) ^ 2) +
                (N * E + (H + B + 1) * (E + Y)) * (1 / (ℓ : ℝ))) := by ring
    _ = C * ((H + B) * N * E * ∑ ℓ ∈ Icc L n, 1 / (ℓ : ℝ) ^ 2 +
          (N * E + (H + B + 1) * (E + Y)) * ∑ ℓ ∈ Icc L n, 1 / (ℓ : ℝ)) := by
        rw [← mul_sum]
        congr 1
        rw [mul_sum, mul_sum, ← sum_add_distrib]
    _ ≤ C * ((H + B) * N * E * (2 / L) + (N * E + (H + B + 1) * (E + Y)) * (1 + Real.log n)) := by
        gcongr
        · have h := sum_one_div_sq_le_of_lt (S := Icc L n) (K := L - 1) fun ℓ hℓ ↦ by
            have := (mem_Icc.mp hℓ).1
            omega
          rwa [Nat.cast_sub hL, Nat.cast_one, sub_add_cancel] at h
        · exact sum_Icc_one_div_le hL n

/-! ### Asymptotics -/

open Filter

/-- `log u → ∞` for the covering length `u = log X / (64 log 4)`. -/
lemma tendsto_log_cover_atTop :
    Tendsto (fun X : ℕ ↦ Real.log (Real.log X / (64 * Real.log 4))) atTop atTop :=
  Real.tendsto_log_atTop.comp (tendsto_log_natCast_atTop.atTop_div_const (by positivity))

/-- `64 log 4 > 1`. -/
lemma one_lt_sixtyFour_mul_log_four : 1 < 64 * Real.log 4 := by
  have h := Real.one_sub_inv_le_log_of_pos (x := 4) (by norm_num)
  norm_num at h
  linarith

/-- The summed pair bounds, `(H + B) N E / L + (N E + (H + B + 1) (E + Y)) log n` with
`E = (log log X / log X)^{r+1}`, `L ≥ (log u)^{r+3}`, `n ≤ (log X)^3`, and `Y = X^{3c}`, are
`o(N / (log X)^r)` once `N ≥ X^{63/64}`. -/
lemma eventually_pair_sum_le (k r B : ℕ) {K c₁ c : ℝ} (hK : 0 ≤ K) (hc₁ : 0 < c₁)
    (hc : 0 < c) (hc' : c ≤ 1 / 8) :
    ∀ᶠ X : ℕ in atTop, ∀ (H Lc n : ℕ) (N : ℝ),
      (H : ℝ) ≤ Real.log X + Real.log (8 * k) + 1 →
      Real.log (Real.log X / (64 * Real.log 4)) ^ (r + 3) ≤ Lc →
      (n : ℝ) ≤ Real.log X ^ 3 → (X : ℝ) ^ (63 / 64 : ℝ) ≤ N →
      K * ((H + B) * N * (Real.log (Real.log X) / Real.log X) ^ (r + 1) * (2 / Lc) +
        (N * (Real.log (Real.log X) / Real.log X) ^ (r + 1) + (H + B + 1) *
          ((Real.log (Real.log X) / Real.log X) ^ (r + 1) + (X : ℝ) ^ (3 * c))) *
            (1 + Real.log n)) ≤ c₁ * N / Real.log X ^ r := by
  have hκ : 0 < Real.log (64 * Real.log 4) := Real.log_pos one_lt_sixtyFour_mul_log_four
  filter_upwards [tendsto_log_natCast_atTop.eventually_ge_atTop
      (Real.exp 1 + |Real.log (8 * k)| + B + 2),
    tendsto_log_cover_atTop.eventually_ge_atTop
      (12 * K * 2 ^ (r + 1) / c₁ + 1 + Real.log (64 * Real.log 4)),
    tendsto_log_natCast_atTop.eventually
      (eventually_log_pow_le_mul_rpow (r + 2) one_pos (ε := c₁ / (12 * (K + 1))) (by positivity)),
    tendsto_natCast_atTop_atTop.eventually
      (eventually_log_pow_le_mul_rpow (r + 2) (δ := 1 / 2) (ε := c₁ / (48 * (K + 1))) (by norm_num)
        (by positivity)),
    eventually_ge_atTop 1] with X hL hv hℓℓ hLX hX₁
  intro H Lc n N hH hLc hn hN
  simp only [Real.rpow_one] at hℓℓ
  set L := Real.log X
  set ℓℓ := Real.log L
  set v := Real.log (L / (64 * Real.log 4))
  set E := (ℓℓ / L) ^ (r + 1)
  set Y := (X : ℝ) ^ (3 * c)
  set κ := Real.log (64 * Real.log 4)
  have hX₁' : (1 : ℝ) ≤ X := by exact_mod_cast hX₁
  have he : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have hL₁ : 1 ≤ L := by linarith [abs_nonneg (Real.log (8 * k))]
  have hL₀ : 0 < L := by linarith
  have hℓℓ₁ : 1 ≤ ℓℓ := by
    rw [Real.le_log_iff_exp_le hL₀]
    linarith [abs_nonneg (Real.log (8 * k))]
  have hℓℓL : ℓℓ ≤ L := Real.log_le_self hL₀.le
  have hvℓℓ : ℓℓ = v + κ := by
    simp only [v, κ, ℓℓ]
    rw [Real.log_div hL₀.ne' (by linarith [one_lt_sixtyFour_mul_log_four])]
    ring
  have hv₁ : 1 ≤ v := by linarith [div_nonneg (by positivity : 0 ≤ 12 * K * 2 ^ (r + 1)) hc₁.le]
  have hvκ : κ ≤ v := by linarith [div_nonneg (by positivity : 0 ≤ 12 * K * 2 ^ (r + 1)) hc₁.le]
  have hvK : 12 * K * 2 ^ (r + 1) ≤ c₁ * v := by
    rw [← div_le_iff₀' hc₁]
    linarith
  have hN₀ : 0 ≤ N := le_trans (by positivity) hN
  have hEL : E * L ^ (r + 1) = ℓℓ ^ (r + 1) := by
    simp only [E]
    rw [div_pow]
    field_simp
  have hE₀ : 0 ≤ E := by positivity
  have hE₁ : E ≤ 1 := pow_le_one₀ (by positivity) ((div_le_one hL₀).mpr hℓℓL)
  have hY₁ : 1 ≤ Y := Real.one_le_rpow hX₁' (by positivity)
  have hY : Y ≤ (X : ℝ) ^ (3 / 8 : ℝ) := Real.rpow_le_rpow_of_exponent_le hX₁' (by linarith)
  have hHB : (H : ℝ) + B + 1 ≤ 2 * L := by linarith [le_abs_self (Real.log (8 * k))]
  have hlogn : 1 + Real.log n ≤ 4 * ℓℓ := by
    rcases Nat.eq_zero_or_pos n with h | h
    · simp only [h, CharP.cast_eq_zero, Real.log_zero]
      linarith
    · have h' : Real.log n ≤ Real.log (L ^ 3) := Real.log_le_log (by exact_mod_cast h) hn
      rw [Real.log_pow] at h'
      push_cast at h'
      linarith
  have hv₀ : 0 < v := by linarith
  -- the three terms
  have hT₁ : K * ((H + B) * N * E * (2 / Lc)) * L ^ r ≤ c₁ / 3 * N := by
    have h₁ : (H : ℝ) + B ≤ 2 * L := by linarith
    calc K * ((H + B) * N * E * (2 / Lc)) * L ^ r
        ≤ K * (2 * L * N * E * (2 / v ^ (r + 3))) * L ^ r := by gcongr
      _ = 4 * K * N * (E * L ^ (r + 1)) / v ^ (r + 3) := by field_simp; ring
      _ = 4 * K * N * ℓℓ ^ (r + 1) / v ^ (r + 3) := by rw [hEL]
      _ ≤ 4 * K * N * (2 * v) ^ (r + 1) / v ^ (r + 3) := by gcongr; linarith
      _ = 4 * K * 2 ^ (r + 1) * N / v ^ 2 := by field_simp; ring
      _ ≤ c₁ / 3 * N := by
        rw [div_le_iff₀ (by positivity)]
        have h₂ : 12 * K * 2 ^ (r + 1) * N ≤ c₁ * v * N := mul_le_mul_of_nonneg_right hvK hN₀
        have h₃ : c₁ * v * N ≤ c₁ * v * N * v := le_mul_of_one_le_right (by positivity) hv₁
        nlinarith
  have hT₂ : K * (N * E * (1 + Real.log n)) * L ^ r ≤ c₁ / 3 * N := by
    calc K * (N * E * (1 + Real.log n)) * L ^ r ≤ K * (N * E * (4 * ℓℓ)) * L ^ r := by gcongr
      _ = 4 * K * N * (E * L ^ (r + 1)) * ℓℓ / L := by field_simp; ring
      _ = 4 * K * N * ℓℓ ^ (r + 2) / L := by rw [hEL]; ring
      _ ≤ 4 * K * N * (c₁ / (12 * (K + 1)) * L) / L := by gcongr
      _ = c₁ / 3 * N * (K / (K + 1)) := by field_simp; ring
      _ ≤ c₁ / 3 * N :=
        mul_le_of_le_one_right (by positivity) ((div_le_one (by linarith)).mpr (by linarith))
  have hT₃ : K * ((H + B + 1) * (E + Y) * (1 + Real.log n)) * L ^ r ≤ c₁ / 3 * N := by
    have hX₀ : (0 : ℝ) < X := by linarith
    calc K * ((H + B + 1) * (E + Y) * (1 + Real.log n)) * L ^ r
        ≤ K * (2 * L * (2 * (X : ℝ) ^ (3 / 8 : ℝ)) * (4 * L)) * L ^ r := by
          gcongr
          · linarith
          · linarith
      _ = 16 * K * L ^ (r + 2) * (X : ℝ) ^ (3 / 8 : ℝ) := by ring
      _ ≤ 16 * K * (c₁ / (48 * (K + 1)) * (X : ℝ) ^ (1 / 2 : ℝ)) * (X : ℝ) ^ (3 / 8 : ℝ) := by
          gcongr
      _ = c₁ / 3 * (K / (K + 1)) * ((X : ℝ) ^ (1 / 2 : ℝ) * (X : ℝ) ^ (3 / 8 : ℝ)) := by
          field_simp
          ring
      _ = c₁ / 3 * (K / (K + 1)) * (X : ℝ) ^ (7 / 8 : ℝ) := by
          rw [← Real.rpow_add hX₀]
          norm_num
      _ ≤ c₁ / 3 * 1 * (X : ℝ) ^ (63 / 64 : ℝ) :=
          mul_le_mul (mul_le_mul_of_nonneg_left ((div_le_one (by linarith)).mpr (by linarith))
            (by positivity)) (Real.rpow_le_rpow_of_exponent_le hX₁' (by norm_num))
            (by positivity) (by positivity)
      _ ≤ c₁ / 3 * N := by rw [mul_one]; gcongr
  rw [le_div_iff₀ (by positivity)]
  linarith

end Erdos420
