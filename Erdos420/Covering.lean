module

public import Erdos420.Covering.Estimates
public import Erdos420.Covering.Residues
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# A covering that protects a fixed set of holes

Let `M_u` be the product of the primes `q` with `(log u)^a ≤ q ≤ u`. For a
fixed finite set `H` of positive holes and a fixed `C`, there is a residue `z`
such that every `z + h` with `h ∈ H` is coprime to `M_u`, while every other
`z + s` with `−C u ≤ s ≤ B` shares a prime with `M_u`. This is the covering of
Westzynthius, with `C` fixed, in the form of Erdős, Graham, Ivić, and Pomerance
(1996, proof of Theorem 3) that keeps all covering primes above `(log u)^a`.

The residue is `0` modulo the primes in `(y, u / K]`, with `y = (log u)^A`.
Residues modulo the primes in `[(log u)^a, y]` are chosen one prime at a time, by
averaging over the classes that avoid `H`. Each survivor then gets its own prime in `(u / K, u]`.

We take `K = 4`. With `D = 16 C² + 2`:

* at most `D u / log u` offsets survive the primes in `(y, u/4]`: the `y`-smooth ones (Rankin),
  the cofactors `c p` with `c ≤ 4C` and `p > u/4` prime (Chebyshev), and those in `[0, B]`;
* the primes in `[(log u)^a, y]` have `∑ 1/q ≥ log (16 D)` once `A = 2a 2^I` with
  `I ≥ 50 log (16 D)`, so the middle stage leaves at most `u / (8 log u)` survivors;
* the `u / (4 log u)` primes in `(u/4, u]` cover them, as each survivor `s` has at most one
  such prime dividing each `s − h`.
-/

@[expose] public section

namespace Erdos420

/-- The product of the primes `q` with `(log u)^a ≤ q ≤ u`. -/
noncomputable def coverModulus (a : ℕ) (u : ℝ) : ℕ :=
  ∏ q ∈ (Finset.Iic ⌊u⌋₊).filter (fun q : ℕ ↦ q.Prime ∧ Real.log u ^ a ≤ q), q

open Filter Finset Real

/-- Residues `e q` that avoid every hole and cover every other offset give the protected cover,
by the Chinese remainder theorem. -/
lemma exists_cover_of_residues {H : Finset ℕ} {B a : ℕ} {C u : ℝ} (e : ℕ → ℤ)
    (hhole : ∀ q : ℕ, q.Prime → q ≤ ⌊u⌋₊ → log u ^ a ≤ q → ∀ h ∈ H, ¬ (q : ℤ) ∣ e q + h)
    (hcov : ∀ s : ℤ, -(C * u) ≤ s → s ≤ B → (∀ h ∈ H, s ≠ h) →
      ∃ q : ℕ, q.Prime ∧ q ≤ ⌊u⌋₊ ∧ log u ^ a ≤ q ∧ (q : ℤ) ∣ e q + s) :
    ∃ z : ℤ, (∀ h ∈ H, IsCoprime (z + h) (coverModulus a u : ℤ)) ∧
      ∀ s : ℤ, -(C * u) ≤ s → s ≤ B → (∀ h ∈ H, s ≠ h) →
        ¬ IsCoprime (z + s) (coverModulus a u : ℤ) := by
  set P := (Iic ⌊u⌋₊).filter fun q : ℕ ↦ q.Prime ∧ log u ^ a ≤ q with hP
  obtain ⟨z, hz⟩ := exists_int_forall_dvd_sub e P fun q hq ↦ (mem_filter.mp hq).2.1
  have hM : (coverModulus a u : ℤ) = ∏ q ∈ P, (q : ℤ) := by
    rw [coverModulus, Nat.cast_prod]
  refine ⟨z, fun h hh ↦ ?_, fun s hs₁ hs₂ hs₃ hcop ↦ ?_⟩
  · rw [hM]
    refine IsCoprime.prod_right fun q hq ↦ ?_
    have hq' := hq
    simp only [hP, mem_filter, mem_Iic] at hq'
    obtain ⟨hqu, hqp, hqa⟩ := hq'
    refine ((Prime.coprime_iff_not_dvd (Nat.prime_iff_prime_int.mp hqp)).mpr fun hd ↦
      hhole q hqp hqu hqa h hh ?_).symm
    rw [show e q + h = (z + h) - (z - e q) by ring]
    exact dvd_sub hd (hz q hq)
  · obtain ⟨q, hqp, hqu, hqa, hd⟩ := hcov s hs₁ hs₂ hs₃
    have hqP : q ∈ P := mem_filter.mpr ⟨mem_Iic.mpr hqu, hqp, hqa⟩
    have hzs : (q : ℤ) ∣ z + s := by
      rw [show z + s = (z - e q) + (e q + s) by ring]
      exact dvd_add (hz q hqP) hd
    have hqM : (q : ℤ) ∣ coverModulus a u := by
      rw [hM]
      exact dvd_prod_of_mem _ hqP
    exact (Nat.prime_iff_prime_int.mp hqp).not_isUnit (hcop.isUnit_of_dvd' hzs hqM)

open scoped Classical in
/-- At most `(16 C² + 2) u / log u` offsets in `[−C u, B]` have no prime factor in `(y, u/4]`:
those in `[0, B]`, the `y`-smooth ones, and the `c p` with `c ≤ 4 C` and `p > u/4` prime. -/
lemma card_survivors_le {C u y : ℝ} {B m₀ : ℕ} (hC : 1 ≤ C) (hu : 16 ≤ u) (hy : 0 ≤ y)
    (hm₀ : ∀ m ≥ m₀, ∀ k : ℕ, (#{p ∈ Ioc k m | p.Prime} : ℝ) ≤ 2 * m / log m)
    (hum₀ : m₀ ≤ ⌊u / 4⌋₊)
    (hsmooth : (#(⌊C * u⌋₊.smoothNumbersUpTo (⌊y⌋₊ + 1)) : ℝ) ≤ u / log u)
    (hB : (B : ℝ) + 1 ≤ u / log u) :
    (#{s ∈ Icc (-⌊C * u⌋) (B : ℤ) |
      ∀ q : ℕ, q.Prime → y < q → (q : ℝ) ≤ u / 4 → ¬ (q : ℤ) ∣ s} : ℝ) ≤
        (16 * C ^ 2 + 2) * (u / log u) := by
  set L := log u with hL_def
  have hu0 : 0 < u := by linarith
  have hlog4 : log 4 ≤ L / 2 := by
    have h16 : log 16 = 2 * log 4 := by
      rw [show (16 : ℝ) = 4 ^ 2 by norm_num, log_pow]
      norm_num
    have : log 16 ≤ L := log_le_log (by norm_num) hu
    linarith
  have hL : 0 < L := by
    have : 0 < log 4 := log_pos (by norm_num)
    linarith
  set N₁ : Finset ℕ :=
    {n ∈ Icc 1 ⌊C * u⌋₊ | ∀ q : ℕ, q.Prime → y < q → (q : ℝ) ≤ u / 4 → ¬ q ∣ n} with hN₁
  -- the negative offsets are `−n` with `n ∈ N₁`
  have h₁ : {s ∈ Icc (-⌊C * u⌋) (B : ℤ) |
      ∀ q : ℕ, q.Prime → y < q → (q : ℝ) ≤ u / 4 → ¬ (q : ℤ) ∣ s} ⊆
        Icc 0 (B : ℤ) ∪ N₁.image fun n : ℕ ↦ -(n : ℤ) := by
    intro s hs
    rw [mem_filter, mem_Icc] at hs
    rcases le_or_gt 0 s with h0 | h0
    · exact mem_union_left _ (mem_Icc.mpr ⟨h0, hs.1.2⟩)
    refine mem_union_right _ (mem_image.mpr ⟨(-s).toNat, ?_, by omega⟩)
    have hn : (((-s).toNat : ℕ) : ℤ) = -s := Int.toNat_of_nonneg (by omega)
    refine mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega, Nat.le_floor ?_⟩, fun q hq hyq hqu hqn ↦ ?_⟩
    · have h₁ : -s ≤ ⌊C * u⌋ := by omega
      have h₂ : ((-s : ℤ) : ℝ) ≤ C * u := Int.le_floor.mp h₁
      rw [← hn] at h₂
      exact_mod_cast h₂
    · refine hs.2 q hq hyq hqu ?_
      have := Int.natCast_dvd_natCast.mpr hqn
      rw [hn] at this
      exact dvd_neg.mp this
  -- a non-smooth `n ∈ N₁` is `c p` with `c ≤ 4 C` and `p > u/4` prime
  have h₂ : N₁ ⊆ ⌊C * u⌋₊.smoothNumbersUpTo (⌊y⌋₊ + 1) ∪ (Icc 1 ⌊4 * C⌋₊).biUnion fun c ↦
      {p ∈ Ioc ⌊u / 4⌋₊ (⌊C * u⌋₊ / c) | p.Prime}.image (c * ·) := by
    intro n hn
    rw [hN₁, mem_filter, mem_Icc] at hn
    by_cases hs : n ∈ (⌊y⌋₊ + 1).smoothNumbers
    · exact mem_union_left _ (Nat.mem_smoothNumbersUpTo.mpr ⟨hn.1.2, hs⟩)
    refine mem_union_right _ ?_
    rw [Nat.mem_smoothNumbers'] at hs
    simp only [not_forall, not_lt] at hs
    obtain ⟨p, hp, hpn, hpy⟩ := hs
    have hyp : y < p := (Nat.floor_lt hy).mp (by omega)
    have hup : u / 4 < p := lt_of_not_ge fun h ↦ hn.2 p hp hyp h hpn
    have hcp : n / p * p = n := Nat.div_mul_cancel hpn
    have hc1 : 1 ≤ n / p := Nat.div_pos (Nat.le_of_dvd (by omega) hpn) hp.pos
    have hn' : (n : ℝ) ≤ C * u := (Nat.cast_le.mpr hn.1.2).trans (Nat.floor_le (by positivity))
    refine mem_biUnion.mpr ⟨n / p, mem_Icc.mpr ⟨hc1, Nat.le_floor ?_⟩, mem_image.mpr ⟨p, ?_, ?_⟩⟩
    · -- `c u/4 < c p = n ≤ C u`
      have h₃ : ((n / p : ℕ) : ℝ) * p = n := by exact_mod_cast hcp
      have h₄ : ((n / p : ℕ) : ℝ) * (u / 4) ≤ ((n / p : ℕ) : ℝ) * p :=
        mul_le_mul_of_nonneg_left hup.le (Nat.cast_nonneg _)
      nlinarith
    · refine mem_filter.mpr ⟨mem_Ioc.mpr ⟨(Nat.floor_lt (by positivity)).mpr hup, ?_⟩, hp⟩
      rw [Nat.le_div_iff_mul_le hc1, mul_comm, hcp]
      exact hn.1.2
    · exact hcp
  -- each `c` contributes at most `π(C u / c) ≤ 4 C u / log u` primes
  have h₃ : ∀ c ∈ Icc 1 ⌊4 * C⌋₊,
      (#{p ∈ Ioc ⌊u / 4⌋₊ (⌊C * u⌋₊ / c) | p.Prime} : ℝ) ≤ 4 * C * (u / L) := by
    intro c _
    set m := ⌊C * u⌋₊ / c
    by_cases hm : m ≤ ⌊u / 4⌋₊
    · rw [Ioc_eq_empty (by omega), filter_empty, card_empty, Nat.cast_zero]
      positivity
    have hm' : u / 4 < m := (Nat.floor_lt (by positivity)).mp (by omega)
    have hmCu : (m : ℝ) ≤ C * u :=
      (Nat.cast_le.mpr (Nat.div_le_self _ _)).trans (Nat.floor_le (by positivity))
    have hlogm : L / 2 ≤ log m := by
      have : log (u / 4) ≤ log m := log_le_log (by positivity) hm'.le
      rw [log_div hu0.ne' (by norm_num)] at this
      linarith
    have hlogm0 : 0 < log m := by linarith
    refine (hm₀ m (hum₀.trans (not_le.mp hm).le) _).trans ?_
    rw [div_le_iff₀ hlogm0]
    have : 4 * C * (u / L) * (L / 2) = 2 * (C * u) := by field_simp; ring
    nlinarith [mul_le_mul_of_nonneg_left hlogm (by positivity : (0 : ℝ) ≤ 4 * C * (u / L))]
  have h₄ : (#N₁ : ℝ) ≤ u / L + 16 * C ^ 2 * (u / L) := by
    calc (#N₁ : ℝ) ≤ #(⌊C * u⌋₊.smoothNumbersUpTo (⌊y⌋₊ + 1)) +
          ∑ c ∈ Icc 1 ⌊4 * C⌋₊, (#{p ∈ Ioc ⌊u / 4⌋₊ (⌊C * u⌋₊ / c) | p.Prime} : ℝ) := by
          have := (card_le_card h₂).trans (card_union_le _ _)
          have h' := card_biUnion_le (s := Icc 1 ⌊4 * C⌋₊) (t := fun c ↦
            {p ∈ Ioc ⌊u / 4⌋₊ (⌊C * u⌋₊ / c) | p.Prime}.image (c * ·))
          have h'' : ∑ c ∈ Icc 1 ⌊4 * C⌋₊, #({p ∈ Ioc ⌊u / 4⌋₊ (⌊C * u⌋₊ / c) | p.Prime}.image
              (c * ·)) ≤ ∑ c ∈ Icc 1 ⌊4 * C⌋₊, #{p ∈ Ioc ⌊u / 4⌋₊ (⌊C * u⌋₊ / c) | p.Prime} :=
            sum_le_sum fun _ _ ↦ card_image_le
          exact_mod_cast this.trans (add_le_add le_rfl (h'.trans h''))
      _ ≤ u / L + ∑ c ∈ Icc 1 ⌊4 * C⌋₊, 4 * C * (u / L) := add_le_add hsmooth (sum_le_sum h₃)
      _ ≤ u / L + 16 * C ^ 2 * (u / L) := by
          rw [sum_const, Nat.card_Icc, add_tsub_cancel_right, nsmul_eq_mul]
          have : (⌊4 * C⌋₊ : ℝ) ≤ 4 * C := Nat.floor_le (by positivity)
          have : 0 ≤ 4 * C * (u / L) := by positivity
          nlinarith
  calc (#{s ∈ Icc (-⌊C * u⌋) (B : ℤ) |
        ∀ q : ℕ, q.Prime → y < q → (q : ℝ) ≤ u / 4 → ¬ (q : ℤ) ∣ s} : ℝ)
      ≤ #(Icc 0 (B : ℤ)) + #N₁ := by
        exact_mod_cast (card_le_card h₁).trans ((card_union_le _ _).trans
          (add_le_add le_rfl card_image_le))
    _ ≤ (B + 1) + (u / L + 16 * C ^ 2 * (u / L)) := by
        gcongr
        rw [Int.card_Icc, sub_zero, show ((B : ℤ) + 1).toNat = B + 1 by omega]
        push_cast
        exact le_rfl
    _ ≤ (16 * C ^ 2 + 2) * (u / L) := by linarith

/-- The primes `q ∈ [L^a, L^{2a 2^I}]` have `∏ (1 − 1/q) ≤ exp (−T)` when `I ≥ 50 T`, since
they include the primes in `(X, X^{2^I}]` with `X = ⌈L^a⌉`. -/
private lemma prod_one_sub_inv_le {a I X₀ : ℕ} {L T : ℝ}
    (hX₀ : ∀ X ≥ X₀, ∀ I : ℕ, (I : ℝ) / 50 ≤ ∑ p ∈ Ioc X (X ^ 2 ^ I) with p.Prime, (1 : ℝ) / p)
    (hT : 50 * T ≤ I) (hL2 : 2 ≤ L) (hLX : (X₀ : ℝ) ≤ L) (ha : 1 ≤ a) :
    ∏ q ∈ (Iic ⌊L ^ (2 * a * 2 ^ I)⌋₊).filter (fun q : ℕ ↦ q.Prime ∧ L ^ a ≤ q), (1 - 1 / (q : ℝ)) ≤
      exp (-T) := by
  set Q := (Iic ⌊L ^ (2 * a * 2 ^ I)⌋₊).filter fun q : ℕ ↦ q.Prime ∧ L ^ a ≤ q with hQ
  have hLLa : L ≤ L ^ a := le_self_pow₀ (by linarith) (by omega)
  set X := ⌈L ^ a⌉₊ with hX_def
  have hX : X₀ ≤ X := by
    have : (X₀ : ℝ) ≤ X := hLX.trans (hLLa.trans (Nat.le_ceil _))
    exact_mod_cast this
  have hXL : (X : ℝ) ≤ L ^ (2 * a) := by
    have h₁ := Nat.ceil_lt_add_one (by positivity : 0 ≤ L ^ a)
    have h₂ : 2 ≤ L ^ a := hL2.trans hLLa
    have h₃ := mul_le_mul_of_nonneg_right h₂ (by positivity : (0 : ℝ) ≤ L ^ a)
    rw [pow_mul', sq]
    linarith
  have hsub : {p ∈ Ioc X (X ^ 2 ^ I) | p.Prime} ⊆ Q := by
    intro p hp
    simp only [mem_filter, mem_Ioc] at hp
    refine mem_filter.mpr ⟨mem_Iic.mpr (Nat.le_floor ?_), hp.2, ?_⟩
    · calc (p : ℝ) ≤ (X : ℝ) ^ 2 ^ I := by exact_mod_cast hp.1.2
        _ ≤ (L ^ (2 * a)) ^ 2 ^ I := by gcongr
        _ = L ^ (2 * a * 2 ^ I) := by rw [← pow_mul]
    · exact (Nat.le_ceil _).trans (by exact_mod_cast hp.1.1.le)
  have hsum : T ≤ ∑ q ∈ Q, 1 / (q : ℝ) :=
    calc T ≤ (I : ℝ) / 50 := by
          rw [le_div_iff₀ (by norm_num)]
          linarith
      _ ≤ ∑ p ∈ Ioc X (X ^ 2 ^ I) with p.Prime, (1 : ℝ) / p := hX₀ X hX I
      _ ≤ ∑ q ∈ Q, 1 / (q : ℝ) :=
          sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ ↦ by positivity
  calc ∏ q ∈ Q, (1 - 1 / (q : ℝ)) ≤ ∏ q ∈ Q, exp (-(1 / (q : ℝ))) := by
        refine prod_le_prod₀ (fun q hq ↦ ?_) fun q _ ↦ one_sub_le_exp_neg _
        have : (1 : ℝ) ≤ q := by exact_mod_cast (mem_filter.mp hq).2.1.one_lt.le
        rw [sub_nonneg, div_le_one (by linarith)]
        exact this
    _ = exp (-∑ q ∈ Q, 1 / (q : ℝ)) := by rw [← exp_sum, sum_neg_distrib]
    _ ≤ exp (-T) := exp_le_exp.mpr (by linarith)

open scoped Classical in
/-- The three stages, for one `u` with `L = log u`: given at most `D u / L` survivors of the
primes in `(y, u/4]`, `∏_{q ∈ [L^a, y]} (1 − 1/q) ≤ 1/(16 D)`, and `u / (4L)` primes in
`(u/4, u]`, residues avoiding the holes cover every other offset in `[−C u, B]`. -/
lemma exists_cover_of_le {H : Finset ℕ} (hH : ∀ h ∈ H, 0 < h) {B : ℕ} (hB : ∀ h ∈ H, h ≤ B)
    {a : ℕ} {C D u y : ℝ} (hC : 1 ≤ C) (hD : 0 < D) (hu : 16 ≤ u) (hL2 : 2 ≤ log u)
    (hLr : (#H : ℝ) < log u ^ a) (hLbad : 4 * #H * (log (2 * C) + log u) ≤ log u ^ a)
    (hBy : (B : ℝ) < y) (hya : log u ^ a ≤ y) (hyu : y < u / 4)
    (hquad : C * u + B ≤ (u / 4) ^ 2)
    (hsurv : (#{s ∈ Icc (-⌊C * u⌋) (B : ℤ) |
      ∀ q : ℕ, q.Prime → y < q → (q : ℝ) ≤ u / 4 → ¬ (q : ℤ) ∣ s} : ℝ) ≤ D * (u / log u))
    (hprod : ∏ q ∈ (Iic ⌊y⌋₊).filter (fun q : ℕ ↦ q.Prime ∧ log u ^ a ≤ q), (1 - 1 / (q : ℝ)) ≤
      (16 * D)⁻¹)
    (hRcard : u / (4 * log u) ≤ #{p ∈ Ioc ⌊u / 4⌋₊ ⌊u⌋₊ | p.Prime})
    (hrL : 8 * #H * log u ≤ u) :
    ∃ z : ℤ, (∀ h ∈ H, IsCoprime (z + h) (coverModulus a u : ℤ)) ∧
      ∀ s : ℤ, -(C * u) ≤ s → s ≤ B → (∀ h ∈ H, s ≠ h) →
        ¬ IsCoprime (z + s) (coverModulus a u : ℤ) := by
  set L := log u with hL_def
  set r := #H with hr
  have hu0 : 0 < u := by linarith
  have hL1 : 1 ≤ L := by linarith
  have hL0 : 0 < L := by linarith
  have hLa1 : 1 ≤ L ^ a := one_le_pow₀ hL1
  have hy0 : 0 ≤ y := by linarith
  have hu4 : u / 4 ≤ u := by linarith
  set Q : Finset ℕ := (Iic ⌊y⌋₊).filter fun q : ℕ ↦ q.Prime ∧ L ^ a ≤ q with hQ
  set R : Finset ℕ := (Ioc ⌊u / 4⌋₊ ⌊u⌋₊).filter Nat.Prime with hR
  set S₁ : Finset ℤ := (Icc (-⌊C * u⌋) (B : ℤ)).filter fun s ↦ (∀ h ∈ H, s ≠ h) ∧
    ∀ q : ℕ, q.Prime → y < q → (q : ℝ) ≤ u / 4 → ¬ (q : ℤ) ∣ s with hS₁
  -- every `s − h` is a nonzero integer with `|s − h| ≤ C u + B`
  have habs : ∀ s ∈ S₁, ∀ h ∈ H, s - h ≠ 0 ∧ |((s - h : ℤ) : ℝ)| ≤ C * u + B := by
    intro s hs h hh
    simp only [hS₁, mem_filter, mem_Icc] at hs
    refine ⟨sub_ne_zero.mpr (hs.2.1 h hh), ?_⟩
    have h₁ : ((-⌊C * u⌋ : ℤ) : ℝ) ≤ s := by exact_mod_cast hs.1.1
    have h₂ : (s : ℝ) ≤ B := by exact_mod_cast hs.1.2
    have h₃ : (⌊C * u⌋ : ℝ) ≤ C * u := Int.floor_le _
    have h₄ : (0 : ℝ) < h := by exact_mod_cast hH h hh
    have h₅ : (h : ℝ) ≤ B := by exact_mod_cast hB h hh
    have h₆ : 0 ≤ C * u := by positivity
    push_cast at h₁ ⊢
    rw [abs_le]
    constructor <;> linarith
  have hS₁card : (#S₁ : ℝ) ≤ D * (u / L) := by
    refine le_trans (Nat.cast_le.mpr (card_le_card fun s hs ↦ ?_)) hsurv
    simp only [hS₁, mem_filter] at hs ⊢
    exact ⟨hs.1, hs.2.2⟩
  -- the middle stage
  have hQp : ∀ q ∈ Q, q.Prime ∧ r < q := fun q hq ↦ by
    simp only [hQ, mem_filter] at hq
    refine ⟨hq.2.1, ?_⟩
    have : (r : ℝ) < q := by linarith [hq.2.2]
    exact_mod_cast this
  have hQa : ∀ q ∈ Q, L ^ a ≤ q := fun q hq ↦ (mem_filter.mp hq).2.2
  have hbad : ∀ s ∈ S₁,
      1 / 2 ≤ ∏ q ∈ Q with ∃ h ∈ H, ((q : ℕ) : ℤ) ∣ s - h, (1 - 1 / (q : ℝ)) := by
    intro s hs
    refine one_half_le_prod_one_sub_one_div hLa1 (fun q hq ↦ hQa q (mem_filter.mp hq).1) ?_
    have hsub : {q ∈ Q | ∃ h ∈ H, ((q : ℕ) : ℤ) ∣ s - h} ⊆
        H.biUnion fun h ↦ {q ∈ Q | ((q : ℕ) : ℤ) ∣ s - h} := by
      intro q hq
      simp only [mem_filter, mem_biUnion] at hq ⊢
      obtain ⟨hqQ, h, hh, hd⟩ := hq
      exact ⟨h, hh, hqQ, hd⟩
    -- each `s − h` has at most `log |s − h| / log 2` prime factors
    have heach : ∀ h ∈ H,
        (#{q ∈ Q | ((q : ℕ) : ℤ) ∣ s - h} : ℝ) ≤ 2 * (log (2 * C) + L) := by
      intro h hh
      obtain ⟨hne, habs'⟩ := habs s hs h hh
      have h₁ := card_filter_dvd_mul_log_two_le_log_abs (fun q hq ↦ (hQp q hq).1) hne
      have h₂ : log |((s - h : ℤ) : ℝ)| ≤ log (2 * C) + L := by
        calc log |((s - h : ℤ) : ℝ)| ≤ log (C * u + B) :=
              log_le_log (abs_pos.mpr (by exact_mod_cast hne)) habs'
          _ ≤ log (2 * C * u) := log_le_log (by positivity) (by
              have : u ≤ C * u := le_mul_of_one_le_left hu0.le hC
              linarith)
          _ = log (2 * C) + L := log_mul (by positivity) hu0.ne'
      have h₄ : (0 : ℝ) ≤ #{q ∈ Q | ((q : ℕ) : ℤ) ∣ s - h} := Nat.cast_nonneg _
      have h₃ := mul_le_mul_of_nonneg_left log_two_gt_d9.le h₄
      have h₅ : 0 ≤ log (2 * C) := log_nonneg (by linarith)
      linarith
    calc (#{q ∈ Q | ∃ h ∈ H, ((q : ℕ) : ℤ) ∣ s - h} : ℝ)
        ≤ ∑ h ∈ H, (#{q ∈ Q | ((q : ℕ) : ℤ) ∣ s - h} : ℝ) := by
          exact_mod_cast (card_le_card hsub).trans card_biUnion_le
      _ ≤ ∑ h ∈ H, 2 * (log (2 * C) + L) := sum_le_sum heach
      _ = r * (2 * (log (2 * C) + L)) := by rw [sum_const, nsmul_eq_mul]
      _ ≤ L ^ a / 2 := by linarith
  obtain ⟨c, hc_hole, hc_card⟩ := exists_middle_residues H Q hQp S₁ hbad
  set S₂ := {s ∈ S₁ | ∀ q ∈ Q, ¬ (q : ℤ) ∣ c q + s} with hS₂
  have hS₂card : (#S₂ : ℝ) ≤ u / L / 8 := by
    have hQ1 : 0 ≤ ∏ q ∈ Q, (1 - 1 / (q : ℝ)) := prod_nonneg fun q hq ↦ by
      have : (1 : ℝ) ≤ q := by exact_mod_cast (hQp q hq).1.one_lt.le
      rw [sub_nonneg, div_le_one (by linarith)]
      exact this
    calc (#S₂ : ℝ) ≤ 2 * #S₁ * ∏ q ∈ Q, (1 - 1 / (q : ℝ)) := hc_card
      _ ≤ 2 * (D * (u / L)) * (16 * D)⁻¹ := by gcongr
      _ = u / L / 8 := by field_simp; ring
  -- the cleanup stage
  have hRu : ∀ q ∈ R, u / 4 < q := fun q hq ↦
    (Nat.floor_lt (by positivity)).mp (mem_Ioc.mp (mem_filter.mp hq).1).1
  have hRhole : ∀ q ∈ R, ∀ h ∈ H, ¬ (q : ℤ) ∣ h := by
    intro q hq h hh hd
    have h₁ := Nat.le_of_dvd (hH h hh) (Int.natCast_dvd_natCast.mp hd)
    have h₂ : (q : ℝ) ≤ B := by exact_mod_cast h₁.trans (hB h hh)
    linarith [hRu q hq]
  have hRbad : ∀ s ∈ S₂, #{q ∈ R | ∃ h ∈ H, ((q : ℕ) : ℤ) ∣ s - h} ≤ r := by
    intro s hs
    have hs₁ := (mem_filter.mp hs).1
    have hsub : {q ∈ R | ∃ h ∈ H, ((q : ℕ) : ℤ) ∣ s - h} ⊆
        H.biUnion fun h ↦ {q ∈ R | ((q : ℕ) : ℤ) ∣ s - h} := by
      intro q hq
      simp only [mem_filter, mem_biUnion] at hq ⊢
      obtain ⟨hqR, h, hh, hd⟩ := hq
      exact ⟨h, hh, hqR, hd⟩
    refine (card_le_card hsub).trans (card_biUnion_le.trans ?_)
    calc ∑ h ∈ H, #{q ∈ R | ((q : ℕ) : ℤ) ∣ s - h} ≤ ∑ h ∈ H, 1 :=
          sum_le_sum fun h hh ↦ by
            obtain ⟨hne, habs'⟩ := habs s hs₁ h hh
            exact card_filter_dvd_le_one_of_abs_le_sq (fun q hq ↦ (mem_filter.mp hq).2)
              (by positivity) hRu hne (habs'.trans hquad)
      _ = r := by rw [sum_const, smul_eq_mul, mul_one]
  have hSR : #S₂ + r ≤ #R := by
    have h₁ : (r : ℝ) ≤ u / L / 8 := by
      rw [div_div, le_div_iff₀ (by positivity)]
      linarith
    have h₂ : u / (4 * L) = u / L / 8 + u / L / 8 := by ring
    have : ((#S₂ + r : ℕ) : ℝ) ≤ (#R : ℕ) := by
      rw [Nat.cast_add]
      linarith only [hS₂card, h₁, hRcard, h₂]
    exact Nat.cast_le.mp this
  obtain ⟨e, he_hole, he_cov⟩ := exists_cleanup_residues H r S₂ R hRhole hRbad hSR
  -- assemble the residues: `c` on `[L^a, y]`, `0` on `(y, u/4]`, `e` on `(u/4, u]`
  refine exists_cover_of_residues
    (fun q ↦ if (q : ℝ) ≤ y then c q else if (q : ℝ) ≤ u / 4 then 0 else e q) ?_ ?_
  · intro q hq hqu hqa h hh
    split_ifs with h₁ h₂
    · exact hc_hole q (mem_filter.mpr ⟨mem_Iic.mpr (Nat.le_floor h₁), hq, hqa⟩) h hh
    · rw [zero_add]
      intro hd
      have h₃ := Nat.le_of_dvd (hH h hh) (Int.natCast_dvd_natCast.mp hd)
      have h₄ : (q : ℝ) ≤ B := by exact_mod_cast h₃.trans (hB h hh)
      linarith [not_le.mp h₁]
    · exact he_hole q (mem_filter.mpr ⟨mem_Ioc.mpr ⟨(Nat.floor_lt (by positivity)).mpr
        (not_le.mp h₂), hqu⟩, hq⟩) h hh
  · intro s hs₁ hs₂ hs₃
    have hsW : s ∈ Icc (-⌊C * u⌋) (B : ℤ) := by
      refine mem_Icc.mpr ⟨?_, hs₂⟩
      rw [neg_le]
      exact Int.le_floor.mpr (by rw [Int.cast_neg]; linarith only [hs₁])
    by_cases hk : ∀ q : ℕ, q.Prime → y < q → (q : ℝ) ≤ u / 4 → ¬ (q : ℤ) ∣ s
    · have hsS₁ : s ∈ S₁ := mem_filter.mpr ⟨hsW, hs₃, hk⟩
      by_cases hk₂ : ∀ q ∈ Q, ¬ (q : ℤ) ∣ c q + s
      · -- a cleanup prime covers `s`
        obtain ⟨q, hqR, hqd⟩ := he_cov s (mem_filter.mpr ⟨hsS₁, hk₂⟩)
        have hq₄ := hRu q hqR
        have hqR' := mem_filter.mp hqR
        refine ⟨q, hqR'.2, (mem_Ioc.mp hqR'.1).2, hya.trans (hyu.le.trans hq₄.le), ?_⟩
        rwa [ite_eq_right (not_le.mpr (hyu.trans hq₄)), ite_eq_right (not_le.mpr hq₄)]
      · -- a middle prime covers `s`
        simp only [not_forall, not_not] at hk₂
        obtain ⟨q, hqQ, hqd⟩ := hk₂
        have hqQ' := mem_filter.mp hqQ
        have hqy : (q : ℝ) ≤ y := (Nat.le_floor_iff hy0).mp (mem_Iic.mp hqQ'.1)
        refine ⟨q, hqQ'.2.1, Nat.le_floor (hqy.trans (hyu.le.trans hu4)), hqQ'.2.2, ?_⟩
        rwa [ite_eq_left hqy]
    · -- a prime in `(y, u/4]` divides `s`
      simp only [not_forall, not_not] at hk
      obtain ⟨q, hq, hyq, hqu, hqd⟩ := hk
      refine ⟨q, hq, Nat.le_floor (hqu.trans hu4), hya.trans hyq.le, ?_⟩
      rwa [ite_eq_right (not_le.mpr hyq), ite_eq_left hqu, zero_add]

/-- For all large `u` some `z` keeps every `z + h` (`h ∈ H`) coprime to
`coverModulus a u` and covers every other `z + s` with `−C u ≤ s ≤ B`. -/
theorem eventually_exists_protected_cover (H : Finset ℕ) (hH : ∀ h ∈ H, 0 < h) (B : ℕ)
    (hB : ∀ h ∈ H, h ≤ B) {a : ℕ} (ha : 2 ≤ a) (C : ℝ) :
    ∀ᶠ u : ℝ in Filter.atTop, ∃ z : ℤ,
      (∀ h ∈ H, IsCoprime (z + h) (coverModulus a u : ℤ)) ∧
      ∀ s : ℤ, -(C * u) ≤ s → s ≤ B → (∀ h ∈ H, s ≠ h) →
        ¬ IsCoprime (z + s) (coverModulus a u : ℤ) := by
  -- a larger `C` covers more
  wlog hC : 1 ≤ C generalizing C with h
  · filter_upwards [h (max C 1) (le_max_right _ _), eventually_ge_atTop 0] with
      u ⟨z, hz₁, hz₂⟩ hu
    refine ⟨z, hz₁, fun s hs₁ hs₂ hs₃ ↦ hz₂ s ?_ hs₂ hs₃⟩
    have : C * u ≤ max C 1 * u := mul_le_mul_of_nonneg_right (le_max_left _ _) hu
    linarith
  set r := #H with hr
  set D : ℝ := 16 * C ^ 2 + 2 with hD
  have hD0 : 0 < D := by positivity
  set T : ℝ := log (16 * D) with hT
  set I : ℕ := ⌈50 * T⌉₊ with hI
  set A : ℕ := 2 * a * 2 ^ I with hA
  have hA1 : 1 ≤ A := Nat.mul_pos (Nat.mul_pos two_pos (by omega)) (by positivity)
  have haA : a ≤ A :=
    calc a ≤ 2 * a := by omega
      _ ≤ 2 * a * 2 ^ I := Nat.le_mul_of_pos_right _ (by positivity)
  obtain ⟨X₀, -, hX₀⟩ := exists_le_sum_Ioc_pow
  obtain ⟨m₀, hm₀⟩ := exists_card_primes_le
  have hlog2C : 0 ≤ log (2 * C) := log_nonneg (by linarith)
  filter_upwards [tendsto_log_atTop.eventually
      (eventually_ge_atTop (2 + B + r + X₀ + 4 * r * (1 + log (2 * C)))),
    eventually_ge_atTop (16 * (C + B + m₀ + 1)),
    eventually_card_smoothNumbersUpTo_le hA1 hC, eventually_div_log_le_card_primes,
    eventually_mul_log_pow_le_self (B + 1) 1, eventually_mul_log_pow_le_self (8 * r) 1,
    eventually_mul_log_pow_le_self 8 A] with u hLK hu hsmooth hRcard hBL hrL hyL
  set L := log u with hL_def
  rw [pow_one] at hBL hrL
  have hu16 : 16 ≤ u := by nlinarith [Nat.cast_nonneg (α := ℝ) B, Nat.cast_nonneg (α := ℝ) m₀]
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg _
  have hX₀0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hB0 : (0 : ℝ) ≤ B := Nat.cast_nonneg _
  have hK : 0 ≤ 4 * r * (1 + log (2 * C)) := by positivity
  have hL2 : 2 ≤ L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have hL0 : 0 < L := by linarith
  have hLLa : L ≤ L ^ a := le_self_pow₀ hL1 (by omega)
  have hLa : L ^ 2 ≤ L ^ a := pow_le_pow_right₀ hL1 ha
  have hLbad : 4 * r * (log (2 * C) + L) ≤ L ^ a := by
    have h₁ : 4 * r * log (2 * C) ≤ 4 * r * log (2 * C) * L :=
      le_mul_of_one_le_right (by positivity) hL1
    have h₂ := mul_le_mul_of_nonneg_left hLK hL0.le
    nlinarith
  have hum₀ : m₀ ≤ ⌊u / 4⌋₊ := Nat.le_floor (by
    have : (0 : ℝ) ≤ C + B + 1 := by positivity
    linarith)
  have hquad : C * u + B ≤ (u / 4) ^ 2 := by nlinarith
  have hLy : L ≤ L ^ A := le_self_pow₀ hL1 (by omega)
  have hyu : L ^ A < u / 4 := by
    have : 0 < L ^ A := pow_pos hL0 A
    linarith
  refine exists_cover_of_le hH hB hC hD0 hu16 hL2 (by linarith) hLbad (by linarith)
    (pow_le_pow_right₀ hL1 haA) hyu hquad ?_ ?_ hRcard (by linarith)
  · -- the first stage leaves at most `D u / L` survivors
    refine (card_survivors_le (B := B) hC hu16 (by positivity) hm₀ hum₀ hsmooth ?_).trans_eq
      (by rw [hD])
    rw [le_div_iff₀ hL0]
    linarith
  · -- the middle primes have `∑ 1/q ≥ T`
    refine (prod_one_sub_inv_le hX₀ (Nat.le_ceil _) hL2 (by linarith) (by omega)).trans_eq ?_
    rw [exp_neg, hT, exp_log (by positivity)]

end Erdos420
