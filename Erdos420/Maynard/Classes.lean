import Erdos420.Maynard.Modulus
import PrimeGapsTheory.Endgame.MainProp

/-!
# Residue classes for the forms `a₀ + M t + b_i`

The sieve of `vendor/PrimeGapsLib` runs over the `n ∈ (N', 2N']` in one class
`n ≡ v (mod Q)`. With `N' = a₀ + M (N − 1)` and `M ∣ Q`, the `n ≡ a₀ (mod M)` in
`(N', 2N']` are the `a₀ + M t` with `t ∈ [N, 2N)` and `a₀ + M t ∈ (N', 2N']`, and
they split into the classes `v (mod Q)` above `a₀ (mod M)`. Only the classes at which
every `v + b_i` is coprime to `Q` carry sieve weight.

For `Q = M W'` with `W'` squarefree and coprime to `M`, these classes correspond to the
`v (mod W')` with every `v + b_i` coprime to `W'`, whose number is
`∏_{p ∣ W'} (p − ν_p)` with `ν_p` the number of classes of the `b_i` mod `p`. For an
admissible tuple this is at least a constant times `W' (φ(W') / W')^k`:
the factors with `p ≤ 2k` are at least `1/p`, and the others at least
`(1 − k/p)(1 − 1/p)^{−k} ≥ 1 − k²/p²`.

## Main results

* `Erdos420.isAdmissible_factorialTuple`: `b_i = (i + 1) k!` is admissible.
* `Erdos420.sum_Ico_eq_sum_validClasses`: the regrouping of a sum over `t` by classes.
* `Erdos420.exists_le_card_validClasses`: the number of classes is
  `≫ W' (φ(W') / W')^k`.
-/

namespace Erdos420

open Finset

/-- `b_i = (i + 1) k!` is an admissible `k`-tuple: it misses `1 (mod p)` for `p ≤ k`, and has
fewer than `p` classes mod `p > k`. -/
lemma isAdmissible_factorialTuple (k : ℕ) :
    GPYSieveS1.IsAdmissible (fun i : Fin k ↦ (i.val + 1) * k.factorial) := by
  refine ⟨fun i j hij ↦ (Nat.mul_lt_mul_right (Nat.factorial_pos k)).mpr
    (Nat.succ_lt_succ (Fin.lt_def.mp hij)), ?_⟩
  rw [Finset.admissible_iff_forall_prime_exists_lt_mod_ne]
  intro p hp
  by_cases hpk : p ≤ k
  · -- every `b_i` is `0 (mod p)`
    refine ⟨1, hp.one_lt, fun x hx ↦ ?_⟩
    obtain ⟨i, -, rfl⟩ := mem_image.mp hx
    rw [Nat.mul_mod, Nat.mod_eq_zero_of_dvd (Nat.dvd_factorial hp.pos hpk), mul_zero,
      Nat.zero_mod]
    exact zero_ne_one
  · refine Finset.exists_lt_forall_mod_ne_of_card_lt (card_image_le.trans_lt ?_)
    rw [card_univ, Fintype.card_fin]
    omega

/-- The residues `v < Q` with `v ≡ a₀ (mod M)` at which every `v + b_i` is coprime to `Q`. -/
def validClasses (Q M a₀ : ℕ) {k : ℕ} (b : Fin k → ℕ) : Finset ℕ :=
  (range Q).filter fun v ↦ v % M = a₀ ∧ ∀ i, (v + b i).Coprime Q

/-- A valid class is a valid residue `w₀ (mod Q)` for the sieve. -/
lemma gcd_eq_one_of_mem_validClasses {Q M a₀ k v : ℕ} {b : Fin k → ℕ}
    (hv : v ∈ validClasses Q M a₀ b) (i : Fin k) :
    (((v : ZMod Q).val : ℤ) + b i).gcd Q = 1 := by
  rw [validClasses, mem_filter, mem_range] at hv
  rw [ZMod.val_cast_of_lt hv.1, ← Nat.cast_add, Int.gcd_natCast_natCast]
  exact hv.2.2 i

/-- A sum over `t ∈ [N, 2N)` of a function of `a₀ + M t`, cut off to `a₀ + M t ∈ (N', 2N']`
with every `a₀ + M t + b_i` coprime to `Q`, is the sum over the valid classes `v (mod Q)` of
the sums over `n ∈ (N', 2N']` with `n ≡ v (mod Q)`. -/
lemma sum_Ico_eq_sum_validClasses {k : ℕ} (b : Fin k → ℕ) {M a₀ N N' Q : ℕ} (hMQ : M ∣ Q)
    (hQ : 0 < Q) (ha₀ : a₀ < M) (hN : 1 ≤ N) (hN' : N' = a₀ + M * (N - 1)) (f : ℕ → ℝ) :
    ∑ t ∈ Ico N (2 * N), (if N' < a₀ + M * t ∧ a₀ + M * t ≤ 2 * N' ∧
        ∀ i, (a₀ + M * t + b i).Coprime Q then f (a₀ + M * t) else 0) =
      ∑ v ∈ validClasses Q M a₀ b, ∑ n ∈ Ioc N' (2 * N') with ((n : ℕ) : ZMod Q) = v, f n := by
  have hM : 0 < M := by omega
  -- coprimality to `Q` depends only on the residue mod `Q`
  have hcop : ∀ x c, (x % Q + c).Coprime Q ↔ (x + c).Coprime Q := fun x c ↦ by
    conv_rhs => rw [← Nat.mod_add_div x Q]
    rw [show x % Q + Q * (x / Q) + c = x % Q + c + Q * (x / Q) by ring,
      Nat.coprime_add_mul_left_left]
  set S := (Ioc N' (2 * N')).filter fun n ↦ n % Q ∈ validClasses Q M a₀ b with hS
  -- the right side is the sum over the `n ∈ (N', 2N']` in a valid class
  have hR : ∑ v ∈ validClasses Q M a₀ b, ∑ n ∈ Ioc N' (2 * N') with ((n : ℕ) : ZMod Q) = v, f n =
      ∑ n ∈ S, f n := by
    rw [← sum_fiberwise_of_maps_to (s := S) (t := validClasses Q M a₀ b) (g := fun n ↦ n % Q)
      fun n hn ↦ (mem_filter.mp hn).2]
    refine sum_congr rfl fun v hv ↦ ?_
    have hvQ : v < Q := mem_range.mp (mem_filter.mp hv).1
    rw [hS, filter_filter]
    refine sum_congr (filter_congr fun n _ ↦ ?_) fun _ _ ↦ rfl
    rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hvQ]
    constructor
    · rintro h
      exact ⟨h ▸ hv, h⟩
    · exact fun h ↦ h.2
  rw [hR, ← sum_filter]
  refine sum_nbij' (fun t ↦ a₀ + M * t) (fun n ↦ n / M) ?_ ?_ ?_ ?_ fun _ _ ↦ rfl
  · -- `t ↦ a₀ + M t` lands in a valid class
    intro t ht
    rw [mem_filter] at ht ⊢
    obtain ⟨-, h₁, h₂, h₃⟩ := ht
    refine ⟨mem_Ioc.mpr ⟨h₁, h₂⟩, ?_⟩
    rw [validClasses, mem_filter, mem_range, Nat.mod_mod_of_dvd _ hMQ, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt ha₀]
    exact ⟨Nat.mod_lt _ hQ, rfl, fun i ↦ (hcop _ _).mpr (h₃ i)⟩
  · -- `n ↦ n / M` lands in `[N, 2N)`
    intro n hn
    rw [mem_filter, mem_Ioc] at hn
    obtain ⟨⟨h₁, h₂⟩, hv⟩ := hn
    rw [validClasses, mem_filter, Nat.mod_mod_of_dvd _ hMQ] at hv
    have hn : a₀ + M * (n / M) = n := by
      rw [← hv.2.1]
      exact Nat.mod_add_div n M
    rw [mem_filter, mem_Ico, hn]
    refine ⟨⟨?_, ?_⟩, h₁, h₂, fun i ↦ (hcop _ _).mp (hv.2.2 i)⟩
    · have h : M * (N - 1) < M * (n / M) := by omega
      have := Nat.lt_of_mul_lt_mul_left h
      omega
    · have h₃ : M * (2 * N - 1) = M + 2 * (M * (N - 1)) := by
        rw [show 2 * N - 1 = 2 * (N - 1) + 1 by omega, Nat.mul_add, Nat.mul_one, mul_left_comm]
        ring
      have h : M * (n / M) < M * (2 * N - 1) := by omega
      have := Nat.lt_of_mul_lt_mul_left h
      omega
  · intro t _
    rw [Nat.add_mul_div_left _ _ hM, Nat.div_eq_of_lt ha₀, zero_add]
  · intro n hn
    rw [mem_filter, validClasses, mem_filter, Nat.mod_mod_of_dvd _ hMQ] at hn
    rw [← hn.2.2.1]
    exact Nat.mod_add_div n M

/-- The number of classes `v (mod n)` at which every `v + b_i` is a unit. -/
noncomputable def unitShiftCount {k : ℕ} (b : Fin k → ℕ) (n : ℕ) : ℕ :=
  Nat.card {v : ZMod n // ∀ i, IsUnit (v + b i)}

/-- `unitShiftCount` is multiplicative, by the Chinese remainder theorem. -/
lemma unitShiftCount_mul {k : ℕ} (b : Fin k → ℕ) {m n : ℕ} (h : m.Coprime n) :
    unitShiftCount b (m * n) = unitShiftCount b m * unitShiftCount b n := by
  rw [unitShiftCount, unitShiftCount, unitShiftCount, ← Nat.card_prod]
  set e := ZMod.chineseRemainder h
  refine Nat.card_congr ((e.toEquiv.subtypeEquiv (q := fun c : ZMod m × ZMod n ↦
    (∀ i, IsUnit (c.1 + (b i : ZMod m))) ∧ ∀ i, IsUnit (c.2 + (b i : ZMod n))) fun v ↦ ?_).trans
      (Equiv.subtypeProdEquivProd (p := fun x : ZMod m ↦ ∀ i, IsUnit (x + (b i : ZMod m)))
        (q := fun y : ZMod n ↦ ∀ i, IsUnit (y + (b i : ZMod n)))))
  rw [← forall_and]
  refine forall_congr' fun i ↦ ?_
  rw [← isUnit_map_iff e, map_add, map_natCast, Prod.isUnit_iff]
  rfl

/-- On a product of distinct primes, `unitShiftCount` is the product over the primes. -/
lemma unitShiftCount_prod {k : ℕ} (b : Fin k → ℕ) (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    unitShiftCount b (∏ p ∈ s, p) = ∏ p ∈ s, unitShiftCount b p := by
  induction s using Finset.induction_on with
  | empty =>
    rw [prod_empty, prod_empty, unitShiftCount]
    exact Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, ⟨⟨0, fun i ↦ isUnit_of_subsingleton _⟩⟩⟩
  | insert p s hp ih =>
    have hp' := hs p (mem_insert_self p s)
    have hs' := fun q hq ↦ hs q (mem_insert_of_mem hq)
    rw [prod_insert hp, prod_insert hp, unitShiftCount_mul, ih hs']
    exact Nat.Coprime.prod_right fun q hq ↦ (Nat.coprime_primes hp' (hs' q hq)).mpr
      fun h ↦ hp (h ▸ hq)

/-- For a prime `p` and an admissible tuple, `1 ≤ unitShiftCount b p` and
`p − k ≤ unitShiftCount b p`. -/
lemma le_unitShiftCount_prime {k : ℕ} (b : Fin k → ℕ) (hb : (univ.image b).Admissible) {p : ℕ}
    (hp : p.Prime) : 1 ≤ unitShiftCount b p ∧ (p : ℝ) - k ≤ unitShiftCount b p := by
  have := Fact.mk hp
  rw [unitShiftCount, Nat.card_eq_fintype_card, Fintype.card_subtype]
  constructor
  · -- the class `−a` missed by the `b_i`
    obtain ⟨a, ha⟩ := hb p hp
    refine card_pos.mpr ⟨-(a : ZMod p), mem_filter.mpr ⟨mem_univ _, fun i ↦ ?_⟩⟩
    refine isUnit_iff_ne_zero.mpr fun h ↦ ha (b i) (mem_image_of_mem b (mem_univ i)) ?_
    rw [← ZMod.natCast_eq_natCast_iff]
    linear_combination h
  · -- the other classes are among the `−b_i`
    have hsub : univ.filter (fun y : ZMod p ↦ ¬∀ i, IsUnit (y + b i)) ⊆
        univ.image fun i ↦ -(b i : ZMod p) := fun y hy ↦ by
      rw [mem_filter] at hy
      push Not at hy
      obtain ⟨i, hi⟩ := hy.2
      rw [isUnit_iff_ne_zero, not_not] at hi
      exact mem_image.mpr ⟨i, mem_univ i, by linear_combination -hi⟩
    have h₁ := card_filter_add_card_filter_not (s := (univ : Finset (ZMod p)))
      (fun y ↦ ∀ i, IsUnit (y + b i))
    have h₂ := (card_le_card hsub).trans card_image_le
    rw [card_univ, ZMod.card] at h₁
    rw [card_univ, Fintype.card_fin] at h₂
    have h₃ : (p : ℝ) ≤ #(univ.filter fun y : ZMod p ↦ ∀ i, IsUnit (y + b i)) + k := by
      exact_mod_cast (by omega : p ≤ #(univ.filter fun y : ZMod p ↦ ∀ i, IsUnit (y + b i)) + k)
    linarith

/-- The valid classes mod `M W` are counted by `unitShiftCount b W`. -/
lemma card_validClasses {k : ℕ} (b : Fin k → ℕ) {M a₀ W : ℕ} (hM : 0 < M) (hMW : M.Coprime W)
    (hW : 0 < W) (ha₀ : a₀ < M) (hcop : ∀ i, (a₀ + b i).Coprime M) :
    #(validClasses (M * W) M a₀ b) = unitShiftCount b W := by
  have := NeZero.mk hW.ne'
  set u := ZMod.unitOfCoprime M hMW with hu
  have hu' : ((u : ZMod W)) = M := ZMod.coe_unitOfCoprime M hMW
  rw [unitShiftCount, Nat.card_eq_fintype_card, Fintype.card_subtype]
  -- `a₀ + M x` with `x = u⁻¹ (v − a₀)` is `v (mod W)`
  have hcast : ∀ v : ZMod W, ((a₀ + M * (↑u⁻¹ * (v - a₀)).val : ℕ) : ZMod W) = v := fun v ↦ by
    push_cast
    rw [ZMod.natCast_zmod_val, ← hu', Units.mul_inv_cancel_left]
    ring
  -- the coprimality to `M` of `a₀ + M x + b_i`
  have hcopM : ∀ x i, (a₀ + M * x + b i).Coprime M := fun x i ↦ by
    rw [show a₀ + M * x + b i = a₀ + b i + M * x by ring, Nat.coprime_add_mul_left_left]
    exact hcop i
  refine card_nbij' (fun n ↦ (n : ZMod W)) (fun v ↦ a₀ + M * (↑u⁻¹ * (v - a₀)).val) ?_ ?_ ?_ ?_
  · intro n hn
    rw [mem_coe, validClasses, mem_filter] at hn
    rw [mem_coe]
    refine mem_filter.mpr ⟨mem_univ _, fun i ↦ ?_⟩
    rw [← Nat.cast_add, ZMod.isUnit_iff_coprime]
    exact (hn.2.2 i).coprime_mul_left_right
  · intro v hv
    rw [mem_coe, mem_filter] at hv
    rw [mem_coe]
    beta_reduce
    have hx := ZMod.val_lt (↑u⁻¹ * (v - a₀) : ZMod W)
    have hMx : M * ((↑u⁻¹ * (v - a₀) : ZMod W).val + 1) ≤ M * W := Nat.mul_le_mul_left M hx
    rw [validClasses, mem_filter, mem_range, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha₀]
    refine ⟨by rw [Nat.mul_succ] at hMx; omega, rfl, fun i ↦ (hcopM _ i).mul_right ?_⟩
    rw [← ZMod.isUnit_iff_coprime, Nat.cast_add, hcast]
    exact hv.2 i
  · intro n hn
    rw [mem_coe, validClasses, mem_filter, mem_range] at hn
    have hn' : a₀ + M * (n / M) = n := by
      rw [← hn.2.1]
      exact Nat.mod_add_div n M
    have hj : n / M < W := (Nat.div_lt_iff_lt_mul hM).mpr (by rw [mul_comm]; exact hn.1)
    have hx : (↑u⁻¹ * ((n : ZMod W) - a₀)).val = n / M := by
      conv_lhs => rw [← hn']
      rw [Nat.cast_add, add_sub_cancel_left, Nat.cast_mul, ← hu', ← mul_assoc, Units.inv_mul,
        one_mul, ZMod.val_cast_of_lt hj]
    change a₀ + M * (↑u⁻¹ * ((n : ZMod W) - a₀)).val = n
    rw [hx, hn']
  · intro v _
    exact hcast v

/-- `∏ (1 − f_i) ≥ 1 − ∑ f_i` for `0 ≤ f_i ≤ 1`. -/
private lemma one_sub_sum_le_prod_one_sub (s : Finset ℕ) (f : ℕ → ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i ∧ f i ≤ 1) :
    1 - ∑ i ∈ s, f i ≤ ∏ i ∈ s, (1 - f i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [sum_insert ha, prod_insert ha]
    have h₁ := ih fun i hi ↦ hf i (mem_insert_of_mem hi)
    obtain ⟨h₂, h₃⟩ := hf a (mem_insert_self a s)
    have h₄ : 0 ≤ ∑ i ∈ s, f i := sum_nonneg fun i hi ↦ (hf i (mem_insert_of_mem hi)).1
    nlinarith

/-- The number of valid classes mod `M W'` is at least a constant times `W' (φ(W') / W')^k`,
for an admissible tuple `b`. -/
theorem exists_le_card_validClasses {k : ℕ} (b : Fin k → ℕ) (hb : (univ.image b).Admissible) :
    ∃ c > (0 : ℝ), ∀ M a₀ W : ℕ, 0 < M → M.Coprime W → Squarefree W → a₀ < M →
      (∀ i, (a₀ + b i).Coprime M) →
        c * W ≤ #(validClasses (M * W) M a₀ b) * ((W : ℝ) / W.totient) ^ k := by
  -- the primes `p ≤ T₀` contribute at least `1/p ≥ 1/T₀` each, and the larger ones at least
  -- `1 − k²/p²`
  set T₀ : ℕ := 4 * k ^ 2 + 1 with hT₀
  have hT₀₁ : (1 : ℝ) ≤ T₀ := by exact_mod_cast (by omega : 1 ≤ T₀)
  refine ⟨(1 / (T₀ : ℝ)) ^ (T₀ + 1) / 2, by positivity, fun M a₀ W hM hMW hW ha₀ hcop ↦ ?_⟩
  set P := W.primeFactors with hP
  have hPp : ∀ p ∈ P, p.Prime := fun p hp ↦ Nat.prime_of_mem_primeFactors hp
  set g : ℕ → ℝ := fun p ↦ unitShiftCount b p * ((p : ℝ) / (p - 1)) ^ k / p with hg
  have hp2 : ∀ p ∈ P, (2 : ℝ) ≤ p := fun p hp ↦ by exact_mod_cast (hPp p hp).two_le
  -- `g p ≥ 1/p`
  have hg₁ : ∀ p ∈ P, 1 / (p : ℝ) ≤ g p := fun p hp ↦ by
    have h₁ : (1 : ℝ) ≤ unitShiftCount b p := by
      exact_mod_cast (le_unitShiftCount_prime b hb (hPp p hp)).1
    have h₂ : (1 : ℝ) ≤ ((p : ℝ) / (p - 1)) ^ k := one_le_pow₀ (by
      have := hp2 p hp
      rw [one_le_div (by linarith)]
      linarith)
    simp only [hg]
    have := hp2 p hp
    exact div_le_div_of_nonneg_right (by nlinarith) (by linarith)
  -- `g p ≥ 1 − k²/p²` for `p > T₀`
  have hg₂ : ∀ p ∈ P, T₀ < p → 1 - (k : ℝ) ^ 2 / (p : ℝ) ^ 2 ≤ g p := fun p hp hpT ↦ by
    have hpT' : (T₀ : ℝ) < p := by exact_mod_cast hpT
    have hp₀ : (0 : ℝ) < p := by linarith
    have hkp : (k : ℝ) ≤ p := by
      have : (k : ℝ) ≤ T₀ := by
        rw [hT₀]
        push_cast
        nlinarith
      linarith
    have h₁ := (le_unitShiftCount_prime b hb (hPp p hp)).2
    -- Bernoulli: `(p / (p − 1))^k = (1 + 1/(p − 1))^k ≥ 1 + k/(p − 1) ≥ 1 + k/p`
    have h₂ : 1 + (k : ℝ) / p ≤ ((p : ℝ) / (p - 1)) ^ k := by
      have hp1 : (0 : ℝ) < p - 1 := by linarith [hp2 p hp]
      have hB := one_add_mul_le_pow (show (-2 : ℝ) ≤ 1 / (p - 1) by
        linarith [one_div_nonneg.mpr hp1.le]) k
      have h₃ : (1 : ℝ) + 1 / (p - 1) = p / (p - 1) := by field_simp; ring
      have h₄ : (k : ℝ) / p ≤ k * (1 / (p - 1)) := by
        rw [mul_one_div]
        exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) hp1 (by linarith)
      rw [← h₃]
      linarith
    have h₃ : 0 ≤ 1 - (k : ℝ) / p := by
      rw [sub_nonneg, div_le_one hp₀]
      exact hkp
    have h₄ : (0 : ℝ) ≤ ((p : ℝ) / (p - 1)) ^ k := le_trans (by positivity) h₂
    calc 1 - (k : ℝ) ^ 2 / (p : ℝ) ^ 2 = (1 - (k : ℝ) / p) * (1 + k / p) := by ring
      _ ≤ (1 - (k : ℝ) / p) * ((p : ℝ) / (p - 1)) ^ k := by gcongr
      _ = ((p : ℝ) - k) * ((p : ℝ) / (p - 1)) ^ k / p := by field_simp
      _ ≤ g p := by
          simp only [hg]
          gcongr
  -- the large primes: `∏ (1 − k²/p²) ≥ 1 − k² ∑_{n > T₀} 1/n² ≥ 1/2`
  have hlarge : 1 / 2 ≤ ∏ p ∈ P with T₀ < p, g p := by
    set L := P.filter (T₀ < ·) with hL
    have hLT : ∀ p ∈ L, T₀ < p := fun p hp ↦ by
      rw [hL, mem_filter] at hp
      exact hp.2
    have hsum : ∑ p ∈ L, (k : ℝ) ^ 2 / (p : ℝ) ^ 2 ≤ 1 / 2 := by
      calc ∑ p ∈ L, (k : ℝ) ^ 2 / (p : ℝ) ^ 2 = (k : ℝ) ^ 2 * ∑ p ∈ L, 1 / (p : ℝ) ^ 2 := by
            rw [mul_sum]
            simp_rw [mul_one_div]
        _ ≤ (k : ℝ) ^ 2 * (2 / (T₀ + 1)) := by gcongr; exact sum_one_div_sq_le_of_lt hLT
        _ ≤ 1 / 2 := by
            rw [hT₀]
            push_cast
            rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
            nlinarith
    have hprod := one_sub_sum_le_prod_one_sub L (fun p ↦ (k : ℝ) ^ 2 / (p : ℝ) ^ 2) fun p hp ↦ by
      rw [hL, mem_filter] at hp
      have hpT' : (T₀ : ℝ) < p := by exact_mod_cast hp.2
      refine ⟨by positivity, ?_⟩
      rw [div_le_one (by nlinarith)]
      have : (k : ℝ) ≤ T₀ := by
        rw [hT₀]
        push_cast
        nlinarith
      nlinarith
    calc (1 : ℝ) / 2 ≤ 1 - ∑ p ∈ L, (k : ℝ) ^ 2 / (p : ℝ) ^ 2 := by linarith
      _ ≤ ∏ p ∈ L, (1 - (k : ℝ) ^ 2 / (p : ℝ) ^ 2) := hprod
      _ ≤ ∏ p ∈ L, g p := prod_le_prod₀ (fun p hp ↦ ?_) fun p hp ↦ by
          rw [hL, mem_filter] at hp
          exact hg₂ p hp.1 hp.2
    rw [hL, mem_filter] at hp
    have hpT' : (T₀ : ℝ) < p := by exact_mod_cast hp.2
    have : (k : ℝ) ≤ T₀ := by
      rw [hT₀]
      push_cast
      nlinarith
    rw [sub_nonneg, div_le_one (by nlinarith)]
    nlinarith
  -- the small primes: `∏ g ≥ (1/T₀)^{T₀ + 1}`
  have hsmall : (1 / (T₀ : ℝ)) ^ (T₀ + 1) ≤ ∏ p ∈ P with ¬T₀ < p, g p := by
    have hcard : #(P.filter (¬T₀ < ·)) ≤ T₀ + 1 := by
      calc #(P.filter (¬T₀ < ·)) ≤ #(range (T₀ + 1)) := card_le_card fun p hp ↦ by
            rw [mem_filter] at hp
            exact mem_range.mpr (by omega)
        _ = T₀ + 1 := card_range _
    calc (1 / (T₀ : ℝ)) ^ (T₀ + 1) ≤ (1 / (T₀ : ℝ)) ^ #(P.filter (¬T₀ < ·)) :=
          pow_le_pow_of_le_one (by positivity) (div_le_one_of_le₀ hT₀₁ (by positivity)) hcard
      _ = ∏ p ∈ P with ¬T₀ < p, 1 / (T₀ : ℝ) := (prod_const _).symm
      _ ≤ ∏ p ∈ P with ¬T₀ < p, g p := prod_le_prod₀ (fun _ _ ↦ by positivity) fun p hp ↦ by
          rw [mem_filter] at hp
          have hpT : (p : ℝ) ≤ T₀ := by exact_mod_cast not_lt.mp hp.2
          exact (div_le_div_of_nonneg_left zero_le_one (by linarith [hp2 p hp.1]) hpT).trans
            (hg₁ p hp.1)
  have hgP : (1 / (T₀ : ℝ)) ^ (T₀ + 1) / 2 ≤ ∏ p ∈ P, g p := by
    rw [← prod_filter_mul_prod_filter_not P (T₀ < ·)]
    calc (1 / (T₀ : ℝ)) ^ (T₀ + 1) / 2 = 1 / 2 * (1 / (T₀ : ℝ)) ^ (T₀ + 1) := by ring
      _ ≤ _ := mul_le_mul hlarge hsmall (by positivity) (by linarith)
  -- assemble: `W = ∏ p`, `W / φ(W) = ∏ p / (p − 1)`, `#V = ∏ unitShiftCount b p`
  have hW₀ : 0 < W := Nat.pos_of_ne_zero hW.ne_zero
  have hWprod : ∏ p ∈ P, p = W := Nat.prod_primeFactors_of_squarefree hW
  have hφ : (0 : ℝ) < W.totient := by exact_mod_cast Nat.totient_pos.mpr hW₀
  have hWφ : (W : ℝ) / W.totient = ∏ p ∈ P, (p : ℝ) / (p - 1) := by
    conv_lhs => rw [natCast_eq_totient_mul_prod_primeFactors W]
    field_simp
    rfl
  rw [card_validClasses b hM hMW hW₀ ha₀ hcop, ← hWprod, unitShiftCount_prod b P hPp, hWprod, hWφ]
  conv_lhs => rw [← hWprod]
  push_cast
  rw [← prod_pow, ← prod_mul_distrib]
  calc (1 / (T₀ : ℝ)) ^ (T₀ + 1) / 2 * ∏ p ∈ P, (p : ℝ)
      ≤ (∏ p ∈ P, g p) * ∏ p ∈ P, (p : ℝ) := by gcongr
    _ = _ := by
        rw [← prod_mul_distrib]
        refine prod_congr rfl fun p hp ↦ ?_
        have := hp2 p hp
        simp only [hg]
        field_simp

end Erdos420
