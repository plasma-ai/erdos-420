module

public import Erdos420.Asymptotics
public import Erdos420.Sieve.Selberg
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Data.Nat.Prime.Int

/-!
# Anchors where a shifted integer is a small multiple of a prime

Let `L_i(t) = a₀ + M t + b_i` be the detector forms and `A_t = k (a₀ + M t)`
the anchors. Fix an offset `s` that is not a hole `k b_i`, and a cofactor `ℓ`.
We count the `t ∈ [N, 2N)` such that every detector `L_i(t)` is `X^c`-rough
and `A_t + s = ℓ p` for a prime `p > X^c`.

Write `g = gcd(ℓ, kM)`. The condition `ℓ ∣ A_t + s` puts `t` in one class
modulo `ℓ / g`, so `t = t₀ + (ℓ / g) v` with `v` in an interval of length
`N g / ℓ + 1`. In `v`, the `r` detectors and the quotient `(A_t + s) / ℓ` are
`r + 1` linear forms. Their determinants are `(M ℓ / g)(b_j − b_i)` and
`(M / g)(s − k b_i)`, which are nonzero because `s` is not a hole. Every prime
dividing a determinant or a leading coefficient is at most `(log X)^{D+3}`
once the primes of `M` are at most `log X`. The sieve bound
`Erdos420.exists_card_sifted_linear_forms_le` with `v₀ = (log X)^{D+3}` and
`Z = X^c` then gives the bound.
-/

@[expose] public section

namespace Erdos420

open Filter

/-- A natural number dividing a nonzero integer is at most its absolute value. -/
private lemma natCast_le_abs_of_dvd {p : ℕ} {x : ℤ} (hx : x ≠ 0) (h : (p : ℤ) ∣ x) :
    (p : ℝ) ≤ |(x : ℝ)| := by
  have := Int.le_of_dvd (abs_pos.2 hx) ((dvd_abs _ _).2 h)
  exact_mod_cast this

open scoped Classical in
/-- At most `≪ (N gcd(ℓ, kM) / ℓ + 1) (log log X / log X)^{r+1} + X^{3c}` anchors `t`
have `X^c`-rough detectors and `k (a₀ + M t) + s = ℓ p` with `p > X^c` prime. -/
theorem exists_card_anchor_pair_le (k r D : ℕ) (hk : 1 ≤ k) (b : Fin r → ℕ)
    (hb : Function.Injective b) {c : ℝ} (hc : 0 < c) (hc' : c < 1 / 4) :
    ∃ C : ℝ, ∀ᶠ X : ℕ in atTop, ∀ M a₀ N ℓ : ℕ, ∀ s : ℤ,
      1 ≤ M → (∀ p : ℕ, p.Prime → p ∣ M → (p : ℝ) ≤ Real.log X) →
      1 ≤ ℓ → (ℓ : ℝ) ≤ Real.log X ^ D → |(s : ℝ)| ≤ Real.log X ^ 2 →
      (∀ i, s ≠ k * b i) →
      (((Finset.Ico N (2 * N)).filter fun t ↦
          (∀ i, ∀ p : ℕ, p.Prime → p ∣ a₀ + M * t + b i → (X : ℝ) ^ c < p) ∧
          ∃ p : ℕ, p.Prime ∧ (X : ℝ) ^ c < p ∧
            ((k * (a₀ + M * t) : ℕ) : ℤ) + s = ℓ * p).card : ℝ) ≤
        C * ((N : ℝ) * Nat.gcd ℓ (k * M) / ℓ + 1) *
            (Real.log (Real.log X) / Real.log X) ^ (r + 1) +
          C * (X : ℝ) ^ (3 * c) := by
  obtain ⟨C₀, hC₀⟩ := exists_card_sifted_linear_forms_le (r + 1)
  set B : ℕ := ∑ i, b i
  set E : ℝ := ((D + 3) / c) ^ (r + 1) with hE_def
  have hE : 0 ≤ E := by positivity
  refine ⟨|C₀| * (E + 1), ?_⟩
  filter_upwards [eventually_ge_atTop 1,
    tendsto_log_natCast_atTop.eventually_ge_atTop (((r + 1 : ℕ) : ℝ) ^ 2 + k * B + k + B + 2),
    tendsto_natCast_atTop_atTop.eventually
      ((isLittleO_log_rpow_rpow_atTop (((D + 3) * (100 * (r + 1)) : ℕ) : ℝ) hc).bound one_pos)]
    with X hX1 hXlog hXpow M a₀ N ℓ s hM hMp hℓ hℓD hs hsb
  set L := Real.log X
  set v₀ := L ^ (D + 3) with hv₀_def
  set Z := (X : ℝ) ^ c with hZ_def
  set g := Nat.gcd ℓ (k * M)
  have hX0 : (0 : ℝ) < X := by exact_mod_cast hX1
  have hB0 : (0 : ℝ) ≤ B := Nat.cast_nonneg _
  have hr0 : (0 : ℝ) ≤ ((r + 1 : ℕ) : ℝ) ^ 2 := by positivity
  have hkB0 : (0 : ℝ) ≤ k * B := by positivity
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have hL2 : 2 ≤ L := by linarith
  have hkL : (k : ℝ) ≤ L := by linarith
  have hkBL : (k * B : ℝ) ≤ L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have hLv : L ≤ v₀ := le_self_pow₀ hL1 (by omega)
  have hL3v : L ^ 3 ≤ v₀ := pow_le_pow_right₀ hL1 (by omega)
  have hlogZ : Real.log Z = c * L := Real.log_rpow hX0 c
  have hratio : Real.log v₀ / Real.log Z = (D + 3) / c * (Real.log L / L) := by
    rw [hlogZ, hv₀_def, Real.log_pow]
    push_cast
    field_simp
  have hR : 0 ≤ Real.log L / L := div_nonneg (Real.log_nonneg hL1) (by linarith)
  have hZ3 : Z ^ 3 = (X : ℝ) ^ (3 * c) := by
    rw [hZ_def, ← Real.rpow_natCast, ← Real.rpow_mul hX0.le]
    norm_num [mul_comm]
  -- every prime above `v₀` misses `M`, `ℓ`, `k`, and the differences `b j − b i` and `k b i − s`
  have hbad : ∀ p : ℕ, p.Prime → v₀ < p → ¬ (p : ℤ) ∣ M ∧ ¬ (p : ℤ) ∣ ℓ ∧ ¬ (p : ℤ) ∣ k ∧
      (∀ i j, i ≠ j → ¬ (p : ℤ) ∣ (b j - b i : ℤ)) ∧ ∀ i, ¬ (p : ℤ) ∣ (k * b i - s : ℤ) := by
    intro p hp hpv
    have hbB : ∀ i, (b i : ℝ) ≤ B := fun i ↦ by
      exact_mod_cast Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)
    refine ⟨fun h ↦ ?_, fun h ↦ ?_, fun h ↦ ?_, fun i j hij h ↦ ?_, fun i h ↦ ?_⟩
    · linarith [hMp p hp (Int.natCast_dvd_natCast.1 h)]
    · have : (p : ℝ) ≤ ℓ := by
        exact_mod_cast Nat.le_of_dvd (by omega) (Int.natCast_dvd_natCast.1 h)
      linarith [pow_le_pow_right₀ hL1 (by omega : D ≤ D + 3)]
    · have : (p : ℝ) ≤ k := by
        exact_mod_cast Nat.le_of_dvd (by omega) (Int.natCast_dvd_natCast.1 h)
      linarith
    · have hne : (b j : ℤ) - b i ≠ 0 := sub_ne_zero.2 fun h' ↦ hij (hb (by exact_mod_cast h')).symm
      have := natCast_le_abs_of_dvd hne h
      push_cast at this
      have : |(b j : ℝ) - b i| ≤ B :=
        abs_sub_le_iff.2 ⟨by linarith [hbB j, Nat.cast_nonneg (α := ℝ) (b i)],
          by linarith [hbB i, Nat.cast_nonneg (α := ℝ) (b j)]⟩
      linarith
    · have hne : (k * b i : ℤ) - s ≠ 0 := sub_ne_zero.2 (hsb i).symm
      have := natCast_le_abs_of_dvd hne h
      push_cast at this
      have : |(k * b i : ℝ) - s| ≤ k * B + L ^ 2 := by
        refine (abs_sub _ _).trans ?_
        rw [abs_of_nonneg (by positivity)]
        have := mul_le_mul_of_nonneg_left (hbB i) (Nat.cast_nonneg (α := ℝ) k)
        linarith
      nlinarith
  set S := (Finset.Ico N (2 * N)).filter fun t ↦
      (∀ i, ∀ p : ℕ, p.Prime → p ∣ a₀ + M * t + b i → (X : ℝ) ^ c < p) ∧
      ∃ p : ℕ, p.Prime ∧ (X : ℝ) ^ c < p ∧ ((k * (a₀ + M * t) : ℕ) : ℤ) + s = ℓ * p
  rcases S.eq_empty_or_nonempty with hS | hS
  · rw [hS, Finset.card_empty, Nat.cast_zero]
    exact add_nonneg (mul_nonneg (mul_nonneg (by positivity) (by positivity)) (pow_nonneg hR _))
      (by positivity)
  -- the solutions `t` lie in one class modulo `m = ℓ / g`, starting at the least one `t₀`
  set t₀ := S.min' hS
  obtain ⟨ht₀, -, p₀, -, -, hp₀⟩ := Finset.mem_filter.1 (S.min'_mem hS)
  rw [Finset.mem_Ico] at ht₀
  push_cast at hp₀
  set m := ℓ / g
  set n := k * M / g
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_left _ (by omega)
  have hgm : g * m = ℓ := Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)
  have hgn : g * n = k * M := Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)
  have hgmZ : (g : ℤ) * m = ℓ := by exact_mod_cast hgm
  have hgnZ : (g : ℤ) * n = k * M := by exact_mod_cast hgn
  have hm0 : 0 < m := Nat.pos_of_ne_zero fun h ↦ by rw [h, mul_zero] at hgm; omega
  have hmn : m.Coprime n := Nat.coprime_div_gcd_div_gcd hg0
  have hdvd : ∀ t ∈ S, t₀ ≤ t ∧ m ∣ t - t₀ := by
    intro t ht
    obtain ⟨-, -, p, -, -, hp⟩ := Finset.mem_filter.1 ht
    push_cast at hp
    have ht₀t : t₀ ≤ t := S.min'_le t ht
    refine ⟨ht₀t, ?_⟩
    have hℓ : ℓ ∣ k * M * (t - t₀) := Int.natCast_dvd_natCast.1
      ⟨p - p₀, by push_cast [Nat.cast_sub ht₀t]; linear_combination hp - hp₀⟩
    rw [← hgm, ← hgn, mul_assoc] at hℓ
    exact hmn.dvd_of_dvd_mul_left (Nat.dvd_of_mul_dvd_mul_left hg0 hℓ)
  -- the forms `n v + p₀` and `M m v + a₀ + M t₀ + b i`
  obtain ⟨α, hα0, hαs⟩ : ∃ α : Fin (r + 1) → ℤ, α 0 = n ∧ ∀ i : Fin r, α i.succ = M * m :=
    ⟨Fin.cons (n : ℤ) fun _ ↦ (M * m : ℤ), rfl, fun _ ↦ rfl⟩
  obtain ⟨β, hβ0, hβs⟩ :
      ∃ β : Fin (r + 1) → ℤ, β 0 = p₀ ∧ ∀ i : Fin r, β i.succ = a₀ + M * t₀ + b i :=
    ⟨Fin.cons (p₀ : ℤ) fun i ↦ (a₀ + M * t₀ + b i : ℤ), rfl, fun _ ↦ rfl⟩
  have hsel := hC₀ α β v₀ Z 0 (N / m + 1) (by linarith) (by linarith)
    (by rw [hlogZ]; nlinarith) (by
      rw [hv₀_def, ← pow_mul]
      rw [Real.rpow_natCast, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
        abs_of_nonneg (by positivity), one_mul] at hXpow
      exact hXpow) (by
      intro p hp hpv
      obtain ⟨hpM, hpℓ, hpk, hpb, hpsb⟩ := hbad p hp hpv
      have hpp : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
      have hpm : ¬ (p : ℤ) ∣ m := fun h ↦ hpℓ (hgmZ ▸ dvd_mul_of_dvd_right h _)
      have hpn : ¬ (p : ℤ) ∣ n := fun h ↦ by
        rcases hpp.dvd_or_dvd (hgnZ ▸ dvd_mul_of_dvd_right h _) with h | h
        exacts [hpk h, hpM h]
      have hpMm : ¬ (p : ℤ) ∣ M * m := fun h ↦ by
        rcases hpp.dvd_or_dvd h with h | h
        exacts [hpM h, hpm h]
      -- `g` times the determinant of the prime form and a detector is `M (k b j − s)`
      have hdet : ∀ j, ¬ (p : ℤ) ∣ n * (a₀ + M * t₀ + b j) - M * m * p₀ := fun j h ↦ by
        have := dvd_mul_of_dvd_right h (g : ℤ)
        rw [show (g : ℤ) * (n * (a₀ + M * t₀ + b j) - M * m * p₀) = M * (k * b j - s) by
          linear_combination
            (a₀ + M * t₀ + b j : ℤ) * hgnZ - (M * p₀ : ℤ) * hgmZ + (M : ℤ) * hp₀] at this
        rcases hpp.dvd_or_dvd this with h | h
        exacts [hpM h, hpsb j h]
      refine ⟨fun j ↦ ?_, fun i j hij ↦ ?_⟩
      · cases j using Fin.cases with
        | zero => rwa [hα0]
        | succ j => rwa [hαs]
      · cases i using Fin.cases <;> cases j using Fin.cases
        · exact absurd rfl hij
        · rw [hα0, hαs, hβ0, hβs]
          exact hdet _
        · rename_i i
          rw [hα0, hαs, hβ0, hβs, show (M * m : ℤ) * p₀ - n * (a₀ + M * t₀ + b i) =
            -(n * (a₀ + M * t₀ + b i) - M * m * p₀) by ring, dvd_neg]
          exact hdet _
        · rename_i i j
          rw [hαs, hαs, hβs, hβs, show (M * m : ℤ) * (a₀ + M * t₀ + b j) -
            M * m * (a₀ + M * t₀ + b i) = M * m * (b j - b i) by ring]
          intro h
          rcases hpp.dvd_or_dvd h with h | h
          exacts [hpMm h, hpb i j (fun h ↦ hij (by rw [h])) h])
  -- `v = (t − t₀) / m` lies in `[0, N / m + 1)` and is sifted by the primes in `(v₀, Z]`
  refine (Nat.cast_le.2 (Finset.card_le_card_of_injOn (fun t ↦ (((t - t₀) / m : ℕ) : ℤ))
    ?_ ?_)).trans (hsel.trans ?_)
  · intro t ht
    obtain ⟨ht₀t, hmt⟩ := hdvd t ht
    obtain ⟨htI, hrough, p, hp, hpX, hpe⟩ := Finset.mem_filter.1 ht
    rw [Finset.mem_Ico] at htI
    push_cast at hpe
    simp only [Finset.coe_filter, Finset.mem_Ico, Set.mem_ofPred_eq]
    set v : ℤ := (((t - t₀) / m : ℕ) : ℤ) with hv_def
    have hv : (m : ℤ) * v = t - t₀ := by
      rw [hv_def, ← Nat.cast_sub ht₀t, ← Nat.cast_mul, Nat.mul_div_cancel' hmt]
    refine ⟨⟨by positivity, ?_⟩, fun j q hq hqv hqZ ↦ ?_⟩
    · have : (t - t₀) / m ≤ N / m := Nat.div_le_div_right (by omega)
      rw [hv_def, zero_add]
      exact_mod_cast Nat.lt_succ_of_le this
    · cases j using Fin.cases with
      | zero =>
        -- the prime form takes the value `p`
        have hℓ0 : (ℓ : ℤ) ≠ 0 := by positivity
        rw [hα0, hβ0, show (n : ℤ) * v + p₀ = p from mul_left_cancel₀ hℓ0 (by
          linear_combination hpe - hp₀ + (k * M : ℤ) * hv - (n * v) * hgmZ + (m * v) * hgnZ)]
        intro h
        rw [(Nat.prime_dvd_prime_iff_eq hq hp).1 (Int.natCast_dvd_natCast.1 h)] at hqZ
        linarith
      | succ i =>
        -- the detector forms take the values `a₀ + M t + b i`
        rw [hαs, hβs, show (M * m : ℤ) * v + (a₀ + M * t₀ + b i) =
            ((a₀ + M * t + b i : ℕ) : ℤ) by
          push_cast
          linear_combination (M : ℤ) * hv]
        exact fun h ↦ absurd (hrough i q hq (Int.natCast_dvd_natCast.1 h)) (not_lt.2 hqZ)
  · intro t ht t' ht' h
    obtain ⟨h₁, h₂⟩ := hdvd t ht
    obtain ⟨h₁', h₂'⟩ := hdvd t' ht'
    have h : (t - t₀) / m = (t' - t₀) / m := Nat.cast_injective h
    have : t - t₀ = t' - t₀ := by
      rw [← Nat.mul_div_cancel' h₂, ← Nat.mul_div_cancel' h₂', h]
    omega
  -- absorb `(log v₀ / log Z)^{r+1} = E (log L / L)^{r+1}` and `Z³ = X^{3c}`
  have hV : ((N / m + 1 : ℕ) : ℝ) ≤ (N : ℝ) * g / ℓ + 1 := by
    have hmR : (m : ℝ) * g = ℓ := by rw [mul_comm]; exact_mod_cast hgm
    have : ((N / m : ℕ) : ℝ) ≤ (N : ℝ) * g / ℓ := by
      refine Nat.cast_div_le.trans_eq ?_
      rw [← hmR]
      field_simp
    push_cast
    linarith
  rw [hratio, mul_pow, hZ3, ← hE_def]
  have h₁ : C₀ * ((N / m + 1 : ℕ) : ℝ) * E ≤ |C₀| * (E + 1) * ((N : ℝ) * g / ℓ + 1) := by
    have := mul_le_mul_of_nonneg_left
      (mul_le_mul hV (by linarith : E ≤ E + 1) hE (by positivity)) (abs_nonneg C₀)
    have := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_abs_self C₀) (Nat.cast_nonneg (N / m + 1))) hE
    linarith
  have h₂ : C₀ ≤ |C₀| * (E + 1) :=
    (le_abs_self _).trans (le_mul_of_one_le_right (abs_nonneg _) (by linarith))
  have := add_le_add (mul_le_mul_of_nonneg_right h₁ (pow_nonneg hR (r + 1)))
    (mul_le_mul_of_nonneg_right h₂ (Real.rpow_nonneg hX0.le (3 * c)))
  linarith

end Erdos420
