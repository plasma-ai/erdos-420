module

public import Mathlib.Algebra.BigOperators.Associated
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Nat.Prime.Int
public import Mathlib.RingTheory.Coprime.Lemmas

/-!
# Choosing residues modulo the covering primes

* Residues modulo distinct primes lift to a single integer (the Chinese remainder theorem).
* Middle stage: some choice of residues `c_q`, each avoiding the classes `−h` of the holes,
  leaves at most `2 |S| ∏_q (1 − 1/q)` survivors of `S`, provided each `s ∈ S` is congruent to
  a hole modulo few of the `q`. This averages over the admissible residues one prime at a time.
* Cleanup stage: each survivor `s` gets its own prime `q` with `z ≡ −s (mod q)`, avoiding the
  at most `r` primes `q` that divide some `s − h`.
* At most `log |n| / log 2` primes divide a nonzero `n`, and at most one prime above `m`
  divides `n` when `|n| ≤ m²`.
-/

@[expose] public section

namespace Erdos420

open Finset Real

/-- Residues modulo distinct primes lift to one integer. -/
lemma exists_int_forall_dvd_sub (f : ℕ → ℤ) (P : Finset ℕ) (hP : ∀ q ∈ P, q.Prime) :
    ∃ z : ℤ, ∀ q ∈ P, (q : ℤ) ∣ z - f q := by
  induction P using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert p P hpP ih =>
    obtain ⟨z₀, hz₀⟩ := ih fun q hq ↦ hP q (mem_insert_of_mem hq)
    have hp := hP p (mem_insert_self p P)
    have hcop : IsCoprime (∏ q ∈ P, (q : ℤ)) p := IsCoprime.prod_left fun q hq ↦
      Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes (hP q (mem_insert_of_mem hq)) hp).mpr
        (ne_of_mem_of_not_mem hq hpP))
    set M := ∏ q ∈ P, (q : ℤ) with hM_def
    obtain ⟨α, β, hαβ⟩ := hcop
    refine ⟨z₀ + α * M * (f p - z₀), fun q hq ↦ ?_⟩
    rcases mem_insert.mp hq with rfl | hq
    · exact ⟨(z₀ - f q) * β, by linear_combination (f q - z₀) * hαβ⟩
    · have hM : (q : ℤ) ∣ M := dvd_prod_of_mem (fun q : ℕ ↦ (q : ℤ)) hq
      rw [show z₀ + α * M * (f p - z₀) - f q = (z₀ - f q) + M * (α * (f p - z₀)) by ring]
      exact dvd_add (hz₀ q hq) (dvd_mul_of_dvd_left hM _)

/-! ### The middle stage -/

/-- Weighted averaging over residues `c_q ∈ A q`, one prime at a time: some choice keeps a
weight of the survivors at most the weighted product of the surviving proportions. -/
lemma exists_residues_sum_le (A : ℕ → Finset ℤ) (Q : Finset ℕ)
    (hA : ∀ q ∈ Q, (A q).Nonempty) (S : Finset ℤ) (ω : ℤ → ℝ) (hω : ∀ s, 0 ≤ ω s) :
    ∃ c : ℕ → ℤ, (∀ q ∈ Q, c q ∈ A q) ∧
      ∑ s ∈ S with ∀ q ∈ Q, ¬ (q : ℤ) ∣ c q + s, ω s ≤
        ∑ s ∈ S, ω s * ∏ q ∈ Q, (#{x ∈ A q | ¬ (q : ℤ) ∣ x + s} : ℝ) / #(A q) := by
  induction Q using Finset.induction_on generalizing S ω with
  | empty => exact ⟨0, by simp, by simp⟩
  | insert p Q hpQ ih =>
    set ρ : ℕ → ℤ → ℝ := fun q s ↦ (#{x ∈ A q | ¬ (q : ℤ) ∣ x + s} : ℝ) / #(A q) with hρ
    set ω' : ℤ → ℝ := fun s ↦ ω s * ∏ q ∈ Q, ρ q s with hω'
    have hAp := hA p (mem_insert_self p Q)
    have hAp' : (0 : ℝ) < #(A p) := by exact_mod_cast hAp.card_pos
    -- choose the residue at `p` by averaging the weights `ω'`
    obtain ⟨x, hx, hxle⟩ : ∃ x ∈ A p,
        ∑ s ∈ S with ¬ (p : ℤ) ∣ x + s, ω' s ≤ ∑ s ∈ S, ω' s * ρ p s := by
      refine exists_le_of_sum_le hAp (le_of_eq ?_)
      rw [sum_const, nsmul_eq_mul]
      calc ∑ x ∈ A p, ∑ s ∈ S with ¬ (p : ℤ) ∣ x + s, ω' s
          = ∑ s ∈ S, ∑ x ∈ A p with ¬ (p : ℤ) ∣ x + s, ω' s := by
            simp_rw [sum_filter]
            exact sum_comm
        _ = ∑ s ∈ S, #(A p) * (ω' s * ρ p s) := by
            refine sum_congr rfl fun s _ ↦ ?_
            rw [sum_const, nsmul_eq_mul, hρ]
            field_simp
        _ = #(A p) * ∑ s ∈ S, ω' s * ρ p s := by rw [mul_sum]
    obtain ⟨c, hcA, hcle⟩ := ih (fun q hq ↦ hA q (mem_insert_of_mem hq))
      {s ∈ S | ¬ (p : ℤ) ∣ x + s} ω hω
    refine ⟨Function.update c p x, fun q hq ↦ ?_, ?_⟩
    · rcases mem_insert.mp hq with rfl | hq
      · simpa using hx
      · rw [Function.update_of_ne (ne_of_mem_of_not_mem hq hpQ)]
        exact hcA q hq
    · have hfil : {s ∈ S | ∀ q ∈ insert p Q, ¬ (q : ℤ) ∣ Function.update c p x q + s} =
          {s ∈ {s ∈ S | ¬ (p : ℤ) ∣ x + s} | ∀ q ∈ Q, ¬ (q : ℤ) ∣ c q + s} := by
        rw [filter_filter]
        refine filter_congr fun s _ ↦ ?_
        simp only [forall_mem_insert, Function.update_self]
        refine and_congr_right fun _ ↦ forall₂_congr fun q hq ↦ ?_
        rw [Function.update_of_ne (ne_of_mem_of_not_mem hq hpQ)]
      rw [hfil]
      calc _ ≤ ∑ s ∈ S with ¬ (p : ℤ) ∣ x + s, ω' s := hcle
        _ ≤ ∑ s ∈ S, ω' s * ρ p s := hxle
        _ = _ := by
            refine sum_congr rfl fun s _ ↦ ?_
            rw [prod_insert hpQ, hω']
            ring

/-- The residues `x ∈ [0, q)` with `q ∤ x + h` for every hole `h`. -/
private def admissible (H : Finset ℕ) (q : ℕ) : Finset ℤ :=
  {x ∈ Ico (0 : ℤ) q | ∀ h ∈ H, ¬ (q : ℤ) ∣ x + h}

/-- Some residue avoids the holes modulo `q > |H|`. -/
private lemma admissible_nonempty (H : Finset ℕ) {q : ℕ} (hq : #H < q) :
    (admissible H q).Nonempty := by
  by_contra hne
  rw [not_nonempty_iff_eq_empty, admissible, filter_eq_empty_iff] at hne
  -- every residue is the class of `−h` for some hole `h`
  have hsub : Ico (0 : ℤ) q ⊆ H.image fun h : ℕ ↦ (-(h : ℤ)) % q := fun x hx ↦ by
    have hx' := hne hx
    simp only [not_forall, not_not] at hx'
    obtain ⟨h, hh, hdvd⟩ := hx'
    rw [mem_Ico] at hx
    refine mem_image.mpr ⟨h, hh, ?_⟩
    have hmod : x ≡ -(h : ℤ) [ZMOD q] :=
      Int.modEq_iff_dvd.mpr (by rw [show -(h : ℤ) - x = -(x + h) by ring]; exact dvd_neg.mpr hdvd)
    rw [← hmod, Int.emod_eq_of_lt hx.1 hx.2]
  have := (card_le_card hsub).trans card_image_le
  rw [Int.card_Ico, sub_zero, Int.toNat_natCast] at this
  omega

/-- At most `#(admissible H q) − 1` admissible residues miss `−s`, when `s` is not congruent
to a hole. -/
private lemma card_filter_admissible_add_one_le (H : Finset ℕ) {q : ℕ} (hq : 0 < q) {s : ℤ}
    (hs : ∀ h ∈ H, ¬ (q : ℤ) ∣ s - h) :
    #{x ∈ admissible H q | ¬ (q : ℤ) ∣ x + s} + 1 ≤ #(admissible H q) := by
  set k := (-s) % q with hk_def
  have hk : k = -s - q * (-s / q) := Int.emod_def _ _
  have hkA : k ∈ admissible H q := by
    refine mem_filter.mpr ⟨mem_Ico.mpr ⟨Int.emod_nonneg _ (by omega),
      Int.emod_lt_of_pos _ (by omega)⟩, fun h hh hd ↦ hs h hh ?_⟩
    rw [show s - h = -(k + h) - q * (-s / q) by rw [hk]; ring]
    exact dvd_sub (dvd_neg.mpr hd) (dvd_mul_right _ _)
  have hsub : {x ∈ admissible H q | ¬ (q : ℤ) ∣ x + s} ⊆ (admissible H q).erase k := by
    intro x hx
    rw [mem_filter] at hx
    refine mem_erase.mpr ⟨fun hxk ↦ hx.2 ?_, hx.1⟩
    rw [hxk, hk]
    exact ⟨-(-s / q), by ring⟩
  have := card_le_card hsub
  rw [card_erase_of_mem hkA] at this
  have := card_pos.mpr ⟨k, hkA⟩
  omega

/-- `∏_{q ∈ F} (1 − 1/q) ≥ 1/2` when every `q ∈ F` is at least `m ≥ 1` and `|F| ≤ m/2`. -/
lemma one_half_le_prod_one_sub_one_div {F : Finset ℕ} {m : ℝ} (hm : 1 ≤ m) (hF : ∀ q ∈ F, m ≤ q)
    (hcard : (#F : ℝ) ≤ m / 2) : 1 / 2 ≤ ∏ q ∈ F, (1 - 1 / (q : ℝ)) := by
  have hm0 : 0 < m := by linarith
  have h₁ : 0 ≤ 1 - 1 / m := by
    rw [sub_nonneg, div_le_one hm0]
    exact hm
  calc (1 : ℝ) / 2 ≤ 1 + #F * (-(1 / m)) := by
        have : (#F : ℝ) * (1 / m) ≤ 1 / 2 := by rw [mul_one_div, div_le_iff₀ hm0]; linarith
        linarith
    _ ≤ (1 + -(1 / m)) ^ #F := one_add_mul_le_pow (by
        have : 1 / m ≤ 1 := by rw [div_le_one hm0]; exact hm
        linarith) _
    _ = ∏ q ∈ F, (1 - 1 / m) := by rw [prod_const, ← sub_eq_add_neg]
    _ ≤ ∏ q ∈ F, (1 - 1 / (q : ℝ)) := by
        refine prod_le_prod₀ (fun _ _ ↦ h₁) fun q hq ↦ ?_
        have := hF q hq
        gcongr

/-- Middle stage: if each `s ∈ S` is congruent to a hole modulo primes `q ∈ Q` with
`∏ (1 − 1/q) ≥ 1/2`, then some residues `c_q` avoiding the holes leave at most
`2 |S| ∏_{q ∈ Q} (1 − 1/q)` survivors. -/
theorem exists_middle_residues (H Q : Finset ℕ) (hQ : ∀ q ∈ Q, q.Prime ∧ #H < q) (S : Finset ℤ)
    (hS : ∀ s ∈ S, 1 / 2 ≤ ∏ q ∈ Q with ∃ h ∈ H, ((q : ℕ) : ℤ) ∣ s - h, (1 - 1 / (q : ℝ))) :
    ∃ c : ℕ → ℤ, (∀ q ∈ Q, ∀ h ∈ H, ¬ (q : ℤ) ∣ c q + h) ∧
      (#{s ∈ S | ∀ q ∈ Q, ¬ (q : ℤ) ∣ c q + s} : ℝ) ≤ 2 * #S * ∏ q ∈ Q, (1 - 1 / (q : ℝ)) := by
  obtain ⟨c, hcA, hcle⟩ := exists_residues_sum_le (admissible H) Q
    (fun q hq ↦ admissible_nonempty H (hQ q hq).2) S (fun _ ↦ 1) fun _ ↦ zero_le_one
  refine ⟨c, fun q hq h hh ↦ (mem_filter.mp (hcA q hq)).2 h hh, ?_⟩
  have hP : 0 ≤ ∏ q ∈ Q, (1 - 1 / (q : ℝ)) := prod_nonneg fun q hq ↦ by
    have : (1 : ℝ) ≤ q := by exact_mod_cast (hQ q hq).1.one_lt.le
    rw [sub_nonneg, div_le_one (by linarith)]
    exact this
  simp only [one_mul, sum_const, nsmul_eq_mul, mul_one] at hcle
  refine hcle.trans ?_
  calc ∑ s ∈ S, ∏ q ∈ Q, (#{x ∈ admissible H q | ¬ (q : ℤ) ∣ x + s} : ℝ) / #(admissible H q)
      ≤ ∑ s ∈ S, 2 * ∏ q ∈ Q, (1 - 1 / (q : ℝ)) := sum_le_sum fun s hs ↦ ?_
    _ = 2 * #S * ∏ q ∈ Q, (1 - 1 / (q : ℝ)) := by rw [sum_const, nsmul_eq_mul]; ring
  -- the proportion is at most `1 − 1/q` when `s` is not congruent to a hole, and `1` otherwise
  have hρ : ∀ q ∈ Q, (#{x ∈ admissible H q | ¬ (q : ℤ) ∣ x + s} : ℝ) / #(admissible H q) ≤
      if ∃ h ∈ H, (q : ℤ) ∣ s - h then 1 else 1 - 1 / (q : ℝ) := by
    intro q hq
    have hA : (0 : ℝ) < #(admissible H q) := by
      exact_mod_cast (admissible_nonempty H (hQ q hq).2).card_pos
    split_ifs with hbad
    · rw [div_le_one hA]
      exact_mod_cast card_filter_le _ _
    · have h₁ := card_filter_admissible_add_one_le H (hQ q hq).1.pos (by simpa using hbad)
      have h₂ : #(admissible H q) ≤ q := by
        have := card_filter_le (Ico (0 : ℤ) q) fun x ↦ ∀ h ∈ H, ¬ (q : ℤ) ∣ x + h
        rwa [Int.card_Ico, sub_zero, Int.toNat_natCast] at this
      have h₁' : (#{x ∈ admissible H q | ¬ (q : ℤ) ∣ x + s} : ℝ) + 1 ≤ #(admissible H q) := by
        exact_mod_cast h₁
      have h₂' : (#(admissible H q) : ℝ) ≤ q := by exact_mod_cast h₂
      rw [div_le_iff₀ hA, sub_mul, one_mul]
      have : 1 / (q : ℝ) * #(admissible H q) ≤ 1 := by
        rw [one_div_mul_eq_div, div_le_one (by exact_mod_cast (hQ q hq).1.pos)]
        exact h₂'
      linarith
  calc ∏ q ∈ Q, (#{x ∈ admissible H q | ¬ (q : ℤ) ∣ x + s} : ℝ) / #(admissible H q)
      ≤ ∏ q ∈ Q, (if ∃ h ∈ H, (q : ℤ) ∣ s - h then 1 else 1 - 1 / (q : ℝ)) :=
        prod_le_prod₀ (fun _ _ ↦ by positivity) hρ
    _ = ∏ q ∈ Q with ¬ ∃ h ∈ H, ((q : ℕ) : ℤ) ∣ s - h, (1 - 1 / (q : ℝ)) := by
        rw [prod_filter]
        exact prod_congr rfl fun q _ ↦ by split_ifs <;> rfl
    _ ≤ 2 * ∏ q ∈ Q, (1 - 1 / (q : ℝ)) := by
        rw [← prod_filter_mul_prod_filter_not Q fun q ↦ ∃ h ∈ H, (q : ℤ) ∣ s - h]
        have := hS s hs
        have h₀ : 0 ≤ ∏ q ∈ Q with ¬ ∃ h ∈ H, ((q : ℕ) : ℤ) ∣ s - h, (1 - 1 / (q : ℝ)) :=
          prod_nonneg fun q hq ↦ by
            have : (1 : ℝ) ≤ q := by exact_mod_cast (hQ q (mem_filter.mp hq).1).1.one_lt.le
            rw [sub_nonneg, div_le_one (by linarith)]
            exact this
        nlinarith

/-! ### The cleanup stage -/

/-- Cleanup stage: if each `s ∈ S` has at most `r` primes `q ∈ R` dividing some `s − h`, and
`|S| + r ≤ |R|`, then residues modulo the primes of `R` avoid the holes and cover `S`. -/
theorem exists_cleanup_residues (H : Finset ℕ) (r : ℕ) (S : Finset ℤ) (R : Finset ℕ)
    (hR : ∀ q ∈ R, ∀ h ∈ H, ¬ (q : ℤ) ∣ h)
    (hS : ∀ s ∈ S, #{q ∈ R | ∃ h ∈ H, ((q : ℕ) : ℤ) ∣ s - h} ≤ r) (hSR : #S + r ≤ #R) :
    ∃ e : ℕ → ℤ, (∀ q ∈ R, ∀ h ∈ H, ¬ (q : ℤ) ∣ e q + h) ∧
      ∀ s ∈ S, ∃ q ∈ R, (q : ℤ) ∣ e q + s := by
  induction S using Finset.induction_on generalizing R with
  | empty => exact ⟨0, fun q hq h hh ↦ by simpa using hR q hq h hh, by simp⟩
  | insert s S hsS ih =>
    rw [card_insert_of_notMem hsS] at hSR
    -- a prime of `R` dividing no `s − h`
    have hlt : #{q ∈ R | ∃ h ∈ H, ((q : ℕ) : ℤ) ∣ s - h} < #R :=
      (hS s (mem_insert_self s S)).trans_lt (by omega)
    obtain ⟨q, hqR, hq⟩ := exists_mem_notMem_of_card_lt_card hlt
    have hq' : ∀ h ∈ H, ¬ (q : ℤ) ∣ s - h := fun h hh hd ↦ hq (mem_filter.mpr ⟨hqR, h, hh, hd⟩)
    obtain ⟨e, he, hcov⟩ := ih (R.erase q) (fun q' hq' ↦ hR q' (mem_of_mem_erase hq'))
      (fun s' hs' ↦ (card_le_card (filter_subset_filter _ (erase_subset q R))).trans
        (hS s' (mem_insert_of_mem hs')))
      (by rw [card_erase_of_mem hqR]; omega)
    refine ⟨Function.update e q (-s), fun q' hq'R h hh ↦ ?_, fun s' hs' ↦ ?_⟩
    · by_cases hqq : q' = q
      · subst hqq
        rw [Function.update_self]
        intro hd
        exact hq' h hh (by rw [show s - h = -(-s + h) by ring]; exact dvd_neg.mpr hd)
      · rw [Function.update_of_ne hqq]
        exact he q' (mem_erase.mpr ⟨hqq, hq'R⟩) h hh
    · rcases mem_insert.mp hs' with rfl | hs'
      · exact ⟨q, hqR, by rw [Function.update_self, neg_add_cancel]; exact dvd_zero _⟩
      · obtain ⟨q', hq'R, hd⟩ := hcov s' hs'
        refine ⟨q', mem_of_mem_erase hq'R, ?_⟩
        rwa [Function.update_of_ne (ne_of_mem_erase hq'R)]

/-! ### Primes dividing a nonzero integer -/

/-- At most `log |n| / log 2` primes of `Q` divide a nonzero `n`. -/
lemma card_filter_dvd_mul_log_two_le_log_abs {Q : Finset ℕ} (hQ : ∀ q ∈ Q, q.Prime) {n : ℤ}
    (hn : n ≠ 0) : (#{q ∈ Q | ((q : ℕ) : ℤ) ∣ n} : ℝ) * log 2 ≤ log |(n : ℝ)| := by
  have hdvd : ∏ q ∈ Q with ((q : ℕ) : ℤ) ∣ n, q ∣ n.natAbs :=
    prod_primes_dvd _ (fun q hq ↦ (hQ q (mem_filter.mp hq).1).prime)
      fun q hq ↦ Int.ofNat_dvd_left.mp (mem_filter.mp hq).2
  have h₁ : 2 ^ #{q ∈ Q | ((q : ℕ) : ℤ) ∣ n} ≤ ∏ q ∈ Q with ((q : ℕ) : ℤ) ∣ n, q :=
    pow_card_le_prod _ _ _ fun q hq ↦ (hQ q (mem_filter.mp hq).1).two_le
  have h₂ := h₁.trans (Nat.le_of_dvd (Int.natAbs_pos.mpr hn) hdvd)
  have h₃ : ((2 ^ #{q ∈ Q | ((q : ℕ) : ℤ) ∣ n} : ℕ) : ℝ) ≤ (n.natAbs : ℝ) := by exact_mod_cast h₂
  rw [Nat.cast_natAbs, Int.cast_abs] at h₃
  push_cast at h₃
  rw [← log_pow]
  exact log_le_log (by positivity) h₃

/-- At most one prime above `m ≥ 0` divides a nonzero `n` with `|n| ≤ m²`. -/
lemma card_filter_dvd_le_one_of_abs_le_sq {R : Finset ℕ} (hR : ∀ q ∈ R, q.Prime) {m : ℝ}
    (hm : 0 ≤ m) (hRm : ∀ q ∈ R, m < q) {n : ℤ} (hn : n ≠ 0) (hnm : |(n : ℝ)| ≤ m ^ 2) :
    #{q ∈ R | ((q : ℕ) : ℤ) ∣ n} ≤ 1 := by
  refine card_le_one.mpr fun q₁ h₁ q₂ h₂ ↦ by_contra fun hne ↦ ?_
  rw [mem_filter] at h₁ h₂
  have hcop : IsCoprime (q₁ : ℤ) q₂ :=
    Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes (hR q₁ h₁.1) (hR q₂ h₂.1)).mpr hne)
  have hd : (q₁ : ℤ) * q₂ ∣ |n| := (dvd_abs _ _).mpr (hcop.mul_dvd h₁.2 h₂.2)
  have hle : (q₁ : ℤ) * q₂ ≤ |n| := Int.le_of_dvd (abs_pos.mpr hn) hd
  have hle' : (q₁ : ℝ) * q₂ ≤ |(n : ℝ)| := by rw [← Int.cast_abs]; exact_mod_cast hle
  have := mul_lt_mul'' (hRm q₁ h₁.1) (hRm q₂ h₂.1) hm hm
  nlinarith

end Erdos420
