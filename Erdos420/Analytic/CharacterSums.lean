import Erdos420.Analytic.Unsmoothing
import Erdos420.Analytic.ZetaExplicitBound
import Mathlib.NumberTheory.Chebyshev

/-!
# Twisted prime sums for all Dirichlet characters

`ψ(x, χ) = ∑_{m ≤ x} Λ(m) χ(m) = δ_χ x + O(x^{15/16} log x)` uniformly for
characters `χ` mod `q ≤ x`, where `δ_χ = 1` for the principal character and `0`
otherwise.

The primitive character `χ*` inducing `χ` has conductor `d ∣ q`. For `χ* ≠ 1`, the
smoothed explicit formula and unsmoothing give the bound with `B = O(log d)`; for
`χ* = 1`, the same holds with the pole of `ζ`. The terms with `(m, q) > 1`, where
`χ` and `χ*` differ, are prime powers `p^k` with `p ∣ q`: the primes contribute at
most `log q` and the higher powers at most `ψ(x) − θ(x) ≤ 2 √x log x`.
-/

namespace Erdos420

open ArithmeticFunction DirichletCharacter

/-- Every Dirichlet character mod `2` is trivial. -/
private lemma eq_one_of_level_two (χ : DirichletCharacter ℂ 2) : χ = 1 := by
  ext a
  have : a = 1 := Subsingleton.elim a 1
  simp [this]

/-- A nontrivial Dirichlet character has modulus at least `3`. -/
private lemma three_le_level {d : ℕ} [NeZero d] {χ : DirichletCharacter ℂ d} (hχ : χ ≠ 1) :
    3 ≤ d := by
  rcases d with _ | _ | _ | d
  · exact absurd rfl (NeZero.ne 0)
  · exact absurd (level_one χ) hχ
  · exact absurd (eq_one_of_level_two χ) hχ
  · omega

/-- The primes dividing `q` have `∑ log p ≤ log q`. -/
private lemma sum_log_primeFactors_le {q : ℕ} (hq : q ≠ 0) :
    ∑ p ∈ q.primeFactors, Real.log p ≤ Real.log q := by
  have h₁ : 0 < ∏ p ∈ q.primeFactors, p :=
    Finset.prod_pos fun p hp ↦ (Nat.prime_of_mem_primeFactors hp).pos
  have h₂ : ∏ p ∈ q.primeFactors, p ≤ q :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero hq) (Nat.prod_primeFactors_dvd q)
  rw [← Real.log_prod fun p hp ↦ by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero,
    ← Nat.cast_prod]
  exact Real.log_le_log (by exact_mod_cast h₁) (by exact_mod_cast h₂)

/-- The terms of `ψ(x)` with `(m, q) > 1` total at most `2 √x log x + log q`. -/
lemma sum_vonMangoldt_not_coprime_le {q : ℕ} (hq : q ≠ 0) {x : ℝ} (hx : 1 ≤ x) :
    ∑ m ∈ Finset.Icc 1 ⌊x⌋₊ with ¬ m.Coprime q, Λ m ≤ 2 * √x * Real.log x + Real.log q := by
  rw [← Finset.sum_filter_add_sum_filter_not _ Nat.Prime]
  -- the higher prime powers
  have h₁ : ∑ m ∈ (Finset.Icc 1 ⌊x⌋₊).filter (¬ ·.Coprime q) with ¬ m.Prime, Λ m ≤
      Chebyshev.psi x - Chebyshev.theta x := by
    rw [Chebyshev.psi_sub_theta_eq_sum_not_prime]
    refine Finset.sum_le_sum_of_subset_of_nonneg (fun m hm ↦ ?_) fun _ _ _ ↦ vonMangoldt_nonneg
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc] at hm ⊢
    exact ⟨⟨by omega, hm.1.1.2⟩, hm.2⟩
  -- the primes dividing `q`
  have h₂ : ∑ m ∈ (Finset.Icc 1 ⌊x⌋₊).filter (¬ ·.Coprime q) with m.Prime, Λ m ≤
      ∑ p ∈ q.primeFactors, Real.log p := by
    calc _ = ∑ m ∈ (Finset.Icc 1 ⌊x⌋₊).filter (¬ ·.Coprime q) with m.Prime, Real.log m :=
          Finset.sum_congr rfl fun m hm ↦ vonMangoldt_apply_prime (Finset.mem_filter.mp hm).2
      _ ≤ _ := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (fun p hp ↦ ?_)
            fun p _ _ ↦ Real.log_natCast_nonneg p
          simp only [Finset.mem_filter] at hp
          exact Nat.mem_primeFactors.mpr
            ⟨hp.2, not_not.mp ((Nat.Prime.coprime_iff_not_dvd hp.2).not.mp hp.1.2), hq⟩
  have h₃ := Chebyshev.psi_sub_theta_le hx
  have h₄ := sum_log_primeFactors_le hq
  linarith

/-- `χ` and the primitive character inducing it agree on `m` coprime to the modulus. -/
private lemma primitiveCharacter_apply_of_coprime {q : ℕ} (χ : DirichletCharacter ℂ q) {m : ℕ}
    (hm : m.Coprime q) : χ.primitiveCharacter m = χ m := by
  have h := χ.primitiveCharacter_apply_of_isCoprime (a := (m : ℤ))
    (Nat.isCoprime_iff_coprime.mpr hm)
  simpa using h

/-- `ψ(x, χ)` and `ψ(x, χ*)` differ by at most `2 √x log x + log q`. -/
lemma norm_sum_sub_sum_primitiveCharacter_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {x : ℝ} (hx : 1 ≤ x) :
    ‖∑ m ∈ Finset.Icc 1 ⌊x⌋₊, (Λ m : ℂ) * χ m -
        ∑ m ∈ Finset.Icc 1 ⌊x⌋₊, (Λ m : ℂ) * χ.primitiveCharacter m‖ ≤
      2 * √x * Real.log x + Real.log q := by
  rw [← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun m _ ↦ ?_).trans
    ((Finset.sum_filter _ _).symm.le.trans (sum_vonMangoldt_not_coprime_le (NeZero.ne q) hx)))
  split_ifs with hm
  · rw [primitiveCharacter_apply_of_coprime χ hm, sub_self, norm_zero]
  · -- off the modulus, `χ` vanishes
    have hχ : χ m = 0 := MulChar.map_nonunit _ (by rwa [ZMod.isUnit_iff_coprime])
    rw [hχ, mul_zero, zero_sub, norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg vonMangoldt_nonneg]
    exact mul_le_of_le_one_right vonMangoldt_nonneg (norm_le_one _ _)

open scoped Classical in
/-- `ψ(x, χ) = δ_χ x + O(x^{15/16} log x)` uniformly for characters `χ` mod `q ≤ x`. -/
theorem exists_norm_sum_vonMangoldt_mul_char_sub_le :
    ∃ K : ℝ, ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (x : ℝ), 2 ≤ x → (q : ℝ) ≤ x →
      ‖∑ m ∈ Finset.Icc 1 ⌊x⌋₊, (Λ m : ℂ) * χ m - (if χ = 1 then (x : ℂ) else 0)‖ ≤
        K * x ^ (15 / 16 : ℝ) * Real.log x := by
  obtain ⟨K₁, hK₁⟩ := exists_norm_sum_vonMangoldt_le
  obtain ⟨K₂, hK₂⟩ := exists_norm_sum_vonMangoldt_sub_le
  refine ⟨57 + 34 * |K₁| + 68 * |K₂|, ?_⟩
  intro q _ χ x hx hqx
  have hq₀ : (0 : ℝ) < q := by exact_mod_cast (NeZero.pos q)
  have hlogx : 1 / 2 ≤ Real.log x := by
    have h := Real.log_le_log (by norm_num) hx
    linarith [Real.log_two_gt_d9]
  have hlogq : Real.log q ≤ Real.log x := Real.log_le_log hq₀ hqx
  set χ' := χ.primitiveCharacter
  have : NeZero χ.conductor := ⟨conductor_ne_zero χ⟩
  -- each term has `‖Λ(m) χ(m)‖ ≤ Λ(m)`
  have hnorm {N : ℕ} (ψ : DirichletCharacter ℂ N) (m : ℕ) : ‖(Λ m : ℂ) * ψ m‖ ≤ Λ m := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg vonMangoldt_nonneg]
    exact mul_le_of_le_one_right vonMangoldt_nonneg (norm_le_one _ _)
  -- the primitive character, by the explicit formula and unsmoothing
  have hprim : ∃ B, 0 ≤ B ∧ B ≤ |K₁| * Real.log x + |K₂| ∧
      ‖∑ m ∈ Finset.Icc 1 ⌊x⌋₊, (Λ m : ℂ) * χ' m - (if χ = 1 then (x : ℂ) else 0)‖ ≤
        (25 + 4 * Real.log x + 34 * B) * x ^ (15 / 16 : ℝ) := by
    by_cases hχ : χ = 1
    · -- the principal character: `χ*` is the character mod `1`
      have hd : χ.conductor = 1 := (eq_one_iff_conductor_eq_one).mp hχ
      have hχ' (m : ℕ) : χ' m = 1 := by
        rw [show χ' = 1 from level_one' _ hd]
        refine MulChar.one_apply ((ZMod.isUnit_iff_coprime m _).mpr ?_)
        rw [hd]
        exact Nat.coprime_one_right m
      refine ⟨|K₂|, abs_nonneg _, ?_, ?_⟩
      · have := mul_nonneg (abs_nonneg K₁) (by linarith : 0 ≤ Real.log x)
        linarith
      simp only [hχ', mul_one, ite_eq_left hχ]
      have h := norm_sum_sub_mul_le (a := fun m ↦ (Λ m : ℂ)) (δ := 1) (B := |K₂|)
        (fun m ↦ by simp [abs_of_nonneg vonMangoldt_nonneg]) (by simp) (abs_nonneg K₂)
        (fun k hk ↦ ?_) hx
      · simpa using h
      · have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
        have h₁ := hK₂ ((k : ℝ) + 1 / 2) (by linarith) (natCast_ne_natCast_add_one_half k)
        rw [floor_natCast_add_one_half] at h₁
        refine le_trans (le_of_eq ?_) (h₁.trans (by gcongr; exact le_abs_self _))
        simp only [one_mul]
    · -- a nontrivial character: `χ*` is nontrivial and primitive
      have hχ'₁ : χ' ≠ 1 := by
        intro h
        have h₁ : χ'.conductor = 1 := by rw [h, conductor_one]
        exact hχ ((eq_one_iff_conductor_eq_one).mpr
          ((primitiveCharacter_isPrimitive χ).symm.trans h₁))
      have hd₃ : 3 ≤ χ.conductor := three_le_level hχ'₁
      have hdq : (χ.conductor : ℝ) ≤ q := by
        exact_mod_cast Nat.le_of_dvd (NeZero.pos q) (conductor_dvd_level χ)
      have hlogd : 0 ≤ Real.log χ.conductor := Real.log_natCast_nonneg _
      refine ⟨|K₁| * Real.log χ.conductor, by positivity, ?_, ?_⟩
      · have : Real.log χ.conductor ≤ Real.log x :=
          (Real.log_le_log (by positivity) hdq).trans hlogq
        nlinarith [abs_nonneg K₁, abs_nonneg K₂]
      simp only [ite_eq_right hχ]
      have h := norm_sum_sub_mul_le (a := fun m ↦ (Λ m : ℂ) * χ' m) (δ := 0)
        (B := |K₁| * Real.log χ.conductor)
        (hnorm χ') (by simp) (by positivity) (fun k hk ↦ ?_) hx
      · simpa using h
      · have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
        have h₁ := hK₁ hd₃ χ' (primitiveCharacter_isPrimitive χ) hχ'₁ ((k : ℝ) + 1 / 2)
          (by linarith) (natCast_ne_natCast_add_one_half k)
        rw [floor_natCast_add_one_half] at h₁
        refine le_trans (le_of_eq ?_) (h₁.trans ?_)
        · simp
        · calc K₁ * ((k : ℝ) + 1 / 2) ^ (7 / 8 : ℝ) * Real.log χ.conductor
              ≤ |K₁| * ((k : ℝ) + 1 / 2) ^ (7 / 8 : ℝ) * Real.log χ.conductor := by
                gcongr
                exact le_abs_self _
            _ = _ := by ring
  obtain ⟨B, hB₀, hB, hP⟩ := hprim
  -- the imprimitive correction
  have hD := norm_sum_sub_sum_primitiveCharacter_le χ (by linarith : (1 : ℝ) ≤ x)
  have htri := norm_sub_le_norm_sub_add_norm_sub
    (∑ m ∈ Finset.Icc 1 ⌊x⌋₊, (Λ m : ℂ) * χ m)
    (∑ m ∈ Finset.Icc 1 ⌊x⌋₊, (Λ m : ℂ) * χ' m) (if χ = 1 then (x : ℂ) else 0)
  -- assembling, with `X = x^{15/16}` and `L = log x`
  set X := x ^ (15 / 16 : ℝ)
  set L := Real.log x
  have hX : 1 ≤ X := Real.one_le_rpow (by linarith) (by norm_num)
  have hsqrt : √x ≤ X := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have h₁ : 2 * √x * L ≤ 2 * (X * L) := by nlinarith
  have h₂ : Real.log q ≤ X * L := hlogq.trans (by nlinarith)
  have h₃ : 25 * X ≤ 50 * (X * L) := by nlinarith
  have h₄ : 34 * B * X ≤ 34 * |K₁| * (X * L) + 68 * |K₂| * (X * L) := by
    have h₅ : B * X ≤ (|K₁| * L + |K₂|) * X := by gcongr
    have h₆ : |K₂| * X ≤ 2 * |K₂| * (X * L) := by nlinarith [abs_nonneg K₂]
    nlinarith
  have h₇ : (25 + 4 * L + 34 * B) * X = 25 * X + 4 * (X * L) + 34 * B * X := by ring
  calc _ ≤ _ := htri
    _ ≤ 2 * √x * L + Real.log q + (25 + 4 * L + 34 * B) * X := add_le_add hD hP
    _ ≤ (57 + 34 * |K₁| + 68 * |K₂|) * (X * L) := by linarith
    _ = (57 + 34 * |K₁| + 68 * |K₂|) * X * L := by ring

end Erdos420
