import Erdos420.Analytic.CharacterSums
import Mathlib.NumberTheory.LSeries.PrimesInAP

/-!
# Primes in arithmetic progressions with a power saving

`θ(Y; q, c) = Y / φ(q) + O(Y^{15/16} log² Y)` uniformly for `q ≤ Y` and `c`
coprime to `q`.

The smoothed explicit formula, with every zero to the left of `re s = 7/8`,
gives `∑_{m ≤ x} Λ(m) χ(m) (1 − m/x) = δ_χ x/2 + O(x^{7/8} log q)` for
primitive `χ` mod `q`. Differencing at `x` and `x + x^{15/16}` gives
`ψ(x, χ) = δ_χ x + O(x^{15/16} log (q x))`. Imprimitive characters differ from
the primitive ones inducing them by `O(√x log x + log q)`. Character orthogonality
and the `O(√x log x)` prime powers finish the proof.
-/

namespace Erdos420

open ArithmeticFunction DirichletCharacter

/-- `θ(Y; q, c) = ∑_{p ≤ Y, p ≡ c (mod q)} log p`. -/
noncomputable def thetaAP (Y : ℝ) (q c : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Iic ⌊Y⌋₊).filter (fun p ↦ p.Prime ∧ p ≡ c [MOD q]), Real.log p

/-- `ψ(Y; q, c) = Y / φ(q) + O(Y^{15/16} log Y)` uniformly for `q ≤ Y` and `c` coprime
to `q`, by orthogonality of characters. -/
theorem exists_abs_sum_vonMangoldt_modEq_sub_le : ∃ K : ℝ, ∀ Y : ℝ, 2 ≤ Y → ∀ q c : ℕ, 1 ≤ q →
    (q : ℝ) ≤ Y → c.Coprime q →
      |∑ m ∈ Finset.Icc 1 ⌊Y⌋₊ with m ≡ c [MOD q], Λ m - Y / q.totient| ≤
        K * Y ^ (15 / 16 : ℝ) * Real.log Y := by
  classical
  obtain ⟨K, hK⟩ := exists_norm_sum_vonMangoldt_mul_char_sub_le
  refine ⟨|K|, fun Y hY q c hq hqY hc ↦ ?_⟩
  have : NeZero q := ⟨by omega⟩
  set a : ZMod q := (c : ZMod q)
  have ha : IsUnit a := (ZMod.isUnit_iff_coprime c q).mpr hc
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  set ψχ : DirichletCharacter ℂ q → ℂ := fun χ ↦ ∑ m ∈ Finset.Icc 1 ⌊Y⌋₊, (Λ m : ℂ) * χ m
  set δχ : DirichletCharacter ℂ q → ℂ := fun χ ↦ if χ = 1 then (Y : ℂ) else 0
  -- the residue class sum as a combination of twisted sums
  have hres : ((∑ m ∈ Finset.Icc 1 ⌊Y⌋₊ with m ≡ c [MOD q], Λ m : ℝ) : ℂ) =
      (q.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q, χ a⁻¹ * ψχ χ := by
    rw [Finset.sum_filter]
    have h (m : ℕ) : (if m ≡ c [MOD q] then Λ m else 0) = vonMangoldt.residueClass a m := by
      simp [vonMangoldt.residueClass, Set.indicator_apply, a, ZMod.natCast_eq_natCast_iff]
    simp_rw [h]
    push_cast
    simp_rw [vonMangoldt.residueClass_apply ha, ← Finset.mul_sum]
    rw [Finset.sum_comm]
    congr 1
    refine Finset.sum_congr rfl fun χ _ ↦ ?_
    simp only [ψχ, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ ↦ ?_
    ring
  -- only the principal character has a main term
  have ha' : IsUnit a⁻¹ := by
    obtain ⟨u, hu⟩ := ha
    rw [← hu, ZMod.inv_coe_unit]
    exact (u⁻¹).isUnit
  have hmain : ∑ χ : DirichletCharacter ℂ q, χ a⁻¹ * δχ χ = Y := by
    simp only [δχ, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rw [MulChar.one_apply ha', one_mul]
  have heq : ((∑ m ∈ Finset.Icc 1 ⌊Y⌋₊ with m ≡ c [MOD q], Λ m - Y / q.totient : ℝ) : ℂ) =
      (q.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q, χ a⁻¹ * (ψχ χ - δχ χ) := by
    have h : ((∑ m ∈ Finset.Icc 1 ⌊Y⌋₊ with m ≡ c [MOD q], Λ m - Y / q.totient : ℝ) : ℂ) =
        (q.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q, χ a⁻¹ * ψχ χ -
          (q.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q, χ a⁻¹ * δχ χ := by
      rw [hmain, Complex.ofReal_sub, hres]
      push_cast
      ring
    rw [h, ← mul_sub, ← Finset.sum_sub_distrib]
    simp_rw [mul_sub]
  -- each character contributes `O(Y^{15/16} log Y)`
  have hcard : (Finset.univ : Finset (DirichletCharacter ℂ q)).card = q.totient := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card,
      card_eq_totient_of_hasEnoughRootsOfUnity ℂ q]
  have hχ : ∀ χ : DirichletCharacter ℂ q, ‖χ a⁻¹ * (ψχ χ - δχ χ)‖ ≤
      |K| * Y ^ (15 / 16 : ℝ) * Real.log Y := by
    intro χ
    rw [norm_mul]
    have hYL : 0 ≤ Y ^ (15 / 16 : ℝ) * Real.log Y :=
      mul_nonneg (by positivity) (Real.log_nonneg (by linarith))
    calc ‖χ a⁻¹‖ * ‖ψχ χ - δχ χ‖ ≤ 1 * (K * Y ^ (15 / 16 : ℝ) * Real.log Y) :=
          mul_le_mul (χ.norm_le_one _) (hK χ Y hY hqY) (norm_nonneg _) zero_le_one
      _ ≤ |K| * Y ^ (15 / 16 : ℝ) * Real.log Y := by
          rw [one_mul, mul_assoc, mul_assoc]
          exact mul_le_mul_of_nonneg_right (le_abs_self K) hYL
  rw [← Real.norm_eq_abs, ← Complex.norm_real, heq, norm_mul, norm_inv, Complex.norm_natCast]
  calc (q.totient : ℝ)⁻¹ * ‖∑ χ : DirichletCharacter ℂ q, χ a⁻¹ * (ψχ χ - δχ χ)‖
      ≤ (q.totient : ℝ)⁻¹ *
          ∑ _χ : DirichletCharacter ℂ q, |K| * Y ^ (15 / 16 : ℝ) * Real.log Y := by
        gcongr
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun χ _ ↦ hχ χ)
    _ = |K| * Y ^ (15 / 16 : ℝ) * Real.log Y := by
        rw [Finset.sum_const, hcard, nsmul_eq_mul]
        field_simp

/-- `θ(Y; q, c) = Y / φ(q) + O(Y^{15/16} log² Y)`, uniformly for `q ≤ Y` and `c`
coprime to `q`. -/
theorem exists_abs_thetaAP_sub_le : ∃ K : ℝ, ∀ Y : ℝ, 2 ≤ Y → ∀ q c : ℕ, 1 ≤ q →
    (q : ℝ) ≤ Y → c.Coprime q →
      |thetaAP Y q c - Y / q.totient| ≤ K * Y ^ (15 / 16 : ℝ) * Real.log Y ^ 2 := by
  obtain ⟨K, hK⟩ := exists_abs_sum_vonMangoldt_modEq_sub_le
  refine ⟨(|K| + 2) / Real.log 2, fun Y hY q c hq hqY hc ↦ ?_⟩
  set S := (Finset.Icc 1 ⌊Y⌋₊).filter (· ≡ c [MOD q])
  -- `θ(Y; q, c)` is the prime part of `ψ(Y; q, c)`
  have hθ : thetaAP Y q c = ∑ m ∈ S with m.Prime, Λ m := by
    have hset :
        (Finset.Iic ⌊Y⌋₊).filter (fun p ↦ p.Prime ∧ p ≡ c [MOD q]) = S.filter Nat.Prime := by
      ext p
      simp only [S, Finset.mem_filter, Finset.mem_Iic, Finset.mem_Icc]
      constructor
      · rintro ⟨hp, hpp, hpc⟩
        exact ⟨⟨⟨hpp.one_lt.le, hp⟩, hpc⟩, hpp⟩
      · rintro ⟨⟨⟨_, hp⟩, hpc⟩, hpp⟩
        exact ⟨hp, hpp, hpc⟩
    rw [thetaAP, hset]
    exact Finset.sum_congr rfl fun p hp ↦ (vonMangoldt_apply_prime (Finset.mem_filter.mp hp).2).symm
  -- the higher prime powers contribute at most `2 √Y log Y`
  have hpow : ∑ m ∈ S with ¬ m.Prime, Λ m ≤ 2 * √Y * Real.log Y := by
    refine le_trans ?_ (Chebyshev.psi_sub_theta_le (by linarith))
    rw [Chebyshev.psi_sub_theta_eq_sum_not_prime]
    refine Finset.sum_le_sum_of_subset_of_nonneg (fun m hm ↦ ?_) fun _ _ _ ↦ vonMangoldt_nonneg
    simp only [S, Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc] at hm ⊢
    exact ⟨⟨by omega, hm.1.1.2⟩, hm.2⟩
  have hpow₀ : 0 ≤ ∑ m ∈ S with ¬ m.Prime, Λ m :=
    Finset.sum_nonneg fun _ _ ↦ vonMangoldt_nonneg
  have hsplit := Finset.sum_filter_add_sum_filter_not S Nat.Prime fun m ↦ Λ m
  have hψ := hK Y hY q c hq hqY hc
  -- assembling, with `X = Y^{15/16}` and `L = log Y`
  set X := Y ^ (15 / 16 : ℝ)
  set L := Real.log Y
  have hX : 0 ≤ X := by positivity
  have hL₂ : Real.log 2 ≤ L := Real.log_le_log (by norm_num) hY
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hsqrt : √Y ≤ X := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have h₁ : |thetaAP Y q c - Y / q.totient| ≤ (|K| + 2) * X * L := by
    have h₂ : |thetaAP Y q c - Y / q.totient| ≤
        |∑ m ∈ S, Λ m - Y / q.totient| + ∑ m ∈ S with ¬ m.Prime, Λ m := by
      have h₃ : thetaAP Y q c - Y / q.totient =
          (∑ m ∈ S, Λ m - Y / q.totient) - ∑ m ∈ S with ¬ m.Prime, Λ m := by
        rw [hθ, ← hsplit]
        ring
      rw [h₃]
      refine (abs_sub (∑ m ∈ S, Λ m - Y / q.totient) (∑ m ∈ S with ¬ m.Prime, Λ m)).trans ?_
      rw [abs_of_nonneg hpow₀]
    have h₄ : K * X * L ≤ |K| * X * L := by
      gcongr
      · linarith
      · exact le_abs_self K
    have h₅ : 2 * √Y * L ≤ 2 * X * L := by gcongr; linarith
    linarith
  calc |thetaAP Y q c - Y / q.totient| ≤ (|K| + 2) * X * L := h₁
    _ ≤ (|K| + 2) * X * (L * (L / Real.log 2)) := by
        gcongr
        rw [le_mul_iff_one_le_right (by linarith), one_le_div hlog2]
        exact hL₂
    _ = (|K| + 2) / Real.log 2 * X * L ^ 2 := by ring

end Erdos420
