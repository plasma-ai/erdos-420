module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.SelbergSieve

/-!
# Selberg's Λ² weights

For a `BoundingSieve` with sifting product `P`, density `ν`, and level `y ≥ 1`, put
`G(y) = ∑_{l ∣ P, l ≤ y} g(l)` with `g = selbergTerms`. Selberg's weights

  `λ_d = ν(d)⁻¹ ∑_{d ∣ m ∣ P} μ(m / d) y_m`,  `y_m = μ(m) g(m) / G(y)` for `m ≤ y`,

satisfy `λ_1 = 1`, vanish above `y`, obey `|λ_d| ≤ ν(d)⁻¹`, and make the main term of the
Λ² sieve exactly `1 / G(y)`: by Möbius inversion over multiples, `∑_{l ∣ d ∣ P} ν(d) λ_d = y_l`,
which diagonalizes the quadratic form of `BoundingSieve.mainSum_lambdaSquared_eq_sum_mul_sum_sq`.

If every `A_d = #{i : d ∣ a i}` is `ν(d) X` up to an error at most `d`, and `ν(d)⁻¹ ≤ d`,
the number of `i` with `a i` coprime to `P` is then at most `X / G(y) + y⁶`.
-/

@[expose] public section

namespace Erdos420

open Finset ArithmeticFunction BoundingSieve
open scoped ArithmeticFunction.Moebius

/-! ### Möbius inversion over multiples -/

/-- `∑_{l ∣ d ∣ m} μ(m / d)` is `1` if `m = l` and `0` otherwise. -/
private lemma sum_divisors_filter_dvd_moebius {l m : ℕ} (hm : m ≠ 0) :
    ∑ d ∈ m.divisors with l ∣ d, (μ (m / d) : ℝ) = if m = l then 1 else 0 := by
  by_cases hlm : l ∣ m
  · obtain ⟨k, rfl⟩ := hlm
    have hl : l ≠ 0 := left_ne_zero_of_mul hm
    have hk : k ≠ 0 := right_ne_zero_of_mul hm
    -- reindex `d = l e` with `e ∣ k`
    have hre : ∑ d ∈ (l * k).divisors with l ∣ d, (μ (l * k / d) : ℝ) =
        ∑ e ∈ k.divisors, (μ (k / e) : ℝ) := by
      refine sum_nbij' (fun d ↦ d / l) (fun e ↦ l * e) (fun d hd ↦ ?_) (fun e he ↦ ?_)
        (fun d hd ↦ ?_) (fun e _ ↦ ?_) (fun d hd ↦ ?_)
      · simp only [mem_filter, Nat.mem_divisors] at hd
        obtain ⟨⟨hdk, -⟩, e, rfl⟩ := hd
        simp only [Nat.mem_divisors]
        rw [Nat.mul_div_cancel_left e (Nat.pos_of_ne_zero hl)]
        exact ⟨Nat.dvd_of_mul_dvd_mul_left (Nat.pos_of_ne_zero hl) hdk, hk⟩
      · simp only [mem_filter, Nat.mem_divisors] at he ⊢
        exact ⟨⟨mul_dvd_mul_left l he.1, hm⟩, dvd_mul_right l e⟩
      · simp only [mem_filter] at hd
        exact Nat.mul_div_cancel' hd.2
      · exact Nat.mul_div_cancel_left e (Nat.pos_of_ne_zero hl)
      · simp only [mem_filter] at hd
        obtain ⟨e, rfl⟩ := hd.2
        rw [Nat.mul_div_cancel_left e (Nat.pos_of_ne_zero hl),
          Nat.mul_div_mul_left k e (Nat.pos_of_ne_zero hl)]
    have hsum : ∑ e ∈ k.divisors, (μ e : ℝ) = if k = 1 then 1 else 0 := by
      have h := congrArg (fun f : ArithmeticFunction ℝ ↦ f k) (coe_moebius_mul_coe_zeta (R := ℝ))
      simpa only [coe_mul_zeta_apply, intCoe_apply, one_apply] using h
    rw [hre, Nat.sum_div_divisors k fun e ↦ (μ e : ℝ), hsum]
    simp [Nat.mul_eq_left hl]
  · rw [ite_eq_right (by rintro rfl; exact hlm dvd_rfl)]
    refine sum_eq_zero fun d hd ↦ absurd ?_ hlm
    simp only [mem_filter, Nat.mem_divisors] at hd
    exact hd.2.trans hd.1.1

/-- Möbius inversion over multiples: `∑_{l ∣ d ∣ n} ∑_{d ∣ m ∣ n} μ(m / d) f(m) = f(l)`. -/
private lemma sum_dvd_sum_dvd_moebius {n l : ℕ} (hn : n ≠ 0) (hl : l ∣ n) (f : ℕ → ℝ) :
    ∑ d ∈ n.divisors with l ∣ d, ∑ m ∈ n.divisors with d ∣ m, (μ (m / d) : ℝ) * f m = f l := by
  rw [sum_comm' (t' := n.divisors) (s' := fun m ↦ {d ∈ m.divisors | l ∣ d})]
  · calc ∑ m ∈ n.divisors, ∑ d ∈ m.divisors with l ∣ d, (μ (m / d) : ℝ) * f m
        = ∑ m ∈ n.divisors, if m = l then f m else 0 := by
          refine sum_congr rfl fun m hm ↦ ?_
          rw [← sum_mul, sum_divisors_filter_dvd_moebius (Nat.pos_of_mem_divisors hm).ne']
          split_ifs <;> simp
      _ = f l := by rw [sum_ite_eq' n.divisors l f, ite_eq_left (Nat.mem_divisors.mpr ⟨hl, hn⟩)]
  · intro d m
    simp only [mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨⟨-, -⟩, hld⟩, ⟨hmn, -⟩, hdm⟩
      exact ⟨⟨⟨hdm, (Nat.pos_of_dvd_of_pos hmn (Nat.pos_of_ne_zero hn)).ne'⟩, hld⟩, hmn, hn⟩
    · rintro ⟨⟨⟨hdm, -⟩, hld⟩, hmn, -⟩
      exact ⟨⟨⟨hdm.trans hmn, hn⟩, hld⟩, ⟨hmn, hn⟩, hdm⟩

/-! ### The weights -/

variable (s : BoundingSieve)

/-- Selberg's `G(y) = ∑_{l ∣ P, l ≤ y} g(l)`. -/
noncomputable def selbergMass (y : ℝ) : ℝ :=
  ∑ l ∈ s.prodPrimes.divisors with ((l : ℕ) : ℝ) ≤ y, s.selbergTerms l

/-- The optimal `y_l = μ(l) g(l) / G(y)` for `l ≤ y`, and `0` above `y`. -/
noncomputable def selbergY (y : ℝ) (l : ℕ) : ℝ :=
  if (l : ℝ) ≤ y then μ l * s.selbergTerms l / selbergMass s y else 0

/-- Selberg's weights `λ_d = ν(d)⁻¹ ∑_{d ∣ m ∣ P} μ(m / d) y_m`. -/
noncomputable def selbergWeight (y : ℝ) (d : ℕ) : ℝ :=
  (s.nu d)⁻¹ * ∑ m ∈ s.prodPrimes.divisors with d ∣ m, (μ (m / d) : ℝ) * selbergY s y m

variable {s}

/-- `g(1) = 1`. -/
lemma selbergTerms_one : s.selbergTerms 1 = 1 := by
  simp [selbergTerms_apply, s.nu_mult.map_one]

/-- `G(y) > 0` for `y ≥ 1`, since `l = 1` contributes `g(1) = 1`. -/
lemma selbergMass_pos {y : ℝ} (hy : 1 ≤ y) : 0 < selbergMass s y := by
  have h1 : 1 ∈ {l ∈ s.prodPrimes.divisors | ((l : ℕ) : ℝ) ≤ y} := by
    simp [prodPrimes_ne_zero, hy]
  calc (0 : ℝ) < s.selbergTerms 1 := by rw [selbergTerms_one]; exact one_pos
    _ ≤ selbergMass s y := single_le_sum (fun l hl ↦
        (selbergTerms_pos (Nat.dvd_of_mem_divisors (mem_filter.mp hl).1)).le) h1

/-- `λ_1 = ∑_{m ≤ y} g(m) / G(y) = 1`. -/
lemma selbergWeight_one {y : ℝ} (hy : 1 ≤ y) : selbergWeight s y 1 = 1 := by
  have hG := selbergMass_pos (s := s) hy
  rw [selbergWeight, s.nu_mult.map_one, inv_one, one_mul,
    filter_true_of_mem fun m _ ↦ one_dvd m]
  calc ∑ m ∈ s.prodPrimes.divisors, (μ (m / 1) : ℝ) * selbergY s y m
      = ∑ m ∈ s.prodPrimes.divisors with ((m : ℕ) : ℝ) ≤ y, s.selbergTerms m / selbergMass s y := by
        rw [sum_filter]
        refine sum_congr rfl fun m hm ↦ ?_
        have hμ : (μ m : ℝ) ^ 2 = 1 := by
          exact_mod_cast moebius_sq_eq_one_of_squarefree (squarefree_of_mem_divisors_prodPrimes hm)
        rw [selbergY, Nat.div_one]
        split_ifs
        · rw [← mul_div_assoc, ← mul_assoc, ← sq, hμ, one_mul]
        · rw [mul_zero]
    _ = 1 := by rw [← sum_div, ← selbergMass, div_self hG.ne']

/-- `λ_d = 0` for `d > y`, since `y_m = 0` for every multiple `m` of `d`. -/
lemma selbergWeight_eq_zero {y : ℝ} {d : ℕ} (hd : y < d) : selbergWeight s y d = 0 := by
  rw [selbergWeight, sum_eq_zero, mul_zero]
  intro m hm
  simp only [mem_filter] at hm
  have : (d : ℝ) ≤ m := by exact_mod_cast Nat.le_of_dvd (Nat.pos_of_mem_divisors hm.1) hm.2
  rw [selbergY, ite_eq_right (by linarith), mul_zero]

/-- `|λ_d| ≤ ν(d)⁻¹`, since `∑_m |y_m| = 1`. -/
lemma abs_selbergWeight_le {y : ℝ} (hy : 1 ≤ y) {d : ℕ} (hd : d ∣ s.prodPrimes) :
    |selbergWeight s y d| ≤ (s.nu d)⁻¹ := by
  have hG := selbergMass_pos (s := s) hy
  have hν := nu_pos_of_dvd_prodPrimes hd
  rw [selbergWeight, abs_mul, abs_inv, abs_of_pos hν]
  refine mul_le_of_le_one_right (inv_pos.2 hν).le ?_
  calc |∑ m ∈ s.prodPrimes.divisors with d ∣ m, (μ (m / d) : ℝ) * selbergY s y m|
      ≤ ∑ m ∈ s.prodPrimes.divisors with d ∣ m, |selbergY s y m| := by
        refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun m _ ↦ ?_)
        rw [abs_mul]
        exact mul_le_of_le_one_left (abs_nonneg _) (by exact_mod_cast abs_moebius_le_one)
    _ ≤ ∑ m ∈ s.prodPrimes.divisors, |selbergY s y m| :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ ↦ abs_nonneg _
    _ ≤ ∑ m ∈ s.prodPrimes.divisors with ((m : ℕ) : ℝ) ≤ y, s.selbergTerms m / selbergMass s y := by
        rw [sum_filter]
        refine sum_le_sum fun m hm ↦ ?_
        have hg := selbergTerms_pos (s := s) (Nat.dvd_of_mem_divisors hm)
        rw [selbergY]
        split_ifs
        · rw [abs_div, abs_mul, abs_of_pos hG, abs_of_pos hg]
          gcongr
          exact mul_le_of_le_one_left hg.le (by exact_mod_cast abs_moebius_le_one)
        · rw [abs_zero]
    _ = 1 := by rw [← sum_div, ← selbergMass, div_self hG.ne']

/-- `∑_{l ∣ d ∣ P} ν(d) λ_d = y_l`. -/
lemma sum_nu_mul_selbergWeight {y : ℝ} {l : ℕ} (hl : l ∈ s.prodPrimes.divisors) :
    ∑ d ∈ s.prodPrimes.divisors, (if l ∣ d then s.nu d * selbergWeight s y d else 0) =
      selbergY s y l := by
  rw [← sum_filter]
  calc ∑ d ∈ s.prodPrimes.divisors with l ∣ d, s.nu d * selbergWeight s y d
      = ∑ d ∈ s.prodPrimes.divisors with l ∣ d,
          ∑ m ∈ s.prodPrimes.divisors with d ∣ m, (μ (m / d) : ℝ) * selbergY s y m := by
        refine sum_congr rfl fun d hd ↦ ?_
        rw [selbergWeight, ← mul_assoc,
          mul_inv_cancel₀ (nu_ne_zero (Nat.dvd_of_mem_divisors (mem_filter.mp hd).1)), one_mul]
    _ = selbergY s y l := sum_dvd_sum_dvd_moebius prodPrimes_ne_zero (Nat.dvd_of_mem_divisors hl) _

/-- The main term of Selberg's weights is `1 / G(y)`. -/
theorem mainSum_selbergWeight {y : ℝ} (hy : 1 ≤ y) :
    s.mainSum (lambdaSquared (selbergWeight s y)) = (selbergMass s y)⁻¹ := by
  have hG := selbergMass_pos (s := s) hy
  rw [mainSum_lambdaSquared_eq_sum_mul_sum_sq]
  calc ∑ l ∈ s.prodPrimes.divisors, (s.selbergTerms l)⁻¹ *
        (∑ d ∈ s.prodPrimes.divisors, if l ∣ d then s.nu d * selbergWeight s y d else 0) ^ 2
      = ∑ l ∈ s.prodPrimes.divisors, (s.selbergTerms l)⁻¹ * selbergY s y l ^ 2 :=
        sum_congr rfl fun l hl ↦ by rw [sum_nu_mul_selbergWeight hl]
    _ = ∑ l ∈ s.prodPrimes.divisors with ((l : ℕ) : ℝ) ≤ y,
          s.selbergTerms l / selbergMass s y ^ 2 := by
        rw [sum_filter]
        refine sum_congr rfl fun l hl ↦ ?_
        have hg := selbergTerms_pos (s := s) (Nat.dvd_of_mem_divisors hl)
        have hμ : (μ l : ℝ) ^ 2 = 1 := by
          exact_mod_cast moebius_sq_eq_one_of_squarefree (squarefree_of_mem_divisors_prodPrimes hl)
        rw [selbergY]
        split_ifs
        · rw [div_pow, mul_pow, hμ]
          field_simp
        · simp
    _ = (selbergMass s y)⁻¹ := by
        rw [← sum_div, ← selbergMass]
        field_simp

/-! ### The sieve bound -/

/-- The Λ² sieve with Selberg's weights at level `y`: if `#{i : d ∣ a i} = ν(d) X + O(d)` and
`ν(d)⁻¹ ≤ d` for `d ∣ P`, then at most `X / G(y) + y⁶` of the `a i` are coprime to `P`. -/
theorem card_filter_coprime_le {ι : Type*} (I : Finset ι) (a : ι → ℕ) {y : ℝ} (hy : 1 ≤ y)
    (hν : ∀ d ∈ s.prodPrimes.divisors, (s.nu d)⁻¹ ≤ d)
    (hR : ∀ d ∈ s.prodPrimes.divisors,
      |(#{i ∈ I | d ∣ a i} : ℝ) - s.nu d * s.totalMass| ≤ d) :
    (#{i ∈ I | Nat.Coprime s.prodPrimes (a i)} : ℝ) ≤
      s.totalMass / selbergMass s y + y ^ 6 := by
  set P := s.prodPrimes
  set w := selbergWeight s y with hw
  have hP₀ : P ≠ 0 := prodPrimes_ne_zero
  -- every coprime `a i` has `∑_{d ∣ (P, a i)} λ²_d ≥ 1`
  have h₁ : (#{i ∈ I | Nat.Coprime P (a i)} : ℝ) ≤
      ∑ d ∈ P.divisors, lambdaSquared w d * #{i ∈ I | d ∣ a i} := by
    calc (#{i ∈ I | Nat.Coprime P (a i)} : ℝ)
        = ∑ i ∈ I, (if Nat.gcd P (a i) = 1 then 1 else 0 : ℝ) := by
          rw [card_filter, Nat.cast_sum]
          exact sum_congr rfl fun i _ ↦ by split_ifs <;> simp_all [Nat.Coprime]
      _ ≤ ∑ i ∈ I, ∑ d ∈ (Nat.gcd P (a i)).divisors, lambdaSquared w d :=
          sum_le_sum fun i _ ↦ upperMoebius_lambdaSquared w (selbergWeight_one hy) _
      _ = ∑ i ∈ I, ∑ d ∈ P.divisors, if d ∣ a i then lambdaSquared w d else 0 := by
          refine sum_congr rfl fun i _ ↦ ?_
          rw [← sum_filter]
          congr 1
          ext d
          simp [Nat.dvd_gcd_iff, hP₀, Nat.gcd_eq_zero_iff]
      _ = ∑ d ∈ P.divisors, lambdaSquared w d * #{i ∈ I | d ∣ a i} := by
          rw [sum_comm]
          refine sum_congr rfl fun d _ ↦ ?_
          rw [← sum_filter, sum_const, nsmul_eq_mul, mul_comm]
  -- split off the main term
  have h₂ : ∑ d ∈ P.divisors, lambdaSquared w d * #{i ∈ I | d ∣ a i} ≤
      s.totalMass / selbergMass s y + ∑ d ∈ P.divisors, |lambdaSquared w d| * d := by
    calc ∑ d ∈ P.divisors, lambdaSquared w d * #{i ∈ I | d ∣ a i}
        = s.totalMass * s.mainSum (lambdaSquared w) + ∑ d ∈ P.divisors,
            lambdaSquared w d * ((#{i ∈ I | d ∣ a i} : ℝ) - s.nu d * s.totalMass) := by
          rw [mainSum, mul_sum, ← sum_add_distrib]
          exact sum_congr rfl fun d _ ↦ by ring
      _ ≤ s.totalMass / selbergMass s y + ∑ d ∈ P.divisors, |lambdaSquared w d| * d := by
          rw [hw, mainSum_selbergWeight hy, ← div_eq_mul_inv]
          refine add_le_add le_rfl (sum_le_sum fun d hd ↦ (le_abs_self _).trans ?_)
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (hR d hd) (abs_nonneg _)
  -- the error is at most `(∑_d |λ_d| d)²`
  have h₃ : ∑ d ∈ P.divisors, |lambdaSquared w d| * d ≤
      (∑ d ∈ P.divisors, |w d| * d) ^ 2 := by
    calc ∑ d ∈ P.divisors, |lambdaSquared w d| * d
        ≤ ∑ d ∈ P.divisors, ∑ d₁ ∈ d.divisors, ∑ d₂ ∈ d.divisors,
            if d = d₁.lcm d₂ then |w d₁| * d₁ * (|w d₂| * d₂) else 0 := by
          refine sum_le_sum fun d hd ↦ ?_
          have hd₀ : d ≠ 0 := (Nat.pos_of_mem_divisors hd).ne'
          rw [lambdaSquared]
          refine (mul_le_mul_of_nonneg_right ((abs_sum_le_sum_abs _ _).trans
            (sum_le_sum fun _ _ ↦ abs_sum_le_sum_abs _ _)) (Nat.cast_nonneg _)).trans ?_
          rw [sum_mul]
          refine sum_le_sum fun d₁ hd₁ ↦ ?_
          rw [sum_mul]
          refine sum_le_sum fun d₂ hd₂ ↦ ?_
          split_ifs with h
          · have hd₁₀ := Nat.pos_of_mem_divisors hd₁
            have hd₂₀ := Nat.pos_of_mem_divisors hd₂
            have hle : (d : ℝ) ≤ d₁ * d₂ := by
              rw [h]
              exact_mod_cast Nat.le_of_dvd (Nat.mul_pos hd₁₀ hd₂₀) (Nat.lcm_dvd_mul d₁ d₂)
            rw [abs_mul]
            calc |w d₁| * |w d₂| * d ≤ |w d₁| * |w d₂| * (d₁ * d₂) := by gcongr
              _ = |w d₁| * d₁ * (|w d₂| * d₂) := by ring
          · simp
      _ ≤ ∑ d ∈ P.divisors, ∑ d₁ ∈ P.divisors, ∑ d₂ ∈ P.divisors,
            if d = d₁.lcm d₂ then |w d₁| * d₁ * (|w d₂| * d₂) else 0 := by
          have hnn : ∀ d d₁ d₂ : ℕ,
              0 ≤ if d = d₁.lcm d₂ then |w d₁| * d₁ * (|w d₂| * d₂) else (0 : ℝ) := by
            intro d d₁ d₂
            split_ifs <;> positivity
          refine sum_le_sum fun d hd ↦ ?_
          have hsub : d.divisors ⊆ P.divisors :=
            Nat.divisors_subset_of_dvd hP₀ (Nat.dvd_of_mem_divisors hd)
          calc ∑ d₁ ∈ d.divisors, ∑ d₂ ∈ d.divisors,
                (if d = d₁.lcm d₂ then |w d₁| * d₁ * (|w d₂| * d₂) else 0)
              ≤ ∑ d₁ ∈ d.divisors, ∑ d₂ ∈ P.divisors,
                (if d = d₁.lcm d₂ then |w d₁| * d₁ * (|w d₂| * d₂) else 0) :=
                sum_le_sum fun d₁ _ ↦ sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ ↦ hnn _ _ _
            _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ ↦
                sum_nonneg fun _ _ ↦ hnn _ _ _
      _ = ∑ d₁ ∈ P.divisors, ∑ d₂ ∈ P.divisors, |w d₁| * d₁ * (|w d₂| * d₂) := by
          rw [sum_comm]
          refine sum_congr rfl fun d₁ hd₁ ↦ ?_
          rw [sum_comm]
          refine sum_congr rfl fun d₂ hd₂ ↦ ?_
          rw [sum_ite_eq' P.divisors (d₁.lcm d₂), ite_eq_left]
          exact Nat.mem_divisors.mpr ⟨Nat.lcm_dvd (Nat.dvd_of_mem_divisors hd₁)
            (Nat.dvd_of_mem_divisors hd₂), hP₀⟩
      _ = (∑ d ∈ P.divisors, |w d| * d) ^ 2 := by
          rw [sq, sum_mul_sum]
  -- each weight is at most `ν(d)⁻¹ ≤ d`, and vanishes above `y`
  have h₄ : ∑ d ∈ P.divisors, |w d| * d ≤ y ^ 3 := by
    have hcard : (#{d ∈ P.divisors | ((d : ℕ) : ℝ) ≤ y} : ℝ) ≤ y := by
      have hsub : {d ∈ P.divisors | ((d : ℕ) : ℝ) ≤ y} ⊆ Icc 1 ⌊y⌋₊ := by
        intro d hd
        simp only [mem_filter] at hd
        exact mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hd.1, Nat.le_floor hd.2⟩
      calc (#{d ∈ P.divisors | ((d : ℕ) : ℝ) ≤ y} : ℝ) ≤ (#(Icc 1 ⌊y⌋₊) : ℝ) := by
            exact_mod_cast card_le_card hsub
        _ ≤ y := by
            rw [Nat.card_Icc, Nat.add_sub_cancel]
            exact Nat.floor_le (by linarith)
    calc ∑ d ∈ P.divisors, |w d| * d = ∑ d ∈ P.divisors with ((d : ℕ) : ℝ) ≤ y, |w d| * d := by
          rw [sum_filter]
          refine sum_congr rfl fun d _ ↦ ?_
          split_ifs with h
          · rfl
          · rw [hw, selbergWeight_eq_zero (not_le.mp h), abs_zero, zero_mul]
      _ ≤ ∑ d ∈ P.divisors with ((d : ℕ) : ℝ) ≤ y, y ^ 2 := by
          refine sum_le_sum fun d hd ↦ ?_
          simp only [mem_filter] at hd
          have hd₀ : (0 : ℝ) ≤ d := Nat.cast_nonneg _
          calc |w d| * d ≤ d * d := by
                gcongr
                exact (abs_selbergWeight_le hy (Nat.dvd_of_mem_divisors hd.1)).trans (hν d hd.1)
            _ ≤ y ^ 2 := by rw [sq]; exact mul_le_mul hd.2 hd.2 hd₀ (by linarith)
      _ ≤ y * y ^ 2 := by
          rw [sum_const, nsmul_eq_mul]
          exact mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = y ^ 3 := by ring
  calc (#{i ∈ I | Nat.Coprime P (a i)} : ℝ)
      ≤ s.totalMass / selbergMass s y + ∑ d ∈ P.divisors, |lambdaSquared w d| * d :=
        h₁.trans h₂
    _ ≤ s.totalMass / selbergMass s y + (y ^ 3) ^ 2 := by
        gcongr
        exact h₃.trans (pow_le_pow_left₀ (sum_nonneg fun _ _ ↦ by positivity) h₄ 2)
    _ = s.totalMass / selbergMass s y + y ^ 6 := by ring

end Erdos420
