module

public import Erdos420.Elementary.Mertens
public import Erdos420.Sieve.Selberg.Count
public import Erdos420.Sieve.Selberg.Mass
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# An upper-bound sieve for linear forms

Let `F_j(v) = α_j v + β_j` for `j < κ`, and suppose that above `v₀` no prime
divides a leading coefficient `α_j` or a determinant `α_i β_j − α_j β_i`. Then
for each prime `v₀ < p ≤ Z` the product of the forms has exactly `κ` roots
modulo `p`. The Selberg sieve with level `Z` bounds the number of `v` in an
interval of length `V` with no `F_j(v)` divisible by such a prime by
`≪_κ V (log v₀ / log Z)^κ + Z³`, uniformly in the forms.

The weights are Selberg's minimizing ones for `g(p) = κ / (p − κ)`. We sift only by
the primes `v₀ < p ≤ T = Z^{1/(24κ)}`, which can only enlarge the sifted set, at
level `y = √Z`. The weights satisfy `|λ_d| ≤ ν(d)⁻¹ ≤ d` with `ν(d) = ∏_{p ∣ d} κ / p`,
which bounds the remainder by `y⁶ = Z³` (`Erdos420.card_filter_coprime_le`). Mertens'
first theorem gives `∑_p g(p) log p ≤ 2κ log (4T) ≤ log y / 2`, so Rankin's trick in
Markov's form gives `G(y) ≥ ∏_{v₀ < p ≤ T} (1 − κ / p)⁻¹ / 2 ≥ exp (κ ∑ 1/p) / 2`
(`Erdos420.prod_one_add_selbergTerms_le`). Mertens' second theorem bounds this below by
`≫_κ (log T / log v₀)^κ ≍_κ (log Z / log v₀)^κ`.
-/

@[expose] public section

namespace Erdos420

open Finset Real BoundingSieve
open ArithmeticFunction hiding log

/-! ### The sieve setup -/

/-- The sifting primes `v₀ < p ≤ T`. -/
noncomputable def siftingPrimes (v₀ T : ℝ) : Finset ℕ :=
  {p ∈ Iic ⌊T⌋₊ | p.Prime ∧ v₀ < p}

/-- Membership in the sifting primes. -/
lemma mem_siftingPrimes {v₀ T : ℝ} {p : ℕ} :
    p ∈ siftingPrimes v₀ T ↔ p ≤ ⌊T⌋₊ ∧ p.Prime ∧ v₀ < p := by
  simp [siftingPrimes]

/-- The primes of `∏_{v₀ < p ≤ T} p` are the sifting primes. -/
lemma primeFactors_prod_siftingPrimes (v₀ T : ℝ) :
    (∏ p ∈ siftingPrimes v₀ T, p).primeFactors = siftingPrimes v₀ T :=
  Nat.primeFactors_prod fun _ hp ↦ (mem_siftingPrimes.mp hp).2.1

/-- The product of the sifting primes is squarefree. -/
lemma squarefree_prod_siftingPrimes (v₀ T : ℝ) : Squarefree (∏ p ∈ siftingPrimes v₀ T, p) :=
  Finset.squarefree_prod_of_pairwise_isCoprime
    (fun _ hp _ hq hpq ↦ Nat.coprime_iff_isRelPrime.mp ((Nat.coprime_primes
      (mem_siftingPrimes.mp hp).2.1 (mem_siftingPrimes.mp hq).2.1).mpr hpq))
    fun _ hp ↦ (mem_siftingPrimes.mp hp).2.1.squarefree

/-- The density `ν(d) = ∏_{p ∣ d} κ / p` of the multiples of `d` among the roots. -/
noncomputable def formsNu (κ : ℕ) : ArithmeticFunction ℝ :=
  prodPrimeFactors fun p ↦ (κ : ℝ) / p

/-- `ν(p) = κ / p` at a prime `p`. -/
lemma formsNu_prime {κ p : ℕ} (hp : p.Prime) : formsNu κ p = κ / p := by
  rw [formsNu, prodPrimeFactors_apply hp.ne_zero, hp.primeFactors, prod_singleton]

/-- The sieve problem: the primes `v₀ < p ≤ T`, the density `ν`, and the total mass `V`. -/
noncomputable def formsSieve (κ : ℕ) (hκ : 1 ≤ κ) (v₀ T : ℝ) (hv₀ : (κ : ℝ) ≤ v₀) (V : ℕ) :
    BoundingSieve where
  support := ∅
  prodPrimes := ∏ p ∈ siftingPrimes v₀ T, p
  prodPrimes_squarefree := squarefree_prod_siftingPrimes v₀ T
  weights := fun _ ↦ 0
  weights_nonneg := fun _ ↦ le_rfl
  totalMass := V
  nu := formsNu κ
  nu_mult := IsMultiplicative.prodPrimeFactors _
  nu_pos_of_prime := fun p hp _ ↦ by
    rw [formsNu_prime hp]
    have : (1 : ℝ) ≤ κ := by exact_mod_cast hκ
    have : (0 : ℝ) < p := by exact_mod_cast hp.pos
    positivity
  nu_lt_one_of_prime := fun p hp hpP ↦ by
    rw [formsNu_prime hp]
    have hpS : p ∈ siftingPrimes v₀ T := by
      rw [← primeFactors_prod_siftingPrimes]
      exact Nat.mem_primeFactors.mpr ⟨hp, hpP, (squarefree_prod_siftingPrimes v₀ T).ne_zero⟩
    have hp₀ : (0 : ℝ) < p := by exact_mod_cast hp.pos
    rw [div_lt_one hp₀]
    exact hv₀.trans_lt (mem_siftingPrimes.mp hpS).2.2

/-! ### The sieve bound for the primes up to `T` -/

/-- The Λ² sieve for the forms with the primes `v₀ < p ≤ T` at level `y`: at most
`2 V / exp (κ ∑_{v₀ < p ≤ T} 1 / p) + y⁶` of the `v` avoid all roots, once
`2κ (log T + log 4) ≤ (log y) / 2`. -/
lemma card_sifted_le_of_level {κ : ℕ} (hκ : 1 ≤ κ) (α β : Fin κ → ℤ) {v₀ T y : ℝ} (v₁ : ℤ)
    (V : ℕ) (hv₀ : 2 * (κ : ℝ) ≤ v₀) (hT : 1 ≤ T) (hy : 1 < y)
    (hTy : 2 * κ * (log T + log 4) ≤ log y / 2)
    (hprime : ∀ p : ℕ, p.Prime → v₀ < p →
      (∀ j, ¬(p : ℤ) ∣ α j) ∧ ∀ i j, i ≠ j → ¬(p : ℤ) ∣ α i * β j - α j * β i) :
    (#{v ∈ Ico v₁ (v₁ + V) | ∀ j, ∀ p ∈ siftingPrimes v₀ T, ¬(p : ℤ) ∣ α j * v + β j} : ℝ) ≤
      2 * V / exp (κ * ∑ p ∈ siftingPrimes v₀ T, (1 : ℝ) / p) + y ^ 6 := by
  have hκ' : (1 : ℝ) ≤ κ := by exact_mod_cast hκ
  have hκv₀ : (κ : ℝ) ≤ v₀ := by linarith
  set s := formsSieve κ hκ v₀ T hκv₀ V
  have hP : s.prodPrimes.primeFactors = siftingPrimes v₀ T := primeFactors_prod_siftingPrimes v₀ T
  -- every sifting prime exceeds `2κ`
  have hbig : ∀ p ∈ siftingPrimes v₀ T, 2 * (κ : ℝ) < p :=
    fun p hp ↦ hv₀.trans_lt (mem_siftingPrimes.mp hp).2.2
  -- `ν(d)⁻¹ ≤ d`
  have hν : ∀ d ∈ s.prodPrimes.divisors, (s.nu d)⁻¹ ≤ d := by
    intro d hd
    have hdsq := squarefree_of_mem_divisors_prodPrimes hd
    change (formsNu κ d)⁻¹ ≤ d
    rw [formsNu, prodPrimeFactors_apply hdsq.ne_zero, ← prod_inv_distrib]
    conv_rhs => rw [← Nat.prod_primeFactors_of_squarefree hdsq, Nat.cast_prod]
    refine prod_le_prod₀ (fun p _ ↦ by positivity) fun p hp ↦ ?_
    have hp₀ : (0 : ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos
    rw [inv_div]
    exact div_le_self hp₀.le hκ'
  -- the counts of multiples of `d`
  have hR : ∀ d ∈ s.prodPrimes.divisors,
      |(#{v ∈ Ico v₁ (v₁ + V) | d ∣ (formsProd α β v).natAbs} : ℝ) - s.nu d * s.totalMass| ≤
        d := by
    intro d hd
    have hdsq := squarefree_of_mem_divisors_prodPrimes hd
    have hdP := Nat.dvd_of_mem_divisors hd
    have h := abs_card_filter_dvd_formsProd_sub_le α β hdsq (fun p hp ↦ ?_) v₁ V
    · simp only [← Int.natCast_dvd]
      change |_ - formsNu κ d * V| ≤ _
      rwa [formsNu, prodPrimeFactors_apply hdsq.ne_zero, mul_comm]
    · have hpS : p ∈ siftingPrimes v₀ T := by
        rw [← hP]
        exact Nat.primeFactors_mono hdP s.prodPrimes_ne_zero hp
      exact hprime p (mem_siftingPrimes.mp hpS).2.1 (mem_siftingPrimes.mp hpS).2.2
  have hsieve := card_filter_coprime_le (s := s) (Ico v₁ (v₁ + V))
    (fun v : ℤ ↦ (formsProd α β v).natAbs) hy.le hν hR
  -- sifted `v` give `F(v)` coprime to `P`
  have hsub : {v ∈ Ico v₁ (v₁ + V) | ∀ j, ∀ p ∈ siftingPrimes v₀ T, ¬(p : ℤ) ∣ α j * v + β j} ⊆
      {v ∈ Ico v₁ (v₁ + V) | Nat.Coprime s.prodPrimes (formsProd α β v).natAbs} := by
    intro v hv
    simp only [mem_filter] at hv ⊢
    refine ⟨hv.1, Nat.coprime_of_dvd fun p hp hpP hpF ↦ ?_⟩
    have hpS : p ∈ siftingPrimes v₀ T := by
      rw [← hP]
      exact Nat.mem_primeFactors.mpr ⟨hp, hpP, s.prodPrimes_ne_zero⟩
    rw [← Int.natCast_dvd, formsProd] at hpF
    obtain ⟨j, -, hj⟩ := (Nat.prime_iff_prime_int.mp hp).dvd_finsetProd_iff _ |>.mp hpF
    simp only [Int.cast_id] at hj
    exact hv.2 j p hpS hj
  -- the lower bound for `G(y)`
  have hG : exp (κ * ∑ p ∈ siftingPrimes v₀ T, (1 : ℝ) / p) ≤ 2 * selbergMass s y := by
    have hsum : ∑ p ∈ s.prodPrimes.primeFactors, s.nu p =
        κ * ∑ p ∈ siftingPrimes v₀ T, (1 : ℝ) / p := by
      rw [hP, mul_sum]
      refine sum_congr rfl fun p hp ↦ ?_
      change formsNu κ p = _
      rw [formsNu_prime (mem_siftingPrimes.mp hp).2.1, mul_one_div]
    rw [← hsum]
    refine exp_sum_nu_le_prod.trans (prod_one_add_selbergTerms_le hy ?_)
    -- `g(p) ≤ 2κ / p`, and Mertens' first theorem
    have hg : ∀ p ∈ s.prodPrimes.primeFactors, s.selbergTerms p ≤ 2 * κ * (1 / p) := by
      intro p hp
      have hp' := Nat.mem_primeFactors.mp hp
      have hp₀ : (0 : ℝ) < p := by exact_mod_cast hp'.1.pos
      have hν₀ : s.nu p = κ / p := formsNu_prime hp'.1
      have hνle : s.nu p ≤ 1 / 2 := by
        rw [hν₀, div_le_iff₀ hp₀]
        linarith [hbig p (hP ▸ hp)]
      have hνnn : 0 ≤ s.nu p := by rw [hν₀]; positivity
      have h1 := one_add_selbergTerms_of_prime hp'.1 hp'.2.1
      have h2 : (1 - s.nu p)⁻¹ ≤ 1 + 2 * s.nu p := by
        rw [inv_le_iff_one_le_mul₀ (by linarith)]
        nlinarith
      rw [mul_one_div, mul_div_assoc, ← hν₀]
      linarith
    calc ∑ p ∈ s.prodPrimes.primeFactors, s.selbergTerms p * log p
        ≤ ∑ p ∈ s.prodPrimes.primeFactors, 2 * κ * (1 / p) * log p := by
          refine sum_le_sum fun p hp ↦ mul_le_mul_of_nonneg_right (hg p hp) ?_
          exact log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt.le)
      _ = 2 * κ * ∑ p ∈ siftingPrimes v₀ T, log p / p := by
          rw [hP, mul_sum]
          exact sum_congr rfl fun p _ ↦ by ring
      _ ≤ 2 * κ * (log T + log 4) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          have hT₁ : 1 ≤ ⌊T⌋₊ := Nat.le_floor (by exact_mod_cast hT)
          calc ∑ p ∈ siftingPrimes v₀ T, log p / p ≤ ∑ p ∈ Nat.primesLE ⌊T⌋₊, log p / p := by
                refine sum_le_sum_of_subset_of_nonneg (fun p hp ↦ ?_) fun p hp _ ↦ ?_
                · have := mem_siftingPrimes.mp hp
                  exact Nat.mem_primesLE.mpr ⟨this.1, this.2.1⟩
                · have := (Nat.mem_primesLE.mp hp).2
                  exact div_nonneg (log_nonneg (by exact_mod_cast this.one_lt.le))
                    (Nat.cast_nonneg _)
            _ ≤ log ⌊T⌋₊ + log 4 := sum_primesLE_log_div_le hT₁
            _ ≤ log T + log 4 := by
                gcongr
                exact Nat.floor_le (by linarith)
      _ ≤ log y / 2 := hTy
  have hexp := exp_pos (κ * ∑ p ∈ siftingPrimes v₀ T, (1 : ℝ) / p)
  calc (#{v ∈ Ico v₁ (v₁ + V) | ∀ j, ∀ p ∈ siftingPrimes v₀ T, ¬(p : ℤ) ∣ α j * v + β j} : ℝ)
      ≤ #{v ∈ Ico v₁ (v₁ + V) | Nat.Coprime s.prodPrimes (formsProd α β v).natAbs} := by
        exact_mod_cast card_le_card hsub
    _ ≤ s.totalMass / selbergMass s y + y ^ 6 := hsieve
    _ ≤ 2 * V / exp (κ * ∑ p ∈ siftingPrimes v₀ T, (1 : ℝ) / p) + y ^ 6 := by
        refine add_le_add ?_ le_rfl
        change (V : ℝ) / selbergMass s y ≤ _
        rw [div_le_div_iff₀ (selbergMass_pos hy.le) hexp]
        nlinarith [Nat.cast_nonneg (α := ℝ) V]

/-! ### The main bound -/

open scoped Classical in
/-- The Selberg upper bound for `κ` linear forms sifted by the primes in
`(v₀, Z]`, uniformly in the forms. -/
theorem exists_card_sifted_linear_forms_le (κ : ℕ) : ∃ C : ℝ,
    ∀ (α β : Fin κ → ℤ) (v₀ Z : ℝ) (v₁ : ℤ) (V : ℕ),
      2 ≤ v₀ → (κ : ℝ) ^ 2 ≤ v₀ → Real.log Z ≤ v₀ → v₀ ^ (100 * κ) ≤ Z →
      (∀ p : ℕ, p.Prime → v₀ < p →
        (∀ j, ¬ (p : ℤ) ∣ α j) ∧ ∀ i j, i ≠ j → ¬ (p : ℤ) ∣ α i * β j - α j * β i) →
      (((Finset.Ico v₁ (v₁ + V)).filter fun v ↦ ∀ j, ∀ p : ℕ, p.Prime → v₀ < p → (p : ℝ) ≤ Z →
          ¬ (p : ℤ) ∣ α j * v + β j).card : ℝ) ≤
        C * V * (Real.log v₀ / Real.log Z) ^ κ + C * Z ^ 3 := by
  rcases Nat.eq_zero_or_pos κ with rfl | hκ
  · -- no forms: the count is at most `V`
    refine ⟨1, fun α β v₀ Z v₁ V _ _ _ hZ _ ↦ ?_⟩
    rw [mul_zero, pow_zero] at hZ
    calc (((Finset.Ico v₁ (v₁ + V)).filter fun v ↦ ∀ j, ∀ p : ℕ, p.Prime → v₀ < p →
          (p : ℝ) ≤ Z → ¬(p : ℤ) ∣ α j * v + β j).card : ℝ)
        ≤ #(Ico v₁ (v₁ + V)) := by exact_mod_cast card_filter_le _ _
      _ = V := by simp
      _ ≤ 1 * V * (log v₀ / log Z) ^ 0 + 1 * Z ^ 3 := by
          have : 0 ≤ Z ^ 3 := by positivity
          simp only [pow_zero, mul_one, one_mul]
          linarith
  obtain ⟨Cm, hCm⟩ := exists_abs_sum_inv_prime_sub_log_log_le
  have hCm₀ : 0 ≤ Cm := (abs_nonneg _).trans (hCm 2 le_rfl)
  refine ⟨2 * exp (2 * κ * Cm) * (24 * κ) ^ κ,
    fun α β v₀ Z v₁ V hv₀ hv₀κ _ hZ hprime ↦ ?_⟩
  have hκ' : (1 : ℝ) ≤ κ := by exact_mod_cast hκ
  have hv₀2κ : 2 * (κ : ℝ) ≤ v₀ := by
    rcases Nat.lt_or_ge κ 2 with h | h
    · have h1 : κ = 1 := by omega
      rw [h1]
      push_cast
      linarith
    · have : (2 : ℝ) ≤ κ := by exact_mod_cast h
      nlinarith
  have hlogv₀ : 0 < log v₀ := log_pos (by linarith)
  -- `log Z ≥ 100 κ log v₀`
  have hZ₀ : 0 < Z := lt_of_lt_of_le (by positivity) hZ
  have hlogZ : 100 * κ * log v₀ ≤ log Z := by
    have := log_le_log (by positivity) hZ
    rw [log_pow] at this
    push_cast at this
    linarith
  have hlogZ₀ : 0 < log Z := lt_of_lt_of_le (by positivity) hlogZ
  have hZ₁ : 1 < Z := by
    by_contra! h
    linarith [log_nonpos hZ₀.le h]
  -- the sifting range `T = Z^{1/(24κ)}` and the level `y = √Z`
  set T := Z ^ ((1 : ℝ) / (24 * κ)) with hT_def
  have hlogT : log T = log Z / (24 * κ) := by
    rw [hT_def, log_rpow hZ₀]
    ring
  have hT₁ : 1 ≤ T := one_le_rpow hZ₁.le (by positivity)
  have hTZ : T ≤ Z := by
    calc T ≤ Z ^ (1 : ℝ) :=
          rpow_le_rpow_of_exponent_le hZ₁.le (by rw [div_le_one (by positivity)]; linarith)
      _ = Z := rpow_one Z
  have hlogv₀T : log v₀ ≤ log T := by
    rw [hlogT, le_div_iff₀ (by positivity)]
    nlinarith
  have hv₀T : v₀ ≤ T := (log_le_log_iff (by linarith) (by linarith)).mp hlogv₀T
  set y := √Z with hy_def
  have hy : 1 < y := by
    rw [hy_def, lt_sqrt zero_le_one]
    linarith
  have hlogy : log y = log Z / 2 := log_sqrt hZ₀.le
  have hTy : 2 * κ * (log T + log 4) ≤ log y / 2 := by
    have hlog2 : log 2 ≤ log v₀ := log_le_log (by norm_num) hv₀
    have h12 : 2 * κ * (log Z / (24 * κ)) = log Z / 12 := by
      field_simp
      ring
    have hκ2 : κ * log 2 ≤ κ * log v₀ := mul_le_mul_of_nonneg_left hlog2 (by positivity)
    rw [hlogT, hlogy, log_four_eq, mul_add, h12]
    linarith
  have hcore := card_sifted_le_of_level hκ α β v₁ V hv₀2κ hT₁ hy hTy hprime
  -- sifting by fewer primes only enlarges the set
  have hsub : ((Finset.Ico v₁ (v₁ + V)).filter fun v ↦ ∀ j, ∀ p : ℕ, p.Prime → v₀ < p →
      (p : ℝ) ≤ Z → ¬(p : ℤ) ∣ α j * v + β j) ⊆
      {v ∈ Ico v₁ (v₁ + V) | ∀ j, ∀ p ∈ siftingPrimes v₀ T, ¬(p : ℤ) ∣ α j * v + β j} := by
    intro v hv
    simp only [mem_filter] at hv ⊢
    refine ⟨hv.1, fun j p hp ↦ ?_⟩
    have hp' := mem_siftingPrimes.mp hp
    refine hv.2 j p hp'.2.1 hp'.2.2 (le_trans ?_ hTZ)
    exact (Nat.cast_le.mpr hp'.1).trans (Nat.floor_le (by linarith))
  -- Mertens: `∑_{v₀ < p ≤ T} 1 / p ≥ log log T − log log v₀ − 2 Cm`
  have hmertens : log (log T) - log (log v₀) - 2 * Cm ≤
      ∑ p ∈ siftingPrimes v₀ T, (1 : ℝ) / p := by
    have h₁ := hCm T (by linarith)
    have h₂ := hCm v₀ hv₀
    have hsplit : ∑ p ∈ (Iic ⌊T⌋₊).filter Nat.Prime, (1 : ℝ) / p =
        ∑ p ∈ siftingPrimes v₀ T, (1 : ℝ) / p +
          ∑ p ∈ (Iic ⌊v₀⌋₊).filter Nat.Prime, (1 : ℝ) / p := by
      rw [← sum_filter_add_sum_filter_not ((Iic ⌊T⌋₊).filter Nat.Prime) fun p : ℕ ↦ v₀ < p,
        siftingPrimes, filter_filter, filter_filter]
      congr 2
      ext p
      simp only [mem_filter, mem_Iic, not_lt]
      constructor
      · rintro ⟨-, hp, hpv⟩
        exact ⟨Nat.le_floor hpv, hp⟩
      · rintro ⟨hpv, hp⟩
        refine ⟨hpv.trans (Nat.floor_le_floor hv₀T), hp, ?_⟩
        exact (Nat.cast_le.mpr hpv).trans (Nat.floor_le (by linarith))
    rw [abs_le] at h₁ h₂
    linarith
  -- assemble
  set E := exp (κ * ∑ p ∈ siftingPrimes v₀ T, (1 : ℝ) / p) with hE_def
  set L := log T / log v₀ with hL_def
  have hL : 0 < L := div_pos (by linarith) hlogv₀
  have hE : 0 < E := exp_pos _
  have hLE : L ^ κ ≤ exp (2 * κ * Cm) * E := by
    have hlogL : log (log T) - log (log v₀) = log L :=
      (log_div (by linarith) hlogv₀.ne').symm
    calc L ^ κ = exp (κ * log L) := by rw [exp_nat_mul, exp_log hL]
      _ ≤ exp (κ * (∑ p ∈ siftingPrimes v₀ T, (1 : ℝ) / p + 2 * Cm)) := by
          gcongr
          linarith
      _ = exp (2 * κ * Cm) * E := by
          rw [hE_def, ← exp_add]
          congr 1
          ring
  have hR : 24 * κ * (log v₀ / log Z) = 1 / L := by
    rw [hL_def, hlogT]
    field_simp
  have hy6 : y ^ 6 = Z ^ 3 := by
    rw [show y ^ 6 = (y ^ 2) ^ 3 by ring, hy_def, sq_sqrt hZ₀.le]
  have hmain : 2 * V / E ≤ 2 * exp (2 * κ * Cm) * (24 * κ) ^ κ * V * (log v₀ / log Z) ^ κ := by
    rw [div_le_iff₀ hE]
    have hV : (0 : ℝ) ≤ V := Nat.cast_nonneg V
    calc 2 * (V : ℝ) = 2 * V * 1 := by ring
      _ ≤ 2 * V * (exp (2 * κ * Cm) * E * (1 / L) ^ κ) := by
          gcongr
          rw [one_div_pow, mul_one_div, le_div_iff₀ (by positivity), one_mul]
          exact hLE
      _ = 2 * exp (2 * κ * Cm) * (24 * κ) ^ κ * V * (log v₀ / log Z) ^ κ * E := by
          rw [← hR, mul_pow]
          ring
  have hC : 1 ≤ 2 * exp (2 * κ * Cm) * (24 * κ) ^ κ := by
    have h1 : 1 ≤ (24 * (κ : ℝ)) ^ κ := one_le_pow₀ (by linarith)
    have h2 : 1 ≤ exp (2 * κ * Cm) := one_le_exp (by positivity)
    nlinarith
  calc (((Finset.Ico v₁ (v₁ + V)).filter fun v ↦ ∀ j, ∀ p : ℕ, p.Prime → v₀ < p →
        (p : ℝ) ≤ Z → ¬(p : ℤ) ∣ α j * v + β j).card : ℝ)
      ≤ #{v ∈ Ico v₁ (v₁ + V) | ∀ j, ∀ p ∈ siftingPrimes v₀ T, ¬(p : ℤ) ∣ α j * v + β j} := by
        exact_mod_cast card_le_card hsub
    _ ≤ 2 * V / E + y ^ 6 := hcore
    _ ≤ 2 * exp (2 * κ * Cm) * (24 * κ) ^ κ * V * (log v₀ / log Z) ^ κ +
          2 * exp (2 * κ * Cm) * (24 * κ) ^ κ * Z ^ 3 := by
        rw [hy6]
        refine add_le_add hmain ?_
        exact le_mul_of_one_le_left (by positivity) hC

end Erdos420
