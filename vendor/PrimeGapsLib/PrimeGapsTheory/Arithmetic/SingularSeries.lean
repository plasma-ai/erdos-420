/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Summable
public import PrimeGapsTheory.Analysis.SingularSeries
public import PrimeGapsTheory.Foundations.MaynardSieveDatum

import PrimeGapsTheory.Tactic.PaperTag

/-!
# The singular series

Euler-product representations and bounds for the singular series `𝔖(γ)`, both for the
second-moment weight `γ` of Definition 3 and for the Maynard sieve weight `γ_g`.  In either
case the Euler product splits as a finite head over the primes dividing the sieve modulus
`W`, whose value is `φ(W)/W`, times a tail over the primes exceeding `D₀`, which is
`1 + O(1/D₀)`.

## Main definitions

* `PrimeGaps.S2mSingularSeries.gammaPrime`: The prime values of the weight `γ` of Definition 3.
* `PrimeGaps.S2mSingularSeries.localFactor`: A local Euler factor of the singular series.
* `PrimeGaps.S2mSingularSeries.headFactor`, `PrimeGaps.S2mSingularSeries.tailFactor`: The head
  and tail parts of the local factor.
* `PrimeGaps.tailProduct`: The Euler tail product `∏_{p ∤ Q} (p-1)²/(p(p-2))`.

## Main results

* `PrimeGaps.S2mSingularSeries.lem_S2m_singular_series`: The singular-series identity for the
  second sieve moment, `𝔖(γ) = (φ(W)/W)(1 + O(1/D₀))`.
* `PrimeGaps.singularSeries_γ_g_eq_totient_mul_tail`: The exact factorization
  `𝔖(γ_g) = (φ(W)/W) · tailProduct`.
* `PrimeGaps.singularSeries_maynardSieveDatum_γ_asymptotic`: The corresponding asymptotic for
  the `γ` field of the Maynard sieve datum.
-/

@[expose] public section

open Real

open scoped Topology

namespace PrimeGaps

namespace S2mSingularSeries

/-- The weight $\gamma$ of Definition 3, given by its values on a prime $p$.
For $p \nmid W$ it is $\frac{p(p-1)^2}{p^3 - p^2 - 2p + 1}$, and for $p \mid W$ it
is $0$.  Only the values at primes enter the singular series, so this prime-value
function is all that the singular-series functional needs. -/
noncomputable def gammaPrime (W : ℕ) (p : ℕ) : ℝ :=
  if p ∣ W then 0
  else (p : ℝ) * ((p : ℝ) - 1) ^ 2 / ((p : ℝ) ^ 3 - (p : ℝ) ^ 2 - 2 * (p : ℝ) + 1)

/-- The promoted singular series can be written as a product indexed by the subtype of primes. -/
theorem singularSeries_eq_tprod_primes (g : ℕ → ℝ) : PrimeGaps.singularSeries g =
      ∏' p : Nat.Primes, (1 - g (p : ℕ) / (p : ℕ))⁻¹ * (1 - 1 / (p : ℕ)) := by
  unfold PrimeGaps.singularSeries
  rw [← tprod_subtype_eq_of_mulSupport_subset (s := {p : ℕ | p.Prime})
      (f := fun p ↦ if Nat.Prime p then (1 - 1 / (p : ℝ)) / (1 - g p / (p : ℝ)) else 1) ?_]
  · exact tprod_congr fun p ↦ by
      rw [if_pos (show Nat.Prime (p : ℕ) from p.2), div_eq_mul_inv, mul_comm]
  · intro p hp
    by_contra hprime
    simp only [Set.mem_ofPred_eq] at hprime
    simp [hprime, Function.mem_mulSupport] at hp

/-- The local Euler factor of $\mathfrak{S}(\gamma)$ at a prime $p$:
$(1 - \gamma(p)/p)^{-1}(1 - 1/p)$. -/
noncomputable def localFactor (W : ℕ) (p : ℕ) : ℝ :=
  (1 - gammaPrime W p / (p : ℝ))⁻¹ * (1 - 1 / (p : ℝ))

/-- The "head" factors: the local factor $1 - 1/p$ at primes $p \mid W$, and $1$
at primes $p \nmid W$.  Its full Euler product is $\phi(W)/W$. -/
noncomputable def headFactor (W : ℕ) (p : ℕ) : ℝ := if p ∣ W then (1 - 1 / (p : ℝ)) else 1

/-- The "tail" factors: the local factor at primes $p \nmid W$, and $1$ at primes
$p \mid W$.  Its full Euler product is the tail product $\prod_{p>D₀}(\cdots)$
that carries the $1 + O(1/D₀)$ asymptotic. -/
noncomputable def tailFactor (W : ℕ) (p : ℕ) : ℝ := if p ∣ W then 1 else localFactor W p

/-- **(Pointwise factorization.)** For every prime `p`, the local Euler factor
splits as the product of its head and tail parts:
`localFactor W p = headFactor W p * tailFactor W p`. -/
theorem localFactor_eq_head_mul_tail (W : ℕ) (p : ℕ) :
    localFactor W p = headFactor W p * tailFactor W p := by
  unfold headFactor tailFactor
  split_ifs with h <;> simp [localFactor, gammaPrime, h]

/-- **(Head product is multipliable.)** For nonzero `W`, the head factors are `1` for all but the
finitely many primes dividing `W`, so the family is multipliable. -/
theorem multipliable_headFactor (W : ℕ) (hWne : W ≠ 0) :
    Multipliable (fun p : Nat.Primes ↦ headFactor W (p : ℕ)) := by
  apply multipliable_of_hasFiniteMulSupport
  apply Set.Finite.subset
    (Set.finite_coe_iff.mp (Finset.finite_toSet (W.primeFactors.subtype Nat.Prime)))
  intro p hp
  have hpdvd : (p : ℕ) ∣ W := by
    have hp' : headFactor W (p : ℕ) ≠ 1 := hp
    by_contra hdvd
    exact hp' (if_neg hdvd)
  rw [Finset.mem_coe, Finset.mem_subtype, Nat.mem_primeFactors]
  exact ⟨p.2, hpdvd, hWne⟩

/-- For a prime `p ∤ W`, `(1 - γ p / p)⁻¹ * (1 - 1/p) = (p⁴ - 2p³ - p² + 3p - 1) / (p³ (p - 2))`. -/
theorem gammaPrime_localFactor_eq (W : ℕ) {p : ℕ} (hp : p.Prime) (hpW : ¬ (p ∣ W)) :
    (1 - gammaPrime W p / (p : ℝ))⁻¹ * (1 - 1 / (p : ℝ)) =
      ((p : ℝ) ^ 4 - 2 * (p : ℝ) ^ 3 - (p : ℝ) ^ 2 + 3 * (p : ℝ) - 1) /
          ((p : ℝ) ^ 3 * ((p : ℝ) - 2)) := by
  have hp2 : 2 ≤ p := hp.two_le
  unfold gammaPrime
  rw [if_neg hpW]
  rcases eq_or_lt_of_le hp2 with hpe | hpg
  · subst hpe
    norm_num
  · have hp3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpg
    have hppos : (0 : ℝ) < (p : ℝ) := by linarith
    have hpne : (p : ℝ) ≠ 0 := by linarith
    have hp2ne : (p : ℝ) - 2 ≠ 0 := by linarith
    have hd : (p : ℝ) ^ 3 - (p : ℝ) ^ 2 - 2 * (p : ℝ) + 1 ≠ 0 := by
      nlinarith [sq_nonneg ((p : ℝ) - 1)]
    have hfac : (1 : ℝ) - (p : ℝ) * ((p : ℝ) - 1) ^ 2 /
        ((p : ℝ) ^ 3 - (p : ℝ) ^ 2 - 2 * (p : ℝ) + 1) / (p : ℝ) = ((p : ℝ) ^ 2 * ((p : ℝ) - 2)) /
          ((p : ℝ) ^ 3 - (p : ℝ) ^ 2 - 2 * (p : ℝ) + 1) := by
      have hdp : ((p : ℝ) ^ 3 - (p : ℝ) ^ 2 - 2 * (p : ℝ) + 1) * (p : ℝ) ≠ 0 :=
        mul_ne_zero hd hpne
      rw [div_div, sub_eq_iff_eq_add, div_add_div _ _ hd hdp, eq_div_iff (mul_ne_zero hd hdp)]
      ring
    rw [hfac, inv_div, show (1 : ℝ) - 1 / (p : ℝ) = ((p : ℝ) - 1) / (p : ℝ) by field_simp,
      div_mul_div_comm, div_eq_div_iff (by positivity) (by positivity)]
    ring

/-- For `x ≥ 3` the local Euler factor value `(x⁴ - 2x³ - x² + 3x - 1) / (x³ (x - 2))` lies
within `2/x²` of `1`. -/
private theorem abs_localFactorValue_sub_one_le {x : ℝ} (hx : 3 ≤ x) :
    |(x ^ 4 - 2 * x ^ 3 - x ^ 2 + 3 * x - 1) / (x ^ 3 * (x - 2)) - 1| ≤ 2 / x ^ 2 := by
  have hden : (0 : ℝ) < x ^ 3 * (x - 2) := by
    have : (0 : ℝ) < x - 2 := by linarith
    positivity
  have hx2 : (0 : ℝ) < x ^ 2 := by positivity
  have hdiff : (x ^ 4 - 2 * x ^ 3 - x ^ 2 + 3 * x - 1) / (x ^ 3 * (x - 2)) - 1 =
      -(x ^ 2 - 3 * x + 1) / (x ^ 3 * (x - 2)) := by
    rw [div_sub_one (ne_of_gt hden)]; ring_nf
  rw [hdiff, abs_div, abs_of_pos hden, div_le_div_iff₀ hden hx2, abs_neg,
    abs_of_nonneg (by nlinarith)]
  nlinarith [sq_nonneg x]

/-- The series `∑ c / n²` over the naturals converges. -/
private theorem summable_const_div_natCast_sq (c : ℝ) : Summable fun n : ℕ ↦ c / (n : ℝ) ^ 2 :=
  (((Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num)).mul_left c).congr fun n ↦
    mul_one_div c _

/-- **(Tail product is multipliable.)** The tail factors satisfy
`tailFactor W p = 1 - 1/p² + O(1/p³)` for `p ∤ W` and `= 1` for `p ∣ W`, so
`log (tailFactor W p) = O(1/p²)` is absolutely summable over primes, giving
multipliability. -/
theorem multipliable_tailFactor (W : ℕ) :
    Multipliable (fun p : Nat.Primes ↦ tailFactor W (p : ℕ)) := by
  set a : Nat.Primes → ℝ := fun p ↦ tailFactor W (p : ℕ) - 1 with hadef
  have hper : ∀ p : Nat.Primes, |a p| ≤ 4 / ((p : ℕ) : ℝ) ^ 2 := by
    intro p
    have hp : (p : ℕ).Prime := p.2
    have hp2 : 2 ≤ (p : ℕ) := hp.two_le
    have hpR2 : (2 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast hp2
    simp only [hadef]
    unfold tailFactor
    by_cases hdvd : (p : ℕ) ∣ W
    · rw [if_pos hdvd]
      simp only [sub_self, abs_zero]
      positivity
    · rw [if_neg hdvd]
      unfold localFactor
      rcases eq_or_lt_of_le hpR2 with hpe | hpg
      · have hp2eq : ((p : ℕ) : ℝ) = 2 := hpe.symm
        unfold gammaPrime
        rw [if_neg hdvd, hp2eq]
        norm_num
      · have hp3 : (3 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast hpg
        rw [gammaPrime_localFactor_eq W hp hdvd]
        refine (abs_localFactorValue_sub_one_le hp3).trans ?_
        gcongr
        norm_num
  have hasum : Summable (fun p : Nat.Primes ↦ |a p|) :=
    Summable.of_nonneg_of_le (fun p ↦ abs_nonneg _) hper
      ((summable_const_div_natCast_sq 4).comp_injective Nat.Primes.coe_nat_injective)
  have hmul : Multipliable (fun p : Nat.Primes ↦ 1 + a p) :=
    Real.multipliable_one_add_of_summable hasum.of_abs
  have heq : (fun p : Nat.Primes ↦ 1 + a p) = (fun p : Nat.Primes ↦ tailFactor W (p : ℕ)) := by
    funext p; simp only [hadef]; ring
  rwa [heq] at hmul

/-- **(Euler product factors as head × tail.)** Using the pointwise factorization
and multipliability of both factor families, the singular series splits:
`S(γ) = (∏' headFactor) * (∏' tailFactor)`. -/
theorem singularSeries_eq_head_mul_tail (W : ℕ) (hW : W ≠ 0) :
    PrimeGaps.singularSeries (gammaPrime W) = (∏' p : Nat.Primes, headFactor W (p : ℕ)) *
        (∏' p : Nat.Primes, tailFactor W (p : ℕ)) := by
  rw [singularSeries_eq_tprod_primes]
  have hpt : ∀ p : Nat.Primes,
      (1 - gammaPrime W (p : ℕ) / ((p : ℕ) : ℝ))⁻¹ * (1 - 1 / ((p : ℕ) : ℝ)) =
        headFactor W (p : ℕ) * tailFactor W (p : ℕ) := fun p ↦ by
    rw [← localFactor_eq_head_mul_tail]
    rfl
  simp_rw [hpt]
  exact Multipliable.tprod_mul (multipliable_headFactor W hW) (multipliable_tailFactor W)

/-- **(Head Euler product equals `φ(W)/W`.)** The infinite product of the head
factors over all primes equals `φ(W)/W`. -/
theorem headFactor_tprod_eq (W : ℕ) (hWne : W ≠ 0) : (∏' p : Nat.Primes, headFactor W (p : ℕ)) =
      (Nat.totient W : ℝ) / (W : ℝ) := by
  let s : Finset Nat.Primes := W.primeFactors.subtype Nat.Prime
  have hstep1 : (∏' p : Nat.Primes, headFactor W (p : ℕ)) = ∏ b ∈ s, headFactor W (b : ℕ) := by
    refine tprod_eq_prod fun b hb ↦ ?_
    have hbdvd : ¬ ((b : ℕ) ∣ W) := fun hdvd ↦
      (Finset.mem_subtype (s := W.primeFactors) (a := b)).not.mp hb
        (Nat.mem_primeFactors.mpr ⟨b.2, hdvd, hWne⟩)
    unfold headFactor
    rw [if_neg hbdvd]
  have hstep2 : ∏ b ∈ s, headFactor W (b : ℕ) = ∏ q ∈ W.primeFactors, headFactor W q := by
    change ∏ b ∈ W.primeFactors.subtype Nat.Prime, headFactor W (b : ℕ) =
      ∏ q ∈ W.primeFactors, headFactor W q
    rw [Finset.prod_subtype_eq_prod_filter]
    refine Finset.prod_congr ?_ (fun _ _ ↦ rfl)
    ext x
    simp only [Finset.mem_filter]
    exact ⟨fun h ↦ h.1, fun hx ↦ ⟨hx, Nat.prime_of_mem_primeFactors hx⟩⟩
  have hstep3 : ∏ q ∈ W.primeFactors, headFactor W q = ∏ q ∈ W.primeFactors, (1 - (q : ℝ)⁻¹) :=
    Finset.prod_congr rfl fun q hq ↦ by
      unfold headFactor
      rw [if_pos (Nat.mem_primeFactors.mp hq).2.1, one_div]
  have htot : (W.totient : ℝ) = W * ∏ q ∈ W.primeFactors, (1 - (q : ℝ)⁻¹) := by
    have := congrArg (fun x : ℚ ↦ (x : ℝ)) (Nat.totient_eq_mul_prod_factors W)
    push_cast at this
    convert this using 2
  have hWRne : (W : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hWne
  rw [hstep1, hstep2, hstep3, htot]
  field_simp

/-- Positivity of the head Euler-product value `φ W / W` for `W ≠ 0`. -/
theorem headFactor_tprod_pos (W : ℕ) (hW : W ≠ 0) : (0 : ℝ) < (Nat.totient W : ℝ) / (W : ℝ) := by
  have hWpos : 0 < W := Nat.pos_of_ne_zero hW
  exact div_pos (Nat.cast_pos.mpr (Nat.totient_pos.mpr hWpos)) (Nat.cast_pos.mpr hWpos)

open scoped PrimeGaps.sieveModulus

/-- For a prime `p`, `p ∣ W N` iff `p ≤ ⌊D₀ N⌋₊`. -/
theorem dvd_W_iff (N : ℕ) {p : ℕ} (hp : p.Prime) :
    p ∣ W N ↔ p ≤ ⌊Real.log (Real.log (Real.log N))⌋₊ := by
  change p ∣ primorial ⌊D₀ N⌋₊ ↔ _
  simpa [D₀] using Nat.Prime.dvd_primorial_iff hp

/-- **(THE ANALYTIC CRUX: tail product is `1 + O(1/D₀)`.)** There are absolute
constants `C > 0` and `D_* ≥ 2` such that whenever `D₀ N ≥ D_*`, the tail Euler
product lies within `C/D₀` of `1`. -/
theorem tailFactor_tprod_bound : ∃ C : ℝ, ∃ D_star : ℝ, 0 < C ∧ 2 ≤ D_star ∧
      ∀ N : ℕ, D_star ≤ D₀ N →
        |(∏' p : Nat.Primes, tailFactor (W N) (p : ℕ)) - 1| ≤ C / D₀ N := by
  refine ⟨8, 4, by norm_num, by norm_num, ?_⟩
  intro N hN
  set M := ⌊Real.log (Real.log (Real.log N))⌋₊ with hMdef
  have hD0eq : D₀ N = Real.log (Real.log (Real.log N)) := rfl
  have hD4 : (4 : ℝ) ≤ D₀ N := hN
  have hD0pos : (0 : ℝ) < D₀ N := by linarith
  have hM4 : 4 ≤ M := by
    rw [hMdef, ← hD0eq]
    exact Nat.le_floor (by exact_mod_cast hD4)
  have hMlt : D₀ N < (M : ℝ) + 1 := by
    rw [hMdef, ← hD0eq]; exact Nat.lt_floor_add_one _
  set a : Nat.Primes → ℝ := fun p ↦ tailFactor (W N) (p : ℕ) - 1 with hadef
  set g : ℕ → ℝ := fun n ↦ if M < n then 2 / (n : ℝ) ^ 2 else 0 with hgdef
  have hper : ∀ p : Nat.Primes, |a p| ≤ g (p : ℕ) := by
    intro p
    have hp : (p : ℕ).Prime := p.2
    simp only [hadef, hgdef]
    unfold tailFactor
    by_cases hdvd : (p : ℕ) ∣ W N
    · have hle : (p : ℕ) ≤ M := (dvd_W_iff N hp).mp hdvd
      rw [if_pos hdvd, if_neg (by omega)]
      simp
    · have hgt : M < (p : ℕ) := by
        by_contra h
        exact hdvd ((dvd_W_iff N hp).mpr (by omega))
      rw [if_neg hdvd, if_pos hgt]
      unfold localFactor
      rw [gammaPrime_localFactor_eq (W N) hp hdvd]
      exact abs_localFactorValue_sub_one_le (by exact_mod_cast show 3 ≤ (p : ℕ) by omega)
  have hgnn : ∀ n, 0 ≤ g n := fun n ↦ by simp only [hgdef]; split_ifs <;> positivity
  have hgsum : Summable g :=
    Summable.of_nonneg_of_le hgnn
      (fun n ↦ by simp only [hgdef]; split_ifs; exacts [le_rfl, by positivity])
      (summable_const_div_natCast_sq 2)
  have hasum : Summable (fun p : Nat.Primes ↦ |a p|) :=
    Summable.of_nonneg_of_le (fun p ↦ abs_nonneg _) hper
      (hgsum.comp_injective Nat.Primes.coe_nat_injective)
  have htail : ∑' n : ℕ, g n ≤ 4 / ((M : ℝ) + 1) := by
    refine Real.tsum_le_of_sum_range_le hgnn fun n ↦ ?_
    have hset : {i ∈ Finset.range n | M < i} = Finset.Ioo M n := by
      ext i; simp [Finset.mem_Ioo, Finset.mem_filter, Finset.mem_range]; omega
    have hcongr : ∀ i ∈ Finset.Ioo M n, (2 : ℝ) / (i : ℝ) ^ 2 = 2 * ((i : ℝ) ^ 2)⁻¹ := fun i _ ↦
      div_eq_mul_inv 2 _
    simp only [hgdef]
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, hset, Finset.sum_congr rfl hcongr,
      ← Finset.mul_sum]
    calc (2 : ℝ) * ∑ i ∈ Finset.Ioo M n, ((i : ℝ) ^ 2)⁻¹ ≤ 2 * (2 / ((M : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_left (sum_Ioo_inv_sq_le M n) (by norm_num)
      _ = 4 / ((M : ℝ) + 1) := by ring
  have hSbound : ∑' p : Nat.Primes, |a p| ≤ 4 / D₀ N :=
    calc ∑' p : Nat.Primes, |a p| ≤ ∑' n : ℕ, g n :=
          Summable.tsum_le_tsum_of_inj (e := fun p : Nat.Primes ↦ (p : ℕ))
            Nat.Primes.coe_nat_injective (fun c _ ↦ hgnn c) hper hasum hgsum
      _ ≤ 4 / ((M : ℝ) + 1) := htail
      _ ≤ 4 / D₀ N := div_le_div_of_nonneg_left (by norm_num) hD0pos (le_of_lt hMlt)
  have hmul : Multipliable (fun p : Nat.Primes ↦ 1 + a p) := by
    have : (fun p : Nat.Primes ↦ 1 + a p) = (fun p : Nat.Primes ↦ tailFactor (W N) (p : ℕ)) := by
      funext p; simp only [hadef]; ring
    rw [this]; exact multipliable_tailFactor (W N)
  have hprodbound : |(∏' p : Nat.Primes, (1 + a p)) - 1| ≤ rexp (4 / D₀ N) - 1 := by
    have hp := hmul.hasProd
    rw [HasProd, SummationFilter.unconditional_filter] at hp
    have htend : Filter.Tendsto (fun s : Finset Nat.Primes ↦ ∏ i ∈ s, (1 + a i)) Filter.atTop
        (𝓝 (∏' i, (1 + a i))) := hp
    have hcont : Filter.Tendsto (fun s : Finset Nat.Primes ↦ |(∏ i ∈ s, (1 + a i)) - 1|)
        Filter.atTop (𝓝 (|(∏' i, (1 + a i)) - 1|)) := (htend.sub_const 1).abs
    refine le_of_tendsto hcont ?_
    filter_upwards with s
    calc |(∏ i ∈ s, (1 + a i)) - 1| ≤ rexp (∑ i ∈ s, |a i|) - 1 := by
            simpa [Real.norm_eq_abs] using Finset.norm_prod_one_add_sub_one_le s a
      _ ≤ rexp (4 / D₀ N) - 1 := by
            gcongr
            exact (hasum.sum_le_tsum s fun i _ ↦ abs_nonneg _).trans hSbound
  have hprodeq : (∏' p : Nat.Primes, (1 + a p)) = ∏' p : Nat.Primes, tailFactor (W N) (p : ℕ) := by
    congr 1; funext p; simp only [hadef]; ring
  rw [hprodeq] at hprodbound
  refine hprodbound.trans ?_
  have hSnn : (0 : ℝ) ≤ 4 / D₀ N := by positivity
  have hkey := Real.abs_exp_sub_one_le
    (show |4 / D₀ N| ≤ 1 by rw [abs_of_nonneg hSnn, div_le_one hD0pos]; linarith)
  rw [abs_of_nonneg (by linarith [Real.one_le_exp hSnn]), abs_of_nonneg hSnn] at hkey
  calc rexp (4 / D₀ N) - 1 ≤ 2 * (4 / D₀ N) := hkey
    _ = 8 / D₀ N := by ring

/-- **Maynard `lem_S2m_singular_series`.** With $W$, $D₀$ and $\gamma$ as in
Definitions 1–3, the singular series satisfies $\mathfrak{S}(\gamma) =
\frac{\phi(W)}{W}(1 + O(1/D₀))$ with an absolute implied constant.  Quantified
form: there are absolute constants $C > 0$ and $D_* \ge 2$ so that whenever
$D₀ = \log\log\log N \ge D_*$ one has
$\left|\mathfrak{S}(\gamma)/(\phi(W)/W) - 1\right| \le C/D₀$. -/
@[pg_tag "bg246" "lem_S2m_singular_series"]
theorem lem_S2m_singular_series : ∃ C : ℝ, ∃ D_star : ℝ, 0 < C ∧ 2 ≤ D_star ∧
      ∀ N : ℕ, D_star ≤ D₀ N →
        |PrimeGaps.singularSeries (gammaPrime (W N)) / ((Nat.totient (W N) : ℝ) / (W N : ℝ)) - 1| ≤
              C / D₀ N := by
  obtain ⟨C, D_star, hC, hDstar, hbound⟩ := tailFactor_tprod_bound
  refine ⟨C, D_star, hC, hDstar, ?_⟩
  intro N hN
  have hphi_pos : (0 : ℝ) < (Nat.totient (W N) : ℝ) / (W N : ℝ) :=
    headFactor_tprod_pos (W N) PrimeGaps.W_ne_zero
  rw [singularSeries_eq_head_mul_tail (W N) PrimeGaps.W_ne_zero,
    headFactor_tprod_eq (W N) PrimeGaps.W_ne_zero, mul_comm, mul_div_assoc,
    div_self (ne_of_gt hphi_pos), mul_one]
  exact hbound N hN

end S2mSingularSeries

/-- The tail product `∏_{p ∤ Q} (p-1)²/(p(p-2))` over primes `p` not dividing `Q`. -/
noncomputable def tailProduct (Q : ℕ) : ℝ :=
  ∏' p : {p : Nat.Primes // ¬ (p : ℕ) ∣ Q},
    (((p : ℕ) : ℝ) - 1) ^ 2 / (((p : ℕ) : ℝ) * (((p : ℕ) : ℝ) - 2))

/-- Characterization of the tail-product factor: each factor exceeds `1` by
`1/(p(p-2))`, i.e. `(p-1)²/(p(p-2)) = 1 + 1/(p(p-2))` for `p > 2`. -/
theorem tail_factor_eq (p : ℝ) (hp : 2 < p) :
    (p - 1) ^ 2 / (p * (p - 2)) = 1 + 1 / (p * (p - 2)) := by
  have hp0 : p ≠ 0 := by linarith
  have hp2 : p - 2 ≠ 0 := by linarith
  field_simp
  ring

/-- The exact evaluation of the local factor of `𝔖(γ_g)` at a prime `p ∣ W`:
the factor equals `(p-1)/p`. -/
theorem local_factor_dvd (W : ℕ) (p : ℕ) (hp : p.Prime) (hpW : p ∣ W) :
    (1 - maynardGammaPrime W p / (p : ℝ))⁻¹ * (1 - 1 / (p : ℝ)) =
      ((p : ℝ) - 1) / (p : ℝ) := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.pos.ne'
  rw [show maynardGammaPrime W p = 0 by simp [maynardGammaPrime, hpW]]
  field_simp
  ring

/-- The exact evaluation of the local factor of `𝔖(γ_g)` at a prime `p ∤ W`
(with `p > 2`): the factor equals `(p-1)²/(p(p-2))`. -/
theorem local_factor_not_dvd (W : ℕ) (p : ℕ) (hp2 : 2 < p) (hpW : ¬ p ∣ W) :
    (1 - maynardGammaPrime W p / (p : ℝ))⁻¹ * (1 - 1 / (p : ℝ)) =
      (((p : ℝ) - 1) ^ 2) / ((p : ℝ) * ((p : ℝ) - 2)) := by
  have hpr : (2 : ℝ) < (p : ℝ) := by exact_mod_cast hp2
  have hp0 : (p : ℝ) ≠ 0 := by linarith
  have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
  have hp2' : (p : ℝ) - 2 ≠ 0 := by linarith
  rw [show maynardGammaPrime W p = (p : ℝ) / ((p : ℝ) - 1) by simp [maynardGammaPrime, hpW],
    show (1 : ℝ) - (p : ℝ) / ((p : ℝ) - 1) / (p : ℝ) = ((p : ℝ) - 2) / ((p : ℝ) - 1) by
      field_simp; ring,
    show (1 : ℝ) - 1 / (p : ℝ) = ((p : ℝ) - 1) / (p : ℝ) by field_simp, inv_div]
  field_simp

/-- The per-prime factor appearing in
`PrimeGaps.singularSeries (maynardGammaPrime Q)`. -/
noncomputable def gFactor (Q : ℕ) (p : Nat.Primes) : ℝ :=
  (1 - maynardGammaPrime Q (p : ℕ) / ((p : ℕ) : ℝ))⁻¹ * (1 - 1 / ((p : ℕ) : ℝ))

/-- `PrimeGaps.singularSeries (maynardGammaPrime Q) = ∏' p : Nat.Primes, gFactor Q p`. -/
theorem singularSeries_eq_tprod_gFactor (Q : ℕ) :
    PrimeGaps.singularSeries (maynardGammaPrime Q) = ∏' p : Nat.Primes, gFactor Q p := by
  rw [PrimeGaps.S2mSingularSeries.singularSeries_eq_tprod_primes]
  rfl

/-- If every prime `≤ D₀ N` divides `Q` and a prime does not divide `Q`, then `D₀ N < p`. -/
theorem lt_of_not_dvd (N Q : ℕ) (hQD : primorial ⌊D₀ N⌋₊ ∣ Q) (p : ℕ) (hp : p.Prime)
    (h : ¬ p ∣ Q) : D₀ N < (p : ℝ) := by
  by_contra! hc
  exact h (((Nat.Prime.dvd_W_iff_le_D₀ hp).2 hc).trans hQD)

/-- If `2 ∣ Q` and a prime does not divide `Q`, then `2 < p`. -/
theorem two_lt_of_not_dvd (Q : ℕ) (h2 : 2 ∣ Q) (p : ℕ) (hp : p.Prime) (h : ¬ p ∣ Q) :
    (2 : ℝ) < (p : ℝ) := by
  have hp2 : p ≠ 2 := fun hp2 ↦ h (hp2 ▸ h2)
  exact_mod_cast lt_of_le_of_ne hp.two_le (Ne.symm hp2)

/-- The value of the factor according as `p ∣ W` or `p ∤ W`. -/
theorem gFactor_eq (Q : ℕ) (h2 : 2 ∣ Q) (p : Nat.Primes) : gFactor Q p = if ((p : ℕ) ∣ Q)
      then (((p : ℕ) : ℝ) - 1) / ((p : ℕ) : ℝ)
      else (((p : ℕ) : ℝ) - 1) ^ 2 / (((p : ℕ) : ℝ) * (((p : ℕ) : ℝ) - 2)) := by
  by_cases hdvd : (p : ℕ) ∣ Q
  · rw [if_pos hdvd]
    exact local_factor_dvd (Q) (p : ℕ) p.2 hdvd
  · rw [if_neg hdvd]
    refine local_factor_not_dvd (Q) (p : ℕ) ?_ hdvd
    exact_mod_cast two_lt_of_not_dvd Q h2 (p : ℕ) p.2 hdvd

/-- The term `gFactor Q p - 1`. -/
noncomputable def gTerm (Q : ℕ) (p : Nat.Primes) : ℝ := gFactor Q p - 1

/-- `gFactor Q p = 1 + gTerm Q p`. -/
theorem gFactor_eq_one_add (Q : ℕ) (p : Nat.Primes) : gFactor Q p = 1 + gTerm Q p := by
  simp [gTerm]

/-- Summability of `1/p²` over primes, as `p^(-2)`. -/
theorem summable_prime_rpow_neg_two :
    Summable (fun p : Nat.Primes ↦ (3 : ℝ) * ((p : ℕ) : ℝ) ^ (-2 : ℝ)) :=
  Summable.mul_left 3 (Nat.Primes.summable_rpow.2 (by norm_num))

/-- The value of `gTerm` according as `p ∣ W` or `p ∤ W`. -/
theorem gTerm_eq (Q : ℕ) (h2 : 2 ∣ Q) (p : Nat.Primes) : gTerm Q p = if ((p : ℕ) ∣ Q)
      then - (1 / ((p : ℕ) : ℝ))
      else 1 / (((p : ℕ) : ℝ) * (((p : ℕ) : ℝ) - 2)) := by
  have hppos : (0 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast p.2.pos
  rw [gTerm, gFactor_eq Q h2 p]
  by_cases hdvd : (p : ℕ) ∣ Q
  · rw [if_pos hdvd, if_pos hdvd]
    field_simp
    ring
  · rw [if_neg hdvd, if_neg hdvd,
      tail_factor_eq _ (two_lt_of_not_dvd Q h2 (p : ℕ) p.2 hdvd)]
    ring

/-- The non-divisor part of `gTerm`. -/
noncomputable def gTermND (Q : ℕ) (p : Nat.Primes) : ℝ := if ((p : ℕ) ∣ Q) then 0 else gTerm Q p

/-- The divisor part of `gTerm`. -/
noncomputable def gTermD (Q : ℕ) (p : Nat.Primes) : ℝ := if ((p : ℕ) ∣ Q) then gTerm Q p else 0

/-- `gTerm Q p = gTermD Q p + gTermND Q p`. -/
theorem gTerm_eq_add (Q : ℕ) (p : Nat.Primes) : gTerm Q p = gTermD Q p + gTermND Q p := by
  unfold gTermD gTermND
  by_cases h : (p : ℕ) ∣ Q <;> simp [h]

/-- Bound on `|gTermND Q p|` by `3 p^(-2)`. -/
theorem abs_gTermND_le (Q : ℕ) (h2 : 2 ∣ Q) (p : Nat.Primes) :
    |gTermND Q p| ≤ (3 : ℝ) * ((p : ℕ) : ℝ) ^ (-2 : ℝ) := by
  have hppos : (0 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast p.2.pos
  rw [show ((p : ℕ) : ℝ) ^ (-2 : ℝ) = (((p : ℕ) : ℝ) ^ 2)⁻¹ by
    rw [Real.rpow_neg hppos.le, Real.rpow_two]]
  unfold gTermND
  by_cases hdvd : (p : ℕ) ∣ Q
  · rw [if_pos hdvd, abs_zero]
    positivity
  · rw [if_neg hdvd, gTerm_eq Q h2 p, if_neg hdvd]
    have hp2 : (2 : ℝ) < ((p : ℕ) : ℝ) := two_lt_of_not_dvd Q h2 (p : ℕ) p.2 hdvd
    have hp3 : (3 : ℝ) ≤ ((p : ℕ) : ℝ) := by
      have hp2nat : 2 < (p : ℕ) := by exact_mod_cast hp2
      exact_mod_cast hp2nat
    have hden_pos : (0 : ℝ) < ((p : ℕ) : ℝ) * (((p : ℕ) : ℝ) - 2) := mul_pos hppos (by linarith)
    rw [abs_of_nonneg (by positivity), div_le_iff₀ hden_pos,
      show (3 : ℝ) * (((p : ℕ) : ℝ) ^ 2)⁻¹ * (((p : ℕ) : ℝ) * (((p : ℕ) : ℝ) - 2)) =
        3 * (((p : ℕ) : ℝ) - 2) / ((p : ℕ) : ℝ) by field_simp, le_div_iff₀ hppos]
    nlinarith [hp3]

/-- `gTermND Q` is summable over primes. -/
theorem summable_gTermND (Q : ℕ) (h2 : 2 ∣ Q) : Summable (gTermND Q) :=
  Summable.of_norm <| Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _)
    (abs_gTermND_le Q h2) summable_prime_rpow_neg_two

/-- The set of primes dividing `Q` is finite. -/
theorem finite_prime_dvd (Q : ℕ) (hQ : Q ≠ 0) : {p : Nat.Primes | (p : ℕ) ∣ Q}.Finite := by
  have hfin : {n : ℕ | n ∣ Q}.Finite :=
    (Set.finite_Icc 0 Q).subset fun n hn ↦
      ⟨Nat.zero_le _, Nat.le_of_dvd hQ.bot_lt hn⟩
  exact Set.Finite.preimage (f := fun p : Nat.Primes ↦ (p : ℕ))
    (fun a _ b _ hab ↦ Subtype.ext hab) hfin

/-- `gTermD Q` is summable over primes (finite support). -/
theorem summable_gTermD (Q : ℕ) (hQ : Q ≠ 0) : Summable (gTermD Q) := by
  refine summable_of_ne_finset_zero (s := (finite_prime_dvd Q hQ).toFinset) fun p hp ↦ ?_
  rw [Set.Finite.mem_toFinset] at hp
  simp only [Set.mem_ofPred_eq] at hp
  unfold gTermD
  rw [if_neg hp]

/-- `gTerm Q` is summable over primes. -/
theorem summable_gTerm (Q : ℕ) (h2 : 2 ∣ Q) (hQ : Q ≠ 0) : Summable (gTerm Q) :=
  ((summable_gTermD Q hQ).add (summable_gTermND Q h2)).congr fun p ↦ (gTerm_eq_add Q p).symm

/-- The factors `gFactor Q` are multipliable. -/
theorem multipliable_gFactor (Q : ℕ) (h2 : 2 ∣ Q) (hQ : Q ≠ 0) : Multipliable (gFactor Q) :=
  (Real.multipliable_one_add_of_summable (summable_gTerm Q h2 hQ)).congr fun i ↦
    (gFactor_eq_one_add Q i).symm

/-- Each factor `gFactor Q p` is strictly positive. -/
theorem gFactor_pos (Q : ℕ) (h2 : 2 ∣ Q) (p : Nat.Primes) : 0 < gFactor Q p := by
  have hppos : (0 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast p.2.pos
  rw [gFactor_eq Q h2 p]
  by_cases hdvd : (p : ℕ) ∣ Q
  · have hp2 : (2 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast p.2.two_le
    rw [if_pos hdvd]
    exact div_pos (by linarith) hppos
  · have hp2 : (2 : ℝ) < ((p : ℕ) : ℝ) := two_lt_of_not_dvd Q h2 (p : ℕ) p.2 hdvd
    rw [if_neg hdvd]
    exact div_pos (by nlinarith) (mul_pos hppos (by linarith))

/-- The logarithms of the factors `gFactor Q` are summable. -/
theorem summable_log_gFactor (Q : ℕ) (h2 : 2 ∣ Q) (hQ : Q ≠ 0) :
    Summable (fun p : Nat.Primes ↦ Real.log (gFactor Q p)) :=
  (Real.summable_log_one_add_of_summable (summable_gTerm Q h2 hQ)).congr fun p ↦
    congrArg Real.log (gFactor_eq_one_add Q p).symm

/-- On the tail subtype `{p // p ∤ Q}`, the tail factor equals `gFactor Q p`. -/
theorem tail_factor_eq_gFactor (Q : ℕ) (h2 : 2 ∣ Q)
    (p : {p : Nat.Primes // ¬ (p : ℕ) ∣ Q}) :
    (((p : ℕ) : ℝ) - 1) ^ 2 / (((p : ℕ) : ℝ) * (((p : ℕ) : ℝ) - 2)) =
      gFactor Q (p : Nat.Primes) := by
  rw [gFactor_eq Q h2 (p : Nat.Primes), if_neg (p.2)]

/-- The tail factors are summable-in-log on the tail subtype. -/
theorem summable_log_tail (Q : ℕ) (h2 : 2 ∣ Q) (hQ : Q ≠ 0) :
    Summable (fun p : {p : Nat.Primes // ¬ (p : ℕ) ∣ Q} ↦
      Real.log (gFactor Q (p : Nat.Primes))) :=
  (summable_log_gFactor Q h2 hQ).subtype _

/-- `tailProduct Q = exp (∑' log (gFactor Q p))` over the tail subtype. -/
theorem tailProduct_eq_exp_tsum (Q : ℕ) (h2 : 2 ∣ Q) (hQ : Q ≠ 0) :
    tailProduct Q = rexp (∑' p : {p : Nat.Primes // ¬ (p : ℕ) ∣ Q},
          Real.log (gFactor Q (p : Nat.Primes))) := by
  rw [tailProduct, Real.rexp_tsum_eq_tprod (fun p ↦ gFactor_pos Q h2 _) (summable_log_tail Q h2 hQ)]
  exact tprod_congr fun p ↦ tail_factor_eq_gFactor Q h2 p

/-- The log-tail-sum is nonnegative (each log-factor is `≥ 0`). -/
theorem log_tail_tsum_nonneg (Q : ℕ) (h2 : 2 ∣ Q) :
    (0 : ℝ) ≤ ∑' p : {p : Nat.Primes // ¬ (p : ℕ) ∣ Q},
        Real.log (gFactor Q (p : Nat.Primes)) := by
  refine tsum_nonneg fun p ↦ Real.log_nonneg ?_
  rw [← tail_factor_eq_gFactor Q h2 p, tail_factor_eq _ (two_lt_of_not_dvd Q h2 _ (p : Nat.Primes).2 p.2)]
  have hp2 : (2 : ℝ) < ((p : Nat.Primes) : ℕ) := two_lt_of_not_dvd Q h2 _ (p : Nat.Primes).2 p.2
  have : (0 : ℝ) ≤ 1 / (((p : Nat.Primes) : ℕ) * (((p : Nat.Primes) : ℕ) - 2)) :=
    div_nonneg (by norm_num) (by nlinarith)
  linarith

/-- `1 ≤ tailProduct Q`. -/
theorem one_le_tailProduct (Q : ℕ) (h2 : 2 ∣ Q) (hQ : Q ≠ 0) : (1 : ℝ) ≤ tailProduct Q := by
  rw [tailProduct_eq_exp_tsum Q h2 hQ]
  simpa using Real.exp_le_exp.2 (log_tail_tsum_nonneg Q h2)

/-- The log-tail-sum is bounded by the tail sum of `gTermND`. -/
theorem log_tail_tsum_le_gTermND (Q : ℕ) (h2 : 2 ∣ Q) (hQ : Q ≠ 0) :
    (∑' p : {p : Nat.Primes // ¬ (p : ℕ) ∣ Q}, Real.log (gFactor Q (p : Nat.Primes))) ≤
      (∑' p : {p : Nat.Primes // ¬ (p : ℕ) ∣ Q},
        gTermND Q (p : Nat.Primes)) := by
  refine Summable.tsum_le_tsum ?_ (summable_log_tail Q h2 hQ) ((summable_gTermND Q h2).subtype _)
  intro p
  have hnd := p.2
  have hgnd : gTermND Q (p : Nat.Primes) = gTerm Q (p : Nat.Primes) := by
    unfold gTermND; rw [if_neg hnd]
  have hpos : (0 : ℝ) ≤ gTermND Q (p : Nat.Primes) := by
    rw [hgnd, gTerm_eq Q h2, if_neg hnd]
    have hp2 : (2 : ℝ) < ((p : Nat.Primes) : ℕ) := two_lt_of_not_dvd Q h2 _ (p : Nat.Primes).2 p.2
    exact div_nonneg (by norm_num) (by nlinarith)
  rw [show gFactor Q (p : Nat.Primes) = 1 + gTermND Q (p : Nat.Primes) by
    rw [hgnd, ← gFactor_eq_one_add]]
  simpa only [Function.comp_apply, add_sub_cancel_left] using
    Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + gTermND Q (p : Nat.Primes) by linarith)

/-- **Analytic kernel.**  The tail sum of `gTermND` (i.e. `∑_{p > D₀} 1/(p(p-2))`) is
bounded by `2 / D₀ N`, provided every prime `≤ D₀ N` divides `Q`. -/
theorem gTermND_tail_sum_le (N Q : ℕ) (hN : 4 ≤ D₀ N) (h2 : 2 ∣ Q)
    (hQD : primorial ⌊D₀ N⌋₊ ∣ Q) :
    (∑' p : {p : Nat.Primes // ¬ (p : ℕ) ∣ Q},
        gTermND Q (p : Nat.Primes)) ≤ 2 / D₀ N := by
  have hN2 : 2 < D₀ N := by linarith
  have hD0 : (0 : ℝ) < D₀ N := by linarith
  set m : ℕ := ⌊D₀ N⌋₊ + 1 with hmdef
  have hfloor_ge : 4 ≤ ⌊D₀ N⌋₊ := Nat.le_floor (by exact_mod_cast hN)
  have hmR : (5 : ℝ) ≤ (m : ℝ) := by exact_mod_cast show 5 ≤ m by omega
  set g : ℕ → ℝ := fun n ↦ if m ≤ n then 1 / (((n : ℝ) - 1) * ((n : ℝ) - 2)) else 0 with hgdef
  have hg_nonneg : ∀ n, 0 ≤ g n := by
    intro n
    simp only [hgdef]
    split_ifs with h
    · have hn5 : (5 : ℝ) ≤ (n : ℝ) := hmR.trans (by exact_mod_cast h)
      have h1 : (0 : ℝ) ≤ (n : ℝ) - 1 := by linarith
      have h2 : (0 : ℝ) ≤ (n : ℝ) - 2 := by linarith
      positivity
    · exact le_rfl
  set F : ℕ → ℝ := fun i ↦ -(1 / ((i : ℝ) - 2)) with hFdef
  have hgF : ∀ i, m ≤ i → g i = F (i + 1) - F i := by
    intro i hi
    have hi5 : (5 : ℝ) ≤ (i : ℝ) := hmR.trans (by exact_mod_cast hi)
    have h1 : ((i : ℝ) - 1) ≠ 0 := ne_of_gt (by linarith)
    have h2 : ((i : ℝ) - 2) ≠ 0 := ne_of_gt (by linarith)
    simp only [hgdef, hFdef, if_pos hi]
    push_cast
    rw [show ((i : ℝ) + 1) - 2 = (i : ℝ) - 1 by ring]
    field_simp
    ring
  have hpartial : ∀ n, m ≤ n →
      (∑ i ∈ Finset.range n, g i) = 1 / ((m : ℝ) - 2) - 1 / ((n : ℝ) - 2) := by
    intro n hn
    have hsplit : Finset.range n = Finset.range m ∪ Finset.Ico m n := by
      rw [Finset.range_eq_Ico, Finset.range_eq_Ico,
        Finset.Ico_union_Ico_eq_Ico (Nat.zero_le m) hn]
    have hzero : (∑ i ∈ Finset.range m, g i) = 0 :=
      Finset.sum_eq_zero fun i hi ↦ by
        rw [Finset.mem_range] at hi
        simp only [hgdef, if_neg (by omega : ¬ m ≤ i)]
    have hdisj : Disjoint (Finset.range m) (Finset.Ico m n) := by
      rw [Finset.range_eq_Ico]
      exact Finset.Ico_disjoint_Ico_consecutive 0 m n
    have hIco : (∑ i ∈ Finset.Ico m n, g i) = ∑ i ∈ Finset.Ico m n, (F (i + 1) - F i) :=
      Finset.sum_congr rfl fun i hi ↦ hgF i (Finset.mem_Ico.mp hi).1
    rw [hsplit, Finset.sum_union hdisj, hzero, zero_add, hIco, Finset.sum_Ico_sub F hn]
    simp only [hFdef]
    ring
  have hg_hasSum : HasSum g (1 / ((m : ℝ) - 2)) := by
    rw [hasSum_iff_tendsto_nat_of_nonneg hg_nonneg]
    refine Filter.Tendsto.congr' ?_
      (show Filter.Tendsto (fun n : ℕ ↦ 1 / ((m : ℝ) - 2) - 1 / ((n : ℝ) - 2)) Filter.atTop
        (𝓝 (1 / ((m : ℝ) - 2))) from ?_)
    · filter_upwards [Filter.eventually_ge_atTop m] with n hn
      exact (hpartial n hn).symm
    · have hinv : Filter.Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) - 2)) Filter.atTop (𝓝 0) := by
        have h1 : Filter.Tendsto (fun n : ℕ ↦ (n : ℝ) - 2) Filter.atTop Filter.atTop := by
          apply Filter.tendsto_atTop_add_const_right
          exact tendsto_natCast_atTop_atTop
        exact (tendsto_inv_atTop_zero.comp h1).congr fun n ↦ by simp [one_div]
      simpa using (tendsto_const_nhds (x := 1 / ((m : ℝ) - 2))).sub hinv
  set e : {p : Nat.Primes // ¬ (p : ℕ) ∣ Q} → ℕ :=
    fun p ↦ ((p : Nat.Primes) : ℕ) with hedef
  have he_inj : Function.Injective e := fun a b hab ↦ Subtype.ext (Subtype.ext hab)
  have hcompare : ∀ p : {p : Nat.Primes // ¬ (p : ℕ) ∣ Q},
      gTermND Q (p : Nat.Primes) ≤ g (e p) := by
    intro p
    have hnd := p.2
    have hme : m ≤ ((p : Nat.Primes) : ℕ) := by
      have : ⌊D₀ N⌋₊ < ((p : Nat.Primes) : ℕ) := by
        exact_mod_cast lt_of_le_of_lt (Nat.floor_le hD0.le)
          (lt_of_not_dvd N Q hQD _ (p : Nat.Primes).2 p.2)
      omega
    have hpR5 : (5 : ℝ) ≤ (((p : Nat.Primes) : ℕ) : ℝ) := hmR.trans (by exact_mod_cast hme)
    rw [show gTermND Q (p : Nat.Primes) =
        1 / ((((p : Nat.Primes) : ℕ) : ℝ) * ((((p : Nat.Primes) : ℕ) : ℝ) - 2)) by
      unfold gTermND
      rw [if_neg hnd, gTerm_eq Q h2, if_neg hnd],
      show g (e p) =
        1 / (((((p : Nat.Primes) : ℕ) : ℝ) - 1) * ((((p : Nat.Primes) : ℕ) : ℝ) - 2)) by
      simp only [hgdef, show e p = ((p : Nat.Primes) : ℕ) from rfl, if_pos hme]]
    set q : ℝ := (((p : Nat.Primes) : ℕ) : ℝ) with hq
    have hq2 : (0 : ℝ) < q - 2 := by linarith
    refine one_div_le_one_div_of_le (mul_pos (by linarith) hq2) ?_
    nlinarith [hq2]
  have hbound : (∑' p : {p : Nat.Primes // ¬ (p : ℕ) ∣ Q},
        gTermND Q (p : Nat.Primes)) ≤ 1 / ((m : ℝ) - 2) :=
    hg_hasSum.tsum_eq ▸ Summable.tsum_le_tsum_of_inj e he_inj (fun c _ ↦ hg_nonneg c) hcompare
      ((summable_gTermND Q h2).subtype _) hg_hasSum.summable
  refine hbound.trans ?_
  rw [div_le_div_iff₀ (by linarith) hD0,
    show (m : ℝ) = (⌊D₀ N⌋₊ : ℝ) + 1 by rw [hmdef]; push_cast; ring]
  nlinarith [Nat.floor_le hD0.le (a := D₀ N), Nat.lt_floor_add_one (D₀ N), hN]

/-- `log (tailProduct Q) ≤ 2 / D₀ N`. -/
theorem log_tailProduct_le (N Q : ℕ) (hN : 4 ≤ D₀ N) (h2 : 2 ∣ Q) (hQ : Q ≠ 0)
    (hQD : primorial ⌊D₀ N⌋₊ ∣ Q) : Real.log (tailProduct Q) ≤ 2 / D₀ N := by
  rw [tailProduct_eq_exp_tsum Q h2 hQ, Real.log_exp]
  exact le_trans (log_tail_tsum_le_gTermND Q h2 hQ) (gTermND_tail_sum_le N Q hN h2 hQD)

/-- `tailProduct Q - 1 ≤ 4 / D₀ N`. -/
theorem tailProduct_sub_one_le (N Q : ℕ) (hN : 4 ≤ D₀ N) (h2 : 2 ∣ Q) (hQ : Q ≠ 0)
    (hQD : primorial ⌊D₀ N⌋₊ ∣ Q) : tailProduct Q - 1 ≤ 4 * (1 / D₀ N) := by
  have hD0 : (0 : ℝ) < D₀ N := by linarith
  have h1 : (1 : ℝ) ≤ tailProduct Q := one_le_tailProduct Q h2 hQ
  have hlog0 : (0 : ℝ) ≤ Real.log (tailProduct Q) := Real.log_nonneg h1
  have hlog := log_tailProduct_le N Q hN h2 hQ hQD
  set t := Real.log (tailProduct Q) with ht
  have ht1 : t ≤ 1 := by
    have h2' : (2 : ℝ) / D₀ N ≤ 1 := by rw [div_le_one hD0]; linarith
    linarith
  rw [show tailProduct Q = rexp t from (Real.exp_log (by linarith)).symm]
  calc rexp t - 1 ≤ 2 * t := by
        have h := Real.abs_exp_sub_one_le (x := t) (by rw [abs_of_nonneg hlog0]; exact ht1)
        rw [abs_of_nonneg hlog0] at h
        linarith [le_abs_self (rexp t - 1), h]
    _ ≤ 2 * (2 / D₀ N) := by linarith
    _ = 4 * (1 / D₀ N) := by ring

/-- **Part 1 — the exact product formula.**  The singular product of `γ_g` factors as
`𝔖(γ_g) = (φ(W)/W) · ∏_{p > D₀} (p-1)²/(p(p-2))`. -/
theorem singularSeries_γ_g_eq_totient_mul_tail (Q : ℕ) (h2 : 2 ∣ Q) (hQ : Q ≠ 0) :
    PrimeGaps.singularSeries (maynardGammaPrime Q) = (Nat.totient Q : ℝ) / (Q : ℝ) *
        tailProduct Q := by
  classical
  set S : Set Nat.Primes := {p : Nat.Primes | (p : ℕ) ∣ Q} with hS
  have hpos : ∀ p : Nat.Primes, 0 < gFactor Q p := gFactor_pos Q h2
  have hsl : Summable (fun p : Nat.Primes ↦ Real.log (gFactor Q p)) := summable_log_gFactor Q h2 hQ
  have hsplit : (∏' p : Nat.Primes, gFactor Q p) = (∏' p : S, gFactor Q (p : Nat.Primes)) *
            (∏' p : (Sᶜ : Set Nat.Primes), gFactor Q (p : Nat.Primes)) := by
    rw [← Real.rexp_tsum_eq_tprod hpos hsl,
      ← Real.rexp_tsum_eq_tprod (fun p : S ↦ hpos _) (hsl.subtype (· ∈ S)),
      ← Real.rexp_tsum_eq_tprod (fun p : (Sᶜ : Set Nat.Primes) ↦ hpos _) (hsl.subtype (· ∈ Sᶜ)),
      ← Real.exp_add]
    exact congrArg _ (Summable.tsum_subtype_add_tsum_subtype_compl hsl S).symm
  have hdiv : (∏' p : S, gFactor Q (p : Nat.Primes)) = (Nat.totient Q : ℝ) / (Q : ℝ) := by
    have : Fintype (S : Type) := (finite_prime_dvd Q hQ).fintype
    have hWne : Q ≠ 0 := hQ
    have hWpos : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ.bot_lt
    have hfac : ∀ p : S, gFactor Q (p : Nat.Primes) = 1 - (((p : Nat.Primes) : ℕ) : ℝ)⁻¹ := by
      intro p
      have hp0 : (((p : Nat.Primes) : ℕ) : ℝ) ≠ 0 := by
        exact_mod_cast ((p : Nat.Primes).2).pos.ne'
      rw [gFactor_eq Q h2, if_pos (show ((p : Nat.Primes) : ℕ) ∣ Q from p.2)]
      field_simp
    rw [tprod_fintype]
    simp_rw [hfac]
    rw [show (∏ p : S, (1 - (((p : Nat.Primes) : ℕ) : ℝ)⁻¹)) =
          ∏ q ∈ Q.primeFactors, (1 - (q : ℝ)⁻¹) from ?_]
    · rw [show ((Nat.totient Q : ℝ)) =
          (Q : ℝ) * ∏ p ∈ Q.primeFactors, (1 - (p : ℝ)⁻¹) by
        have := congrArg (fun x : ℚ ↦ (x : ℝ)) (Nat.totient_eq_mul_prod_factors (Q))
        push_cast at this
        exact this]
      field_simp
    · apply Finset.prod_bij (fun (p : S) _ ↦ ((p : Nat.Primes) : ℕ))
      · exact fun p _ ↦ Nat.mem_primeFactors.mpr ⟨(p : Nat.Primes).2, p.2, hWne⟩
      · exact fun p _ q _ hpq ↦ Subtype.ext (Subtype.ext hpq)
      · intro q hq
        rw [Nat.mem_primeFactors] at hq
        exact ⟨⟨⟨q, hq.1⟩, hq.2.1⟩, Finset.mem_univ _, rfl⟩
      · exact fun p _ ↦ rfl
  have htail : (∏' p : (Sᶜ : Set Nat.Primes), gFactor Q (p : Nat.Primes)) = tailProduct Q := by
    rw [tailProduct, ← Equiv.tprod_eq
      (Equiv.subtypeEquivRight (p := fun p : Nat.Primes ↦ p ∈ (Sᶜ : Set Nat.Primes))
        (q := fun p : Nat.Primes ↦ ¬ (p : ℕ) ∣ Q) fun p ↦ Iff.rfl)]
    refine tprod_congr fun p ↦ ?_
    have hnd : ¬ ((p : Nat.Primes) : ℕ) ∣ Q := p.2
    simp only [Equiv.subtypeEquivRight_apply_coe]
    rw [gFactor_eq Q h2 (p : Nat.Primes), if_neg hnd]
  rw [singularSeries_eq_tprod_gFactor Q, hsplit, hdiv, htail]

/-- **Part 2 — the asymptotic.**  As `N → ∞`, uniformly in squarefree `Q` with `2 ∣ Q` and
`primorial ⌊D₀ N⌋₊ ∣ Q`, the singular product of the Maynard sieve `SieveDatum`'s `γ` field
satisfies `𝔖((maynardSieveDatum Q h2 hQ).γ) = (φ(Q)/Q)(1 + O(1/D₀))`. Concretely, there exist
`C > 0` and `x₀` such that for all `N ≥ x₀` the error of the singular product compared to
`φ(Q)/Q` is at most `C (φ(Q)/Q) / D₀ N`. -/
@[pg_tag "bg246" "slem_gg_singular_series"]
theorem singularSeries_maynardSieveDatum_γ_asymptotic : ∃ C > 0, ∃ x₀ : ℝ, ∀ N : ℕ, x₀ ≤ N →
      ∀ (Q : ℕ) (h2 : 2 ∣ Q) (hQ : Squarefree Q), primorial ⌊D₀ N⌋₊ ∣ Q →
      |PrimeGaps.singularSeries ((maynardSieveDatum Q h2 hQ).γ) -
        (Nat.totient Q : ℝ) / (Q : ℝ)| ≤
        C * ((Nat.totient Q : ℝ) / (Q : ℝ)) * (1 / D₀ N) := by
  refine ⟨4, by norm_num, rexp (rexp (rexp 4)), ?_⟩
  intro N hx₀ Q h2 hQ hQD
  rw [show PrimeGaps.singularSeries ((maynardSieveDatum Q h2 hQ).γ) =
      PrimeGaps.singularSeries (maynardGammaPrime Q) by
    unfold PrimeGaps.singularSeries
    refine tprod_congr fun p ↦ ?_
    by_cases hp : p.Prime
    · simp only [hp, if_true]
      rw [maynardSieveDatum_γ_prime Q h2 hQ p hp, maynardGammaPrime]
    · simp [hp]]
  have hN4 : 4 ≤ D₀ N := by
    have h1 : rexp (rexp 4) ≤ Real.log N :=
      calc rexp (rexp 4) = Real.log (rexp (rexp (rexp 4))) :=
            (Real.log_exp _).symm
        _ ≤ Real.log N := Real.log_le_log (Real.exp_pos _) hx₀
    have h2' : rexp 4 ≤ Real.log (Real.log N) :=
      calc rexp 4 = Real.log (rexp (rexp 4)) := (Real.log_exp _).symm
        _ ≤ Real.log (Real.log N) := Real.log_le_log (Real.exp_pos _) h1
    have h3 : (4 : ℝ) ≤ Real.log (Real.log (Real.log N)) :=
      calc (4 : ℝ) = Real.log (rexp 4) := (Real.log_exp _).symm
        _ ≤ Real.log (Real.log (Real.log N)) := Real.log_le_log (Real.exp_pos _) h2'
    exact h3
  have hφW_nonneg : (0 : ℝ) ≤ (Nat.totient Q : ℝ) / (Q : ℝ) := by positivity
  have htail_ge_one : (1 : ℝ) ≤ tailProduct Q := one_le_tailProduct Q h2 hQ.ne_zero
  rw [singularSeries_γ_g_eq_totient_mul_tail Q h2 hQ.ne_zero,
    show (Nat.totient Q : ℝ) / (Q : ℝ) * tailProduct Q -
        (Nat.totient Q : ℝ) / (Q : ℝ) =
      ((Nat.totient Q : ℝ) / (Q : ℝ)) * (tailProduct Q - 1) by ring,
    abs_mul, abs_of_nonneg hφW_nonneg,
    abs_of_nonneg (by linarith : (0 : ℝ) ≤ tailProduct Q - 1)]
  calc ((Nat.totient Q : ℝ) / (Q : ℝ)) * (tailProduct Q - 1)
      ≤ ((Nat.totient Q : ℝ) / (Q : ℝ)) * (4 * (1 / D₀ N)) :=
        mul_le_mul_of_nonneg_left (tailProduct_sub_one_le N Q hN4 h2 hQ.ne_zero hQD) hφW_nonneg
    _ = 4 * ((Nat.totient Q : ℝ) / (Q : ℝ)) * (1 / D₀ N) := by ring

end PrimeGaps

end
