module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Int.CardIntervalMod
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Data.Nat.Squarefree
public import Mathlib.Data.ZMod.QuotientRing
public import Mathlib.Tactic.LinearCombination

/-!
# Counting roots of linear forms by the Chinese remainder theorem

Let `F(v) = ∏_{j < κ} (α_j v + β_j)`, and let `d` be squarefree such that no prime `p ∣ d`
divides a leading coefficient `α_j` or a determinant `α_i β_j − α_j β_i`. Modulo such a prime
the roots `−β_j / α_j` are `κ` distinct classes, so by the Chinese remainder theorem `F` has
exactly `κ^{ω(d)}` roots modulo `d`. An interval of length `V` meets each class modulo `d`
`V / d + O(1)` times, so

  `#{v ∈ [v₁, v₁ + V) : d ∣ F(v)} = V ∏_{p ∣ d} κ / p + O(d)`.
-/

@[expose] public section

namespace Erdos420

open Finset
open scoped Function

variable {κ : ℕ} (α β : Fin κ → ℤ)

/-- The product `∏_j (α_j r + β_j)` of the linear forms, in any commutative ring. -/
def formsProd {R : Type*} [CommRing R] (r : R) : R :=
  ∏ j, ((α j : R) * r + β j)

/-- Ring homomorphisms commute with `formsProd`. -/
lemma map_formsProd {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (r : R) :
    f (formsProd α β r) = formsProd α β (f r) := by
  simp [formsProd, map_prod]

/-- Modulo a prime `p` dividing no `α_j` and no determinant, `F` has exactly `κ` roots. -/
lemma card_formsProd_eq_zero_prime {p : ℕ} [Fact p.Prime]
    (hα : ∀ j, ¬(p : ℤ) ∣ α j) (hdet : ∀ i j, i ≠ j → ¬(p : ℤ) ∣ α i * β j - α j * β i) :
    #{r : ZMod p | formsProd α β r = 0} = κ := by
  have hα' : ∀ j, (α j : ZMod p) ≠ 0 :=
    fun j h ↦ hα j ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h)
  -- the roots are the `−β_j / α_j`
  have hroots : ({r : ZMod p | formsProd α β r = 0} : Finset (ZMod p)) =
      univ.image fun j ↦ -(β j : ZMod p) / (α j : ZMod p) := by
    ext r
    simp only [formsProd, mem_filter, mem_univ, true_and, mem_image, prod_eq_zero_iff]
    constructor
    · rintro ⟨j, hj⟩
      refine ⟨j, ?_⟩
      field_simp [hα' j]
      linear_combination -hj
    · rintro ⟨j, rfl⟩
      refine ⟨j, ?_⟩
      field_simp [hα' j]
      ring
  rw [hroots, card_image_of_injective _ fun i j hij ↦ ?_, card_univ, Fintype.card_fin]
  by_contra hne
  apply hdet i j hne
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  field_simp [hα' i, hα' j] at hij
  push_cast
  linear_combination hij

/-- Modulo a squarefree `d` all of whose primes see `κ` distinct roots, `F` has exactly
`κ^{ω(d)}` roots. -/
lemma card_formsProd_eq_zero {d : ℕ} [NeZero d] (hd : Squarefree d)
    (h : ∀ p ∈ d.primeFactors,
      (∀ j, ¬(p : ℤ) ∣ α j) ∧ ∀ i j, i ≠ j → ¬(p : ℤ) ∣ α i * β j - α j * β i) :
    #{r : ZMod d | formsProd α β r = 0} = κ ^ #d.primeFactors := by
  have hcop : Pairwise (Nat.Coprime on fun i : d.primeFactors ↦ (i : ℕ)) := fun i j hij ↦
    (Nat.coprime_primes (Nat.prime_of_mem_primeFactors i.2)
      (Nat.prime_of_mem_primeFactors j.2)).mpr fun h ↦ hij (Subtype.ext h)
  have hprod : ∏ i : d.primeFactors, (i : ℕ) = d := by
    rw [prod_coe_sort d.primeFactors fun p ↦ p, Nat.prod_primeFactors_of_squarefree hd]
  have : ∀ i : d.primeFactors, Fact (i : ℕ).Prime :=
    fun i ↦ ⟨Nat.prime_of_mem_primeFactors i.2⟩
  -- the Chinese remainder theorem
  let e : ZMod d ≃+* Π i : d.primeFactors, ZMod (i : ℕ) :=
    (ZMod.ringEquivCongr hprod.symm).trans (ZMod.prodEquivPi _ hcop)
  have he : ∀ (r : ZMod d) (i : d.primeFactors), e (formsProd α β r) i = formsProd α β (e r i) :=
    fun r i ↦ map_formsProd α β ((Pi.evalRingHom _ i).comp e.toRingHom) r
  calc #{r : ZMod d | formsProd α β r = 0}
      = #(Fintype.piFinset fun i : d.primeFactors ↦
          ({x : ZMod (i : ℕ) | formsProd α β x = 0} : Finset _)) := by
        refine card_bij' (fun r _ ↦ e r) (fun f _ ↦ e.symm f) (fun r hr ↦ ?_) (fun f hf ↦ ?_)
          (fun r _ ↦ e.symm_apply_apply r) (fun f _ ↦ e.apply_symm_apply f)
        · simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset] at hr ⊢
          intro i
          rw [← he, hr, map_zero, Pi.zero_apply]
        · simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset] at hf ⊢
          refine e.injective ?_
          rw [map_zero]
          funext i
          rw [he, e.apply_symm_apply, Pi.zero_apply]
          exact hf i
    _ = ∏ i : d.primeFactors, #({x : ZMod (i : ℕ) | formsProd α β x = 0} : Finset _) :=
        Fintype.card_piFinset _
    _ = ∏ _i : d.primeFactors, κ :=
        prod_congr rfl fun i _ ↦ card_formsProd_eq_zero_prime α β (h i i.2).1 (h i i.2).2
    _ = κ ^ #d.primeFactors := by rw [prod_const, card_univ, Fintype.card_coe]

/-- `⌈a + b⌉ - ⌈a⌉` is a nonnegative integer within `1` of `b ≥ 0`. -/
private lemma ceil_add_sub_ceil (a b : ℚ) (hb : 0 ≤ b) :
    0 ≤ ⌈a + b⌉ - ⌈a⌉ ∧ |((⌈a + b⌉ - ⌈a⌉ : ℤ) : ℚ) - b| ≤ 1 := by
  have h₁ := Int.le_ceil (a + b)
  have h₂ := Int.ceil_lt_add_one (a + b)
  have h₃ := Int.le_ceil a
  have h₄ := Int.ceil_lt_add_one a
  refine ⟨sub_nonneg.mpr (Int.ceil_mono (by linarith)), ?_⟩
  rw [abs_le]
  push_cast
  constructor <;> linarith

/-- An interval of length `V` meets a class modulo `d` `V / d + O(1)` times. -/
private lemma abs_card_filter_intCast_eq_sub_le {d : ℕ} [NeZero d] (r : ZMod d) (v₁ : ℤ) (V : ℕ) :
    |(#{v ∈ Ico v₁ (v₁ + V) | ((v : ℤ) : ZMod d) = r} : ℝ) - V / d| ≤ 1 := by
  have hd : (0 : ℤ) < d := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  have hfilter : {v ∈ Ico v₁ (v₁ + V) | ((v : ℤ) : ZMod d) = r} =
      {v ∈ Ico v₁ (v₁ + V) | v ≡ (r.val : ℤ) [ZMOD d]} := by
    refine filter_congr fun v _ ↦ ?_
    rw [← ZMod.intCast_eq_intCast_iff, Int.cast_natCast, ZMod.natCast_zmod_val]
  have hcard := Int.Ico_filter_modEq_card v₁ (v₁ + V) hd (r.val : ℤ)
  rw [← hfilter] at hcard
  have hx : ((((v₁ + V : ℤ) : ℚ) - ((r.val : ℤ) : ℚ)) / ((d : ℤ) : ℚ)) =
      (((v₁ : ℚ) - ((r.val : ℤ) : ℚ)) / ((d : ℤ) : ℚ)) + (V : ℚ) / ((d : ℤ) : ℚ) := by
    push_cast
    ring
  rw [hx] at hcard
  obtain ⟨h₀, h₁⟩ := ceil_add_sub_ceil (((v₁ : ℚ) - ((r.val : ℤ) : ℚ)) / ((d : ℤ) : ℚ))
    ((V : ℚ) / ((d : ℤ) : ℚ)) (by positivity)
  rw [max_eq_left h₀] at hcard
  rw [← hcard] at h₁
  have h₂ := (Rat.cast_le (K := ℝ)).mpr h₁
  push_cast at h₂
  exact h₂

/-- An interval of length `V` meets a set `S` of classes modulo `d` `V |S| / d + O(|S|)` times. -/
private lemma abs_card_filter_intCast_mem_sub_le {d : ℕ} [NeZero d] (S : Finset (ZMod d)) (v₁ : ℤ)
    (V : ℕ) :
    |(#{v ∈ Ico v₁ (v₁ + V) | ((v : ℤ) : ZMod d) ∈ S} : ℝ) - V * #S / d| ≤ #S := by
  have hcard : (#{v ∈ Ico v₁ (v₁ + V) | ((v : ℤ) : ZMod d) ∈ S} : ℝ) =
      ∑ r ∈ S, (#{v ∈ Ico v₁ (v₁ + V) | ((v : ℤ) : ZMod d) = r} : ℝ) := by
    rw [← sum_card_fiberwise_eq_card_filter (Ico v₁ (v₁ + V)) S fun v : ℤ ↦ ((v : ℤ) : ZMod d)]
    push_cast
    rfl
  calc |(#{v ∈ Ico v₁ (v₁ + V) | ((v : ℤ) : ZMod d) ∈ S} : ℝ) - V * #S / d|
      = |∑ r ∈ S, ((#{v ∈ Ico v₁ (v₁ + V) | ((v : ℤ) : ZMod d) = r} : ℝ) - V / d)| := by
        rw [hcard, sum_sub_distrib, sum_const, nsmul_eq_mul]
        ring_nf
    _ ≤ ∑ r ∈ S, |(#{v ∈ Ico v₁ (v₁ + V) | ((v : ℤ) : ZMod d) = r} : ℝ) - V / d| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ _r ∈ S, (1 : ℝ) := sum_le_sum fun r _ ↦ abs_card_filter_intCast_eq_sub_le r v₁ V
    _ = #S := by rw [sum_const, nsmul_eq_mul, mul_one]

/-- `#{v ∈ [v₁, v₁ + V) : d ∣ F(v)} = V ∏_{p ∣ d} κ / p + O(d)` for squarefree `d` all of whose
primes see `κ` distinct roots. -/
theorem abs_card_filter_dvd_formsProd_sub_le {d : ℕ} (hd : Squarefree d)
    (h : ∀ p ∈ d.primeFactors,
      (∀ j, ¬(p : ℤ) ∣ α j) ∧ ∀ i j, i ≠ j → ¬(p : ℤ) ∣ α i * β j - α j * β i)
    (v₁ : ℤ) (V : ℕ) :
    |(#{v ∈ Ico v₁ (v₁ + V) | (d : ℤ) ∣ formsProd α β v} : ℝ) -
        V * ∏ p ∈ d.primeFactors, (κ : ℝ) / p| ≤ d := by
  have : NeZero d := ⟨hd.ne_zero⟩
  set S : Finset (ZMod d) := {r | formsProd α β r = 0} with hS_def
  have hS := card_formsProd_eq_zero α β hd h
  have hfilter : {v ∈ Ico v₁ (v₁ + V) | (d : ℤ) ∣ formsProd α β v} =
      {v ∈ Ico v₁ (v₁ + V) | ((v : ℤ) : ZMod d) ∈ S} := by
    refine filter_congr fun v _ ↦ ?_
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, hS_def, mem_filter]
    have := map_formsProd α β (Int.castRingHom (ZMod d)) v
    simp only [eq_intCast] at this
    rw [this]
    simp
  have hmain : (V : ℝ) * ∏ p ∈ d.primeFactors, (κ : ℝ) / p = V * #S / d := by
    rw [hS, prod_div_distrib, prod_const, ← Nat.cast_prod,
      Nat.prod_primeFactors_of_squarefree hd]
    push_cast
    ring
  rw [hfilter, hmain]
  refine (abs_card_filter_intCast_mem_sub_le S v₁ V).trans ?_
  exact_mod_cast (card_le_univ S).trans (ZMod.card d).le

end Erdos420
