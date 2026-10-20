import Erdos420.Maynard.RoughnessBound.Local
import Erdos420.Maynard.RoughnessBound.PrimeSums

/-!
# Maynard's roughness bound

This is Proposition 6.1(4) of Maynard, *Dense clusters of primes in subsets*
(Compositio Math. 152 (2016)), proved there as Proposition 9.5, for the weights of
`vendor/PrimeGapsLib`: for every `ε > 0` there is `ρ > 0` such that the `n ≡ w₀ (mod Q)` in
`(N, 2N]` for which some `n + hᵢ` has a prime factor `p ≤ N^ρ` carry at most `ε` times the
mass scale of `S₁`.

Every such `p` is coprime to `Q`, so the weight is at most the sum over `m` and primes
`p ≤ N^ρ`, `p ∤ Q`, of the weight on `n` with `p ∣ n + h_m`. By `exists_sum_weight_dvd_le`
that is at most `C (N / (Q p)) B_p² A^k + (C B_p R (log R)^{2k})²`, where
`B_p = L log p / log R + (k − 1) F₀ / (p − 1)` and `A = sumA Q R ≪ (φ(Q)/Q) log R`. So the main
terms total `≪ mainScale ∑_p B_p² / p`, with
`∑_{p ≤ N^ρ} (log p / log R)² / p ≤ 2 (ρ / (θ/2 − δ))²` by Mertens' first theorem and
`∑_{p > D₀} 1 / ((p − 1)² p) ≪ 1 / D₀`. The `≤ 2 N^ρ` error terms are
`N^ρ R² (log R)^{4k} ≤ mainScale / D₀` by the library's `eventually_master` at
`δ' = δ − ρ / 2`, which needs `θ − 2δ + ρ + η < 1`.
-/

namespace Erdos420

open Finset
open scoped PrimeGaps

open scoped Classical in
/-- The `n` with some `p ∣ n + hᵢ`, `p ≤ X`, `p ∈ P` are covered by the sets `p ∣ n + h_m`. -/
lemma sum_filter_exists_dvd_le {k : ℕ} (h : Fin k → ℕ) (S : Finset ℕ) (A : ℕ → Prop)
    [DecidablePred A] (X : ℝ) (P : Finset ℕ) (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n)
    (hP : ∀ n ∈ S, A n → ∀ i p, p.Prime → p ∣ n + h i → (p : ℝ) ≤ X → p ∈ P) :
    ∑ n ∈ S with A n ∧ ∃ i, ∃ p : ℕ, p.Prime ∧ p ∣ n + h i ∧ (p : ℝ) ≤ X, f n ≤
      ∑ m, ∑ p ∈ P, ∑ n ∈ S with A n ∧ p ∣ n + h m, f n := by
  classical
  have hnn : ∀ n m p, 0 ≤ if A n ∧ p ∣ n + h m then f n else 0 := fun n m p ↦ by
    split_ifs
    · exact hf n
    · exact le_rfl
  calc ∑ n ∈ S with A n ∧ ∃ i, ∃ p : ℕ, p.Prime ∧ p ∣ n + h i ∧ (p : ℝ) ≤ X, f n
      = ∑ n ∈ S, if A n ∧ ∃ i, ∃ p : ℕ, p.Prime ∧ p ∣ n + h i ∧ (p : ℝ) ≤ X then f n else 0 :=
        sum_filter _ _
    _ ≤ ∑ n ∈ S, ∑ m, ∑ p ∈ P, if A n ∧ p ∣ n + h m then f n else 0 := by
        refine sum_le_sum fun n hn ↦ ?_
        split_ifs with hbad
        · obtain ⟨hA, i, p, hp, hpd, hpX⟩ := hbad
          have hpP := hP n hn hA i p hp hpd hpX
          calc f n = if A n ∧ p ∣ n + h i then f n else 0 := (ite_eq_left ⟨hA, hpd⟩).symm
            _ ≤ ∑ p ∈ P, if A n ∧ p ∣ n + h i then f n else 0 :=
                single_le_sum (f := fun p ↦ if A n ∧ p ∣ n + h i then f n else 0)
                  (fun p _ ↦ hnn n i p) hpP
            _ ≤ ∑ m, ∑ p ∈ P, if A n ∧ p ∣ n + h m then f n else 0 :=
                single_le_sum (f := fun m ↦ ∑ p ∈ P, if A n ∧ p ∣ n + h m then f n else 0)
                  (fun m _ ↦ sum_nonneg fun p _ ↦ hnn n m p) (mem_univ i)
        · exact sum_nonneg fun m _ ↦ sum_nonneg fun p _ ↦ hnn n m p
    _ = ∑ m, ∑ p ∈ P, ∑ n ∈ S with A n ∧ p ∣ n + h m, f n := by
        rw [sum_comm]
        refine sum_congr rfl fun m _ ↦ ?_
        rw [sum_comm]
        exact sum_congr rfl fun p _ ↦ (sum_filter _ _).symm

/-- The master inequality at `R' = N^{c₀ + ρ/2}` gives
`N^ρ R² (log R)^{4k} ≤ φ^k N (log R)^k / (Q^{k+1} D)` at `R = N^{c₀}`. -/
private lemma rpow_mul_sq_mul_log_pow_le {N ρ c₀ Q φ D : ℝ} (hN : 1 < N) (hρ : 0 ≤ ρ) (hc₀ : 0 ≤ c₀)
    (hQ : 0 < Q) (hD : 0 < D) {k : ℕ}
    (hmaster : (N ^ (c₀ + ρ / 2)) ^ 2 * Real.log (N ^ (c₀ + ρ / 2)) ^ (3 * k) * Q ^ (k + 1) * D ≤
      φ ^ k * N) :
    N ^ ρ * (N ^ c₀) ^ 2 * Real.log (N ^ c₀) ^ (4 * k) ≤
      φ ^ k * N * Real.log (N ^ c₀) ^ k / Q ^ (k + 1) / D := by
  have hN0 : 0 < N := by linarith
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg hN.le
  have hsq : (N ^ (c₀ + ρ / 2)) ^ 2 = N ^ ρ * (N ^ c₀) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le,
      ← Real.rpow_mul hN0.le, ← Real.rpow_add hN0]
    congr 1
    push_cast
    ring
  have hlog : Real.log (N ^ c₀) ≤ Real.log (N ^ (c₀ + ρ / 2)) := by
    rw [Real.log_rpow hN0, Real.log_rpow hN0]
    nlinarith
  have hlog0 : 0 ≤ Real.log (N ^ c₀) := by rw [Real.log_rpow hN0]; positivity
  rw [div_div, le_div_iff₀ (by positivity)]
  calc N ^ ρ * (N ^ c₀) ^ 2 * Real.log (N ^ c₀) ^ (4 * k) * (Q ^ (k + 1) * D)
      = N ^ ρ * (N ^ c₀) ^ 2 * Real.log (N ^ c₀) ^ (3 * k) * Q ^ (k + 1) * D *
          Real.log (N ^ c₀) ^ k := by
        rw [show 4 * k = 3 * k + k by ring, pow_add]
        ring
    _ ≤ (N ^ (c₀ + ρ / 2)) ^ 2 * Real.log (N ^ (c₀ + ρ / 2)) ^ (3 * k) * Q ^ (k + 1) * D *
          Real.log (N ^ c₀) ^ k := by
        rw [hsq]
        gcongr
    _ ≤ φ ^ k * N * Real.log (N ^ c₀) ^ k := by gcongr

/-- The CRT terms: `#P (C B R ℓ^{2k})² ≤ 2 C² B² S / D` from `#P ≤ 2 X` and
`X R² ℓ^{4k} ≤ S / D`. -/
private lemma mul_sq_le_of_le {cardP X C B R ℓ S D : ℝ} {k : ℕ} (hcard : cardP ≤ 2 * X)
    (hbase : X * R ^ 2 * ℓ ^ (4 * k) ≤ S / D) :
    cardP * (C * B * R * ℓ ^ (2 * k)) ^ 2 ≤ (2 * C ^ 2 * B ^ 2 / D) * S := by
  have hsq : (C * B * R * ℓ ^ (2 * k)) ^ 2 = C ^ 2 * B ^ 2 * (R ^ 2 * ℓ ^ (4 * k)) := by
    rw [show 4 * k = 2 * k * 2 by ring, pow_mul]
    ring
  have h0 : 0 ≤ C ^ 2 * B ^ 2 := by positivity
  calc cardP * (C * B * R * ℓ ^ (2 * k)) ^ 2 ≤ 2 * X * (C * B * R * ℓ ^ (2 * k)) ^ 2 := by
        gcongr
    _ = 2 * (C ^ 2 * B ^ 2) * (X * R ^ 2 * ℓ ^ (4 * k)) := by rw [hsq]; ring
    _ ≤ 2 * (C ^ 2 * B ^ 2) * (S / D) := by gcongr
    _ = (2 * C ^ 2 * B ^ 2 / D) * S := by ring

/-- `A / D ≤ ε / 3` once `D ≥ 3 A / ε`. -/
private lemma div_le_div_three {A D ε : ℝ} (hε : 0 < ε) (hD : 0 < D) (h : 3 * A / ε ≤ D) :
    A / D ≤ ε / 3 := by
  rw [div_le_iff₀ hε] at h
  rw [div_le_iff₀ hD]
  linarith

/-- With `ρ ≤ min (1/4) (ε c₀² / (12 k K (L² + 1)))`, `k K · 4 L² ρ² / c₀² ≤ ε / 3`. -/
private lemma mul_rho_sq_le {k K L ρ c₀ ε : ℝ} (hk : 0 < k) (hK : 0 < K) (hc₀ : 0 < c₀) (hρ : 0 ≤ ρ)
    (hρ1 : ρ ≤ 1) (hρε : ρ ≤ ε * c₀ ^ 2 / (12 * k * K * (L ^ 2 + 1))) :
    k * K * (4 * L ^ 2 * ρ ^ 2 / c₀ ^ 2) ≤ ε / 3 := by
  have hρsq : ρ ^ 2 ≤ ρ := by nlinarith
  calc k * K * (4 * L ^ 2 * ρ ^ 2 / c₀ ^ 2) ≤ k * K * (4 * (L ^ 2 + 1) * ρ / c₀ ^ 2) := by
        gcongr
        · nlinarith
    _ ≤ k * K * (4 * (L ^ 2 + 1) * (ε * c₀ ^ 2 / (12 * k * K * (L ^ 2 + 1))) / c₀ ^ 2) := by
        gcongr
    _ = ε / 3 := by field_simp; ring

/-- The final combination: main terms `k K S ∑ B_p² / p` and CRT terms `k #P E`. -/
private lemma mul_add_le_of_le {k K S T cardP E a b c ε : ℝ} (hk : 0 ≤ k) (hK : 0 ≤ K) (hS : 0 ≤ S)
    (hT : T ≤ a + b) (hE : cardP * E ≤ c * S) (ha : k * K * a ≤ ε / 3) (hb : k * K * b ≤ ε / 3)
    (hc : k * c ≤ ε / 3) :
    k * (K * S * T + cardP * E) ≤ ε * S := by
  have h1 : k * (K * S * T) ≤ k * K * a * S + k * K * b * S := by
    have := mul_le_mul_of_nonneg_left hT (mul_nonneg (mul_nonneg hk hK) hS)
    nlinarith
  have h2 : k * (cardP * E) ≤ k * c * S := by nlinarith
  nlinarith

open PrimeGaps in
open scoped PrimeGaps.sieveTruncation in
open scoped Classical in
/-- **Maynard's Proposition 6.1(4).** For every `ε > 0` there is `ρ > 0` such that, for large
`N`, every modulus `Q` with `ModulusHyp` and every valid class `w₀ (mod Q)`, the `n ∈ (N, 2N]`
in the class for which some `n + hᵢ` has a prime factor `p ≤ N^ρ` carry sieve weight at most
`ε mainScale`. -/
theorem exists_sum_weight_nonrough_le {k : ℕ}
    (hk : 2 ≤ k) (h : Fin k → ℕ) (hadm : GPYSieveS1.IsAdmissible h)
    (F : EuclideanSpace ℝ (Fin k) → ℝ) (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hsupp : Function.support F ⊆ 𝓡 k)
    (θ δ : ℝ) (hθ0 : 0 < θ) (hθ : θ < 1 / 2) (hδ : 0 < δ) (hδθ : δ < θ / 2)
    (CQ η : ℝ) (hη : η < 2 * δ) :
    ∀ ε > (0 : ℝ), ∃ ρ > (0 : ℝ), ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ N →
      ∀ Q : ℕ, PrimeGaps.ModulusHyp CQ η N Q → ∀ w₀ : ZMod Q,
        (∀ i, ((w₀.val : ℤ) + h i).gcd Q = 1) →
        ∑ n ∈ Ioc N (2 * N) with (n : ℕ) = w₀ ∧
            ∃ i, ∃ p : ℕ, p.Prime ∧ p ∣ n + h i ∧ (p : ℝ) ≤ (N : ℝ) ^ ρ,
          PrimeGaps.weight h (PrimeGaps.l₀ (PrimeGaps.sieveTruncation N δ θ) Q
            (fun x ↦ F (WithLp.toLp 2 x.ofLp))) n ≤
        ε * PrimeGaps.mainScale k N (PrimeGaps.sieveTruncation N δ θ) Q := by
  classical
  intro ε hε
  -- `F` is Lipschitz and bounded
  have hcs : HasCompactSupport F :=
    HasCompactSupport.of_support_subset_isCompact EuclideanSpace.isCompact_scaledStdSimplex hsupp
  obtain ⟨L, hL⟩ := hF.lipschitzWith_of_hasCompactSupport hcs (by simp)
  obtain ⟨F₀, hF₀⟩ := hF.continuous.bounded_above_of_compact_support hcs
  have hF₀' : ∀ x, |F x| ≤ F₀ := fun x ↦ by simpa using hF₀ x
  have hF₀0 : 0 ≤ F₀ := (abs_nonneg _).trans (hF₀' 0)
  set c₀ := θ / 2 - δ with hc₀def
  have hc₀ : 0 < c₀ := by linarith
  have hk1 : (1 : ℝ) ≤ k - 1 := by
    have : (2 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  obtain ⟨C, hC, NL, hLoc⟩ := exists_sum_weight_dvd_le hk h hadm F hsupp L hL F₀ hF₀' θ δ
    ⟨hθ0, by linarith⟩ ⟨hδ, hδθ⟩ CQ η
  obtain ⟨c₁, hc₁, NM, hM⟩ := mertens_factor δ θ ⟨hδ, hδθ, by linarith⟩ CQ η
  set K := C * c₁ ^ k with hKdef
  have hK : 0 < K := by positivity
  set ρ := min (1 / 4) (ε * c₀ ^ 2 / (12 * k * K * ((L : ℝ) ^ 2 + 1)))
  have hρ : 0 < ρ := lt_min (by norm_num) (by positivity)
  have hρ4 : ρ ≤ 1 / 4 := min_le_left _ _
  have hρε : ρ ≤ ε * c₀ ^ 2 / (12 * k * K * ((L : ℝ) ^ 2 + 1)) := min_le_right _ _
  set Bs := (L : ℝ) * (ρ / c₀) + (k - 1) * F₀
  have hBs : 0 ≤ Bs := by positivity
  set D₁ := max (6 * k * C ^ 2 * Bs ^ 2 / ε) (48 * k * K * (k - 1) ^ 2 * F₀ ^ 2 / ε) + 1
  -- conditions on `N`
  set δ' := δ - ρ / 2 with hδ'def
  have hmaster := eventually_master k θ δ' CQ η (by linarith)
    (by rw [hδ'def]; linarith)
  have hD : ∀ᶠ N : ℕ in Filter.atTop, D₁ ≤ D₀ N :=
    (D0_tendsto_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop D₁
  have hlog : ∀ᶠ N : ℕ in Filter.atTop, Real.log 4 / ρ ≤ Real.log N :=
    tendsto_log_natCast_atTop.eventually_ge_atTop _
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp (hmaster.and (hD.and hlog))
  refine ⟨ρ, hρ, max (max NL NM) N₁, ?_⟩
  intro N hN Q hQ w₀ hw₀
  have hNL : NL ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hNM : NM ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  obtain ⟨hmasterN, hDN, hlogN⟩ :=
    hN₁ N (by exact_mod_cast le_trans (le_max_right _ _) hN)
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hlogNpos : 0 < Real.log N := lt_of_lt_of_le (by positivity) hlogN
  have hN1 : (1 : ℝ) < N := by
    by_contra hle
    exact absurd hlogNpos (not_lt.mpr (Real.log_nonpos (Nat.cast_nonneg _) (not_lt.mp hle)))
  have hN0 : (0 : ℝ) < N := by linarith
  have hρlog : Real.log 4 ≤ ρ * Real.log N := by
    rwa [div_le_iff₀ hρ, mul_comm] at hlogN
  have hlogR : Real.log R = c₀ * Real.log N := Real.log_rpow hN0 _
  have hlogRpos : 0 < Real.log R := by rw [hlogR]; positivity
  have hD₀pos : 0 < D₀ N := lt_of_lt_of_le (by positivity) hDN
  set S := PrimeGaps.mainScale k N R Q with hSdef
  have hS0 : 0 ≤ S := by
    rw [hSdef, PrimeGaps.mainScale]
    have := hlogRpos.le
    positivity
  set M := ⌊(N : ℝ) ^ ρ⌋₊
  have hNρ1 : 1 ≤ (N : ℝ) ^ ρ := Real.one_le_rpow hN1.le hρ.le
  have hM1 : 1 ≤ M := Nat.le_floor (by exact_mod_cast hNρ1)
  have hMle : (M : ℝ) ≤ (N : ℝ) ^ ρ := Nat.floor_le (by positivity)
  set P := (Nat.primesLE M).filter (fun p ↦ ¬p ∣ Q)
  set wt : ℕ → ℝ := fun n ↦ PrimeGaps.weight h (PrimeGaps.l₀ (PrimeGaps.sieveTruncation N δ θ)
    Q (fun x ↦ F (WithLp.toLp 2 x.ofLp))) n
  -- cover by the primes `p ∈ P`
  have hcover := sum_filter_exists_dvd_le h (Ioc N (2 * N)) (fun n ↦ (n : ZMod Q) = w₀)
    ((N : ℝ) ^ ρ) P wt (fun n ↦ PrimeGaps.w_nonneg) fun n _ hn i p hp hpd hpX ↦ by
      refine mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨Nat.le_floor hpX, hp⟩, fun hpQ ↦ ?_⟩
      have : NeZero Q := ⟨hQ.ne_zero⟩
      exact not_dvd_add_of_gcd_eq_one (hw₀ i) hn hp hpQ hpd
  refine hcover.trans ?_
  -- the bound for each prime
  set B : ℕ → ℝ := fun p ↦ L * (Real.log p / Real.log R) + (k - 1) / (p - 1) * F₀
  have hPprime : ∀ p ∈ P, p.Prime := fun p hp ↦ (Nat.mem_primesLE.mp (mem_filter.mp hp).1).2
  have hB0 : ∀ p ∈ P, 0 ≤ B p := fun p hp ↦ by
    have hp1 : (1 : ℝ) < p := by exact_mod_cast (hPprime p hp).one_lt
    have : (0 : ℝ) ≤ Real.log p := Real.log_nonneg hp1.le
    have : (0 : ℝ) < p - 1 := by linarith
    positivity
  have hBle : ∀ p ∈ P, B p ≤ Bs := fun p hp ↦ by
    have hp1 : (2 : ℝ) ≤ p := by exact_mod_cast (hPprime p hp).two_le
    have hpM : (p : ℝ) ≤ (N : ℝ) ^ ρ :=
      le_trans (by exact_mod_cast (Nat.mem_primesLE.mp (mem_filter.mp hp).1).1) hMle
    have hlogp : Real.log p ≤ ρ * Real.log N := by
      rw [← Real.log_rpow hN0]
      exact Real.log_le_log (by linarith) hpM
    have h1 : Real.log p / Real.log R ≤ ρ / c₀ := by
      rw [hlogR, div_le_div_iff₀ (by positivity) hc₀]
      nlinarith
    have h2 : (k - 1 : ℝ) / (p - 1) ≤ k - 1 :=
      div_le_self (by linarith) (by linarith)
    exact add_le_add (mul_le_mul_of_nonneg_left h1 L.2) (mul_le_mul_of_nonneg_right h2 hF₀0)
  have hstep : ∀ m, ∀ p ∈ P, ∑ n ∈ Ioc N (2 * N) with (n : ℕ) = w₀ ∧ p ∣ n + h m, wt n ≤
      K * (B p ^ 2 / p) * S + (C * Bs * R * Real.log R ^ (2 * k)) ^ 2 := by
    intro m p hp
    refine (hLoc N hNL Q hQ w₀ hw₀ m p (hPprime p hp) (mem_filter.mp hp).2).trans ?_
    have hA0 : 0 ≤ MaynardOffDiagonal.sumA Q R := sum_nonneg fun _ _ ↦ by positivity
    have hA := hM N hNM Q hQ
    have hQ0 : (0 : ℝ) < Q := by exact_mod_cast hQ.pos
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (hPprime p hp).pos
    have hR0 : 0 ≤ R := by positivity
    have hlogR2k : 0 ≤ Real.log R ^ (2 * k) := pow_nonneg hlogRpos.le _
    refine add_le_add ?_ ?_
    · calc C * (N / (Q * p : ℝ)) * B p ^ 2 * MaynardOffDiagonal.sumA Q R ^ k
          ≤ C * (N / (Q * p : ℝ)) * B p ^ 2 *
              (c₁ * ((Q.totient : ℝ) / Q) * Real.log R) ^ k := by gcongr
        _ = K * (B p ^ 2 / p) * S := by
            rw [hSdef, PrimeGaps.mainScale, hKdef, mul_pow, mul_pow, div_pow]
            field_simp
            ring
    · have := hB0 p hp
      have := hBle p hp
      gcongr
  calc ∑ m, ∑ p ∈ P, ∑ n ∈ Ioc N (2 * N) with (n : ℕ) = w₀ ∧ p ∣ n + h m, wt n
      ≤ ∑ _m : Fin k, ∑ p ∈ P, (K * (B p ^ 2 / p) * S +
          (C * Bs * R * Real.log R ^ (2 * k)) ^ 2) :=
        sum_le_sum fun m _ ↦ sum_le_sum fun p hp ↦ hstep m p hp
    _ = k * (K * S * ∑ p ∈ P, B p ^ 2 / p +
          #P * (C * Bs * R * Real.log R ^ (2 * k)) ^ 2) := by
        rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, sum_add_distrib, sum_const,
          nsmul_eq_mul, mul_sum]
        congr 2
        exact sum_congr rfl fun p _ ↦ by ring
    _ ≤ ε * S := ?_
  -- the main terms: `∑_p B_p² / p ≤ 4 L² ρ² / c₀² + 16 (k − 1)² F₀² / (⌊D₀⌋ + 1)`
  have hlogM : Real.log M ≤ ρ * Real.log N := by
    rw [← Real.log_rpow hN0]
    exact Real.log_le_log (by exact_mod_cast hM1) hMle
  have hPD : ∀ p ∈ P, ⌊D₀ N⌋₊ < p := fun p hp ↦ by
    by_contra hle
    exact (mem_filter.mp hp).2 (hQ.prime_dvd_of_le_D₀ (hPprime p hp)
      ((Nat.le_floor_iff hD₀pos.le).mp (not_lt.mp hle)))
  have hmainsum : ∑ p ∈ P, B p ^ 2 / p ≤
      4 * L ^ 2 * ρ ^ 2 / c₀ ^ 2 + 16 * (k - 1) ^ 2 * F₀ ^ 2 / (⌊D₀ N⌋₊ + 1) := by
    refine (sum_sq_div_le (filter_subset _ _) hPD hM1 L (Real.log R) (k - 1) F₀
      (ρ * Real.log N) hlogM hρlog).trans_eq ?_
    rw [hlogR]
    field_simp
  -- the CRT errors: `#P (C Bs R (log R)^{2k})² ≤ 2 C² Bs² S / D₀`
  have hcard : (#P : ℝ) ≤ 2 * (N : ℝ) ^ ρ := by
    have : #P ≤ M + 1 := (card_filter_le _ _).trans ((card_filter_le _ _).trans
      (card_range _).le)
    calc (#P : ℝ) ≤ M + 1 := by exact_mod_cast this
      _ ≤ 2 * (N : ℝ) ^ ρ := by linarith
  have hcrtbase : (N : ℝ) ^ ρ * R ^ 2 * Real.log R ^ (4 * k) ≤ S / D₀ N := by
    have he : θ / 2 - δ' = c₀ + ρ / 2 := by rw [hδ'def, hc₀def]; ring
    have hm := hmasterN Q hQ
    rw [show PrimeGaps.sieveTruncation N δ' θ = (N : ℝ) ^ (c₀ + ρ / 2) from
      congrArg ((N : ℝ) ^ ·) he] at hm
    rw [hSdef, PrimeGaps.mainScale]
    exact rpow_mul_sq_mul_log_pow_le hN1 hρ.le hc₀.le (by exact_mod_cast hQ.pos) hD₀pos hm
  have hcrt : (#P : ℝ) * (C * Bs * R * Real.log R ^ (2 * k)) ^ 2 ≤
      (2 * C ^ 2 * Bs ^ 2 / D₀ N) * S :=
    mul_sq_le_of_le hcard hcrtbase
  -- the choice of `ρ` and `N`
  have hD₁a : 3 * (k * (2 * C ^ 2 * Bs ^ 2)) / ε ≤ D₀ N := by
    have : 6 * k * C ^ 2 * Bs ^ 2 / ε ≤ D₁ :=
      (le_max_left _ _).trans (le_add_of_nonneg_right zero_le_one)
    calc 3 * (k * (2 * C ^ 2 * Bs ^ 2)) / ε = 6 * k * C ^ 2 * Bs ^ 2 / ε := by ring
      _ ≤ D₁ := this
      _ ≤ D₀ N := hDN
  have hD₁b : 3 * (k * K * (16 * (k - 1) ^ 2 * F₀ ^ 2)) / ε ≤ ⌊D₀ N⌋₊ + 1 := by
    have : 48 * k * K * (k - 1) ^ 2 * F₀ ^ 2 / ε ≤ D₁ :=
      (le_max_right _ _).trans (le_add_of_nonneg_right zero_le_one)
    calc 3 * (k * K * (16 * (k - 1) ^ 2 * F₀ ^ 2)) / ε =
          48 * k * K * (k - 1) ^ 2 * F₀ ^ 2 / ε := by ring
      _ ≤ D₁ := this
      _ ≤ D₀ N := hDN
      _ ≤ ⌊D₀ N⌋₊ + 1 := (Nat.lt_floor_add_one _).le
  refine mul_add_le_of_le (Nat.cast_nonneg k) hK.le hS0 hmainsum hcrt
    (mul_rho_sq_le (by positivity) hK hc₀ hρ.le (by linarith) hρε) ?_ ?_
  · rw [mul_div_assoc']
    exact div_le_div_three hε (by positivity) hD₁b
  · rw [mul_div_assoc']
    exact div_le_div_three hε hD₀pos hD₁a

end Erdos420
