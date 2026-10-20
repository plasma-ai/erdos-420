import Erdos420.Maynard.Classes
import Erdos420.Maynard.Hypotheses
import Erdos420.Maynard.Modulus
import Erdos420.Maynard.Pointwise
import Erdos420.Maynard.RoughnessBound
import Erdos420.Maynard.Variational
import PrimeGapsTheory.Variational.MkApprox

/-!
# Maynard's sieve for a growing CRT modulus

This is Proposition 6.1 of Maynard, *Dense clusters of primes in subsets*
(Compositio Math. 152 (2016)), for the forms `L_i(t) = a₀ + M t + b_i` with
`t ∈ [N, 2N)`, `M N ≍ X`, and `M ≤ X^{1/64}` squarefree with prime factors at most
`log X / 2`. The analytic inputs are the prime number theorem and the level of
distribution `Erdos420.hasPowerSavingLevel`, which comes from primes in progressions
with error `x^{15/16} log² x`.

For each `m`, a fixed admissible tuple `b` of size `r` gives weights
`W ≥ 0` with
- prime surplus: `∑ W(t) (#{i : L_i(t) prime} − (m − 1)) ≥ γ ∑ W`;
- mass: `∑ W ≥ c N / (log X)^r`, since the singular series is at least a
  constant times `(M / φ(M))^r ≥ 1`;
- roughness: the `t` for which some `L_i(t)` has a prime factor `≤ X^ρ` carry
  at most `η ∑ W`, for `ρ` small in terms of `η` (Proposition 6.1(4));
- a pointwise bound `W(t) ≤ C` when every `L_i(t)` is `X^ρ`-rough, since then
  each `L_i(t)` has `O(1/ρ)` divisors.

The weights come from the sieve of `vendor/PrimeGapsLib` for the forms `n + b_i` with
`n = a₀ + M t ∈ (N', 2N']`, `N' = a₀ + M (N − 1)`, over the residue classes
`n ≡ v (mod Q)`, `Q = M W'`, where `W'` is the product of the primes `p ≤ D₀(N')` not
dividing `M`. Every class above `a₀ (mod M)` with each `v + b_i` coprime to `Q` is used,
so that `W(t)` is Maynard's `w(a₀ + M t)` on all of them, divided by
`((φ(Q)/Q) log R)^{2r}`. There are `≫ W' (φ(W')/W')^r` such classes
(`exists_le_card_validClasses`), each of mass `≍ (φ(Q)/Q)^r (log R)^r N' / Q`, so the
total is `≫ (N'/M) (M/φ(M))^r / (log R)^r`.
-/

namespace Erdos420

open Filter Finset EuclideanSpace
open scoped PrimeGaps

/-- The mass of the weights: `#V` classes, each of mass at least `(I/2) mainScale`, divided by
`((φ(Q)/Q) log R)^{2k}`, give at least `c N / (log X)^k`. -/
lemma le_card_mul_mainScale_div {k M N N' W' X : ℕ} {cV I α V R : ℝ} (hcV : 0 < cV)
    (hI : 0 < I) (hα : 0 < α) (hM : 1 ≤ M) (hMW : M.Coprime W') (hW' : 0 < W') (hN : 2 ≤ N)
    (hN' : M * (N - 1) ≤ N') (hN'X : N' ≤ X ^ 2) (hX : 2 ≤ X)
    (hR : Real.log R = α * Real.log N') (hR₀ : 0 < Real.log R)
    (hV : cV * W' ≤ V * ((W' : ℝ) / W'.totient) ^ k) :
    cV * I / (4 * (2 * α) ^ k) * N / Real.log X ^ k ≤
      V * (I / 2) * PrimeGaps.mainScale k N' R (M * W') /
        (((M * W').totient : ℝ) / (M * W' : ℕ) * Real.log R) ^ (2 * k) := by
  have hX₁ : (1 : ℝ) < X := by exact_mod_cast hX
  have hlogX : 0 < Real.log X := Real.log_pos hX₁
  have hM₀ : (0 : ℝ) < M := by exact_mod_cast hM
  have hW₀ : (0 : ℝ) < W' := by exact_mod_cast hW'
  have hφM : (0 : ℝ) < M.totient := by exact_mod_cast Nat.totient_pos.mpr hM
  have hφW : (0 : ℝ) < W'.totient := by exact_mod_cast Nat.totient_pos.mpr hW'
  have hφMM : (M.totient : ℝ) ≤ M := by exact_mod_cast Nat.totient_le M
  -- `N' ≥ M (N − 1) ≥ M N / 2`
  have hN'M : (M : ℝ) * N / 2 ≤ N' := by
    have h₁ : M * N = M * (N - 1) + M := by
      rw [← Nat.mul_succ]
      congr 1
      omega
    have h₂ : M ≤ M * (N - 1) := Nat.le_mul_of_pos_right _ (by omega)
    have h : ((M * N : ℕ) : ℝ) ≤ ((2 * N' : ℕ) : ℝ) := by exact_mod_cast (by omega : M * N ≤ 2 * N')
    push_cast at h
    linarith
  have hN'₀ : (0 : ℝ) < N' := by
    have : (0 : ℝ) < M * N / 2 := by positivity
    linarith
  -- `log R = α log N' ≤ 2 α log X`
  have hLk : Real.log R ^ k ≤ (2 * α) ^ k * Real.log X ^ k := by
    have h : Real.log N' ≤ 2 * Real.log X := by
      calc Real.log N' ≤ Real.log ((X : ℝ) ^ 2) :=
            Real.log_le_log hN'₀ (by exact_mod_cast hN'X)
        _ = 2 * Real.log X := by rw [Real.log_pow]; push_cast; ring
    rw [← mul_pow]
    refine pow_le_pow_left₀ hR₀.le ?_ k
    rw [hR]
    nlinarith
  -- the right side is `(I/2) (N' / log^k R) V (M/φ(M))^k (W'/φ(W'))^k / (M W')`
  have hφQ : (((M * W').totient : ℕ) : ℝ) = M.totient * W'.totient := by
    rw [Nat.totient_mul hMW]
    push_cast
    ring
  have hRHS : V * (I / 2) * PrimeGaps.mainScale k N' R (M * W') /
      (((M * W').totient : ℝ) / (M * W' : ℕ) * Real.log R) ^ (2 * k) =
        I / 2 * (N' / Real.log R ^ k) *
          (V * ((M : ℝ) / M.totient) ^ k * ((W' : ℝ) / W'.totient) ^ k / (M * W')) := by
    rw [PrimeGaps.mainScale, hφQ]
    push_cast
    rw [mul_comm 2 k, pow_mul]
    simp only [mul_pow, div_pow, pow_succ]
    -- clear the `k`-th powers as positive variables
    have hAk := pow_pos hφM k
    have hBk := pow_pos hφW k
    have hMk := pow_pos hM₀ k
    have hWk := pow_pos hW₀ k
    have hLk₀ := pow_pos hR₀ k
    generalize (M.totient : ℝ) ^ k = A at hAk ⊢
    generalize (W'.totient : ℝ) ^ k = B at hBk ⊢
    generalize (M : ℝ) ^ k = Mk at hMk ⊢
    generalize (W' : ℝ) ^ k = Wk at hWk ⊢
    generalize Real.log R ^ k = Lk at hLk₀ ⊢
    field_simp
  -- `V (M/φ(M))^k (W'/φ(W'))^k / (M W') ≥ c_V / M`
  have hB : cV / M ≤ V * ((M : ℝ) / M.totient) ^ k * ((W' : ℝ) / W'.totient) ^ k / (M * W') := by
    rw [le_div_iff₀ (by positivity)]
    have h₁ : 1 ≤ ((M : ℝ) / M.totient) ^ k := one_le_pow₀ ((one_le_div hφM).mpr hφMM)
    have h₂ : 0 ≤ V * ((W' : ℝ) / W'.totient) ^ k := (by positivity : 0 ≤ cV * W').trans hV
    calc cV / M * (M * W') = cV * W' := by field_simp
      _ ≤ V * ((W' : ℝ) / W'.totient) ^ k := hV
      _ ≤ V * ((W' : ℝ) / W'.totient) ^ k * ((M : ℝ) / M.totient) ^ k :=
          le_mul_of_one_le_right h₂ h₁
      _ = V * ((M : ℝ) / M.totient) ^ k * ((W' : ℝ) / W'.totient) ^ k := by ring
  have hmid : (M : ℝ) * N / 2 / ((2 * α) ^ k * Real.log X ^ k) ≤ N' / Real.log R ^ k :=
    div_le_div₀ hN'₀.le hN'M (pow_pos hR₀ k) hLk
  rw [hRHS]
  calc cV * I / (4 * (2 * α) ^ k) * N / Real.log X ^ k
      = I / 2 * ((M : ℝ) * N / 2 / ((2 * α) ^ k * Real.log X ^ k)) * (cV / M) := by
        field_simp
        ring
    _ ≤ I / 2 * (N' / Real.log R ^ k) * (cV / M) := by gcongr
    _ ≤ _ := by gcongr

open scoped Classical in
/-- Maynard weights for `a₀ + M t + b_i`, `t ∈ [N, 2N)`, with a prime surplus over
`m − 1`, mass `≫ N / (log X)^r`, little mass on non-rough `t`, and bounded
values on rough `t`, for squarefree `M` with prime factors at most `log X / 2`, so that
`M W'` is a sieve modulus. -/
theorem exists_maynard_weights (m : ℕ) :
    ∃ (r : ℕ) (b : Fin r → ℕ) (γ c : ℝ), Function.Injective b ∧ (∀ i, 0 < b i) ∧
      0 < γ ∧ 0 < c ∧ ∀ η > (0 : ℝ), ∃ ρ > (0 : ℝ), ∃ C : ℝ, ∀ᶠ X : ℕ in atTop,
        ∀ M a₀ N : ℕ, 1 ≤ M → (M : ℝ) ≤ (X : ℝ) ^ (1 / 64 : ℝ) → Squarefree M →
          (∀ p : ℕ, p.Prime → p ∣ M → (p : ℝ) ≤ Real.log X / 2) → a₀ < M →
          X ≤ M * N → M * N ≤ 2 * X → (∀ i, (a₀ + b i).Coprime M) →
          ∃ W : ℕ → ℝ, (∀ t, 0 ≤ W t) ∧
            γ * ∑ t ∈ Ico N (2 * N), W t ≤
              ∑ t ∈ Ico N (2 * N), W t *
                (((univ.filter fun i ↦ (a₀ + M * t + b i).Prime).card : ℝ) - (m - 1)) ∧
            c * N / Real.log X ^ r ≤ ∑ t ∈ Ico N (2 * N), W t ∧
            (∀ t, (∀ i, ∀ p : ℕ, p.Prime → p ∣ a₀ + M * t + b i → (X : ℝ) ^ ρ < p) →
              W t ≤ C) ∧
            ∑ t ∈ (Ico N (2 * N)).filter (fun t ↦ ∃ i, ∃ p : ℕ, p.Prime ∧
                p ∣ a₀ + M * t + b i ∧ (p : ℝ) ≤ (X : ℝ) ^ ρ), W t ≤
              η * ∑ t ∈ Ico N (2 * N), W t := by
  -- the sieve parameters: level `θ`, truncation `R = N^{θ/2 − δ} = N^{1/128}`, modulus size
  -- `Q ≤ N^{ηQ}` and power saving `ϖ`
  set θ : ℝ := 5 / 128 with hθ_def
  set δ : ℝ := 3 / 256 with hδ_def
  set ηQ : ℝ := 5 / 256 with hηQ_def
  set ϖ : ℝ := 3 / 64 with hϖ_def
  set α : ℝ := θ / 2 - δ with hα_def
  have hθ0 : 0 < θ := by norm_num [hθ_def]
  have hθ : θ < 1 / 2 := by norm_num [hθ_def]
  have hδ : 0 < δ := by norm_num [hδ_def]
  have hδθ : δ < θ / 2 := by norm_num [hδ_def, hθ_def]
  have hηQ : ηQ < 2 * δ := by norm_num [hηQ_def, hδ_def]
  have hηQ' : ηQ > 1 / 64 := by norm_num [hηQ_def]
  have hϖ : θ < ϖ := by norm_num [hθ_def, hϖ_def]
  have hα : α = 1 / 128 := by norm_num [hα_def, hθ_def, hδ_def]
  have hα₀ : 0 < α := by rw [hα]; norm_num
  have hPNT := primeCountingEstimate
  have hPS : Nat.HasPowerSavingLevel θ ϖ :=
    hasPowerSavingLevel (by norm_num [hθ_def]) (by norm_num [hϖ_def])
  -- a dimension `k ≥ 2` with `α (M_k − 1) ≥ m + 1`, and the admissible tuple `(i + 1) k!`
  obtain ⟨k, hk, hMk⟩ := ((eventually_ge_atTop 2).and
    (tendsto_M_atTop.eventually_ge_atTop (128 * ((m : ℝ) + 1) + 1))).exists
  set b : Fin k → ℕ := fun i ↦ (i.val + 1) * k.factorial with hb_def
  have hadm : GPYSieveS1.IsAdmissible b := isAdmissible_factorialTuple k
  have hb₀ : ∀ i, 0 < b i := fun i ↦ Nat.mul_pos (Nat.succ_pos _) (Nat.factorial_pos k)
  -- a smooth witness `F` with `(M_k − 1) ‖F‖² < ∑ J_m(F)`
  obtain ⟨-, hwit⟩ := PrimeGaps.M_pos_and_le_and_exists_smooth_lt_sum_J k hk
  obtain ⟨F, hF, htsupp, hmem, hJ, hI⟩ := hwit 1 one_pos
  have hsupp : Function.support F ⊆ 𝓡 k := (subset_tsupport F).trans htsupp
  set I := ‖(PrimeGaps.MainProp.canonMemLp F hF hsupp).toLp F‖ ^ 2 with hI_def
  set JJ := ∑ i, PrimeGaps.J i ((PrimeGaps.MainProp.canonMemLp F hF hsupp).toLp F) with hJJ_def
  have hI₀ : 0 < I := hI
  have hwit' : ((m : ℝ) + 1) * I < (θ / 2 - δ) * JJ := by
    have h₁ : (PrimeGaps.M k - 1) * I < JJ := hJ
    have h₂ : (m : ℝ) + 1 ≤ α * (PrimeGaps.M k - 1) := by rw [hα]; linarith
    calc ((m : ℝ) + 1) * I ≤ α * (PrimeGaps.M k - 1) * I := by gcongr
      _ = α * ((PrimeGaps.M k - 1) * I) := by ring
      _ < α * JJ := by gcongr
  -- the sieve inputs: the modulus, the number of classes, the `S₁` asymptotic, the positivity
  -- of `S₂ − (m + 1) S₁`, and the sharp bound for `λ`
  obtain ⟨CQ, hCQ⟩ := exists_modulusHyp
  obtain ⟨cV, hcV, hV⟩ := exists_le_card_validClasses b hadm.2
  obtain ⟨e₁, _e₂, he₁, _he₂, N₁, hmain⟩ := PrimeGaps.MainProp.prop_main_prop hPNT hk b hadm F hF
    hsupp θ δ hθ0 hθ hδ hδθ CQ ηQ ϖ hηQ hPS hϖ
  obtain ⟨N₂, hpos⟩ := PrimeGaps.MainProp.lem_S_positive hPNT hk b hadm F hF hsupp θ δ hθ0 hθ
    hδ hδθ CQ ηQ ϖ hηQ hPS hϖ ((m : ℝ) + 1) (by positivity) hwit'
  obtain ⟨Cl, N₃, hl⟩ := exists_abs_l₀_le hk F hF hsupp θ δ hδθ CQ ηQ
  obtain ⟨N₅, hN₅⟩ := eventually_atTop.mp (he₁.eventually (ge_mem_nhds (half_pos hI₀)))
  refine ⟨k, b, 2, cV * I / (4 * (2 * α) ^ k), fun i j hij ↦ ?_, hb₀, two_pos, by positivity,
    fun η hη ↦ ?_⟩
  · have h := Nat.eq_of_mul_eq_mul_right (Nat.factorial_pos k) hij
    exact Fin.ext (by omega)
  -- the roughness exponent `ρ_L` at scale `N'`, and `ρ = ρ_L / 2` at scale `X`
  obtain ⟨ρL, hρL, N₄, hrough⟩ := exists_sum_weight_nonrough_le hk b hadm F hF hsupp θ δ
    hθ0 hθ hδ hδθ CQ ηQ hηQ (η * I / 2) (by positivity)
  set T : ℝ := 2 ^ (2 / (ρL / 2)) with hT_def
  refine ⟨ρL / 2, by positivity, (T ^ k * Cl) ^ 2, ?_⟩
  have hX₀ : Tendsto (fun X : ℕ ↦ (X : ℝ) / 2) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_div_const two_pos
  filter_upwards [hCQ ηQ hηQ', hX₀.eventually_ge_atTop (max (max (max N₁ N₂) (max N₃ N₄)) N₅),
    eventually_ge_atTop (16 + k * k.factorial)] with X hXQ hXN hX
  intro M a₀ N hM₁ hMX hMsq hMp ha₀ hMN₁ hMN₂ hcop
  simp only [max_le_iff] at hXN
  obtain ⟨⟨⟨hXN₁, hXN₂⟩, hXN₃, hXN₄⟩, hXN₅⟩ := hXN
  -- `√X ≤ X / 2`, so `M ≤ X^{1/64} ≤ X / 2`
  have hX₁ : (16 : ℝ) ≤ X := by exact_mod_cast (by omega : 16 ≤ X)
  have hX₀' : (0 : ℝ) < X := by linarith
  set s := (X : ℝ) ^ (1 / 2 : ℝ) with hs_def
  have hss : s * s = X := by rw [hs_def, ← Real.rpow_add hX₀']; norm_num
  have hs₄ : 4 ≤ s := by
    have h : Real.sqrt 16 ≤ Real.sqrt X := Real.sqrt_le_sqrt hX₁
    rwa [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num), Real.sqrt_eq_rpow] at h
  have hsX : s ≤ X / 2 := by nlinarith
  have hMX₂ : (M : ℝ) ≤ X / 2 :=
    hMX.trans ((Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)).trans hsX)
  have h2M : 2 * M ≤ X := by
    have h : ((2 * M : ℕ) : ℝ) ≤ X := by push_cast; linarith
    exact_mod_cast h
  have hN₂ : 2 ≤ N := by
    by_contra h
    have : M * N ≤ M * 1 := Nat.mul_le_mul_left M (by omega)
    omega
  -- the sieve scale `N' = a₀ + M (N − 1) ∈ [X/2, 2X]`
  set N' := a₀ + M * (N - 1) with hN'_def
  have hMN : M * N = M * (N - 1) + M := by
    rw [← Nat.mul_succ]
    congr 1
    omega
  have hN'MN : N' ≤ M * N := by omega
  have hN'X : N' ≤ 2 * X := hN'MN.trans hMN₂
  have hXN' : X ≤ 2 * N' := by omega
  have hN'lo : (X : ℝ) / 2 ≤ N' := by
    have h : (X : ℝ) ≤ 2 * N' := by exact_mod_cast hXN'
    linarith
  have hN'hi : (N' : ℝ) ≤ 2 * X := by exact_mod_cast hN'X
  have hN'₁ : (1 : ℝ) < N' := by linarith
  have hN'₀ : (0 : ℝ) < N' := by linarith
  have hsN' : s ≤ N' := hsX.trans hN'lo
  -- the modulus `Q = M W'` and the sieve weights at scale `N'`
  set W' := sieveCofactor M N' with hW'_def
  set Q := M * W' with hQ_def
  have hQ : PrimeGaps.ModulusHyp CQ ηQ N' Q := hXQ M N' hMsq hMX hMp hN'lo hN'hi
  have hQ₀ : (0 : ℝ) < Q := by exact_mod_cast hQ.pos
  set R := PrimeGaps.sieveTruncation N' δ θ with hR_def
  have hlogR : Real.log R = α * Real.log N' := by
    rw [hR_def, PrimeGaps.sieveTruncation, Real.log_rpow hN'₀]
  have hlogR₀ : 0 < Real.log R := by
    rw [hlogR]
    exact mul_pos hα₀ (Real.log_pos hN'₁)
  set l := PrimeGaps.l₀ R Q (fun x ↦ F (WithLp.toLp 2 x.ofLp)) with hl_def
  set base := (Q.totient : ℝ) / Q * Real.log R with hbase_def
  have hbase : 0 < base := mul_pos (div_pos hQ.totient_pos hQ₀) hlogR₀
  set nrm := base ^ (2 * k) with hnrm_def
  have hnrm : 0 < nrm := pow_pos hbase _
  set mS := PrimeGaps.mainScale k N' R Q with hmS_def
  have hmS : 0 < mS := by
    rw [hmS_def, PrimeGaps.mainScale]
    have := hQ.totient_pos
    positivity
  set V := validClasses Q M a₀ b with hV_def
  -- every valid class is a sieve class, with `S₁ ≥ (I / 2) mainScale` and `S₂ > (m + 1) S₁`
  have hval : ∀ v ∈ V, ∀ i, (((v : ZMod Q).val : ℤ) + b i).gcd Q = 1 :=
    fun v hv ↦ gcd_eq_one_of_mem_validClasses hv
  have hS₁ : ∀ v ∈ V, I / 2 * mS ≤ PrimeGaps.S₁ b l N' (v : ZMod Q) := by
    intro v hv
    have h := (hmain N' (by linarith) Q hQ (v : ZMod Q) (hval v hv)).1
    have he : e₁ N' ≤ I / 2 := hN₅ N' (by exact_mod_cast (by linarith : (N₅ : ℝ) ≤ N'))
    have h₂ := (abs_le.mp h).1
    have h₃ := mul_le_mul_of_nonneg_right he hmS.le
    linarith only [h₂, h₃]
  have hS₂ : ∀ v ∈ V, 0 < PrimeGaps.S₂ b l N' (v : ZMod Q) -
      ((m : ℝ) + 1) * PrimeGaps.S₁ b l N' (v : ZMod Q) :=
    fun v hv ↦ hpos N' (by linarith) Q hQ (v : ZMod Q) (hval v hv)
  -- the weights: Maynard's `w(a₀ + M t)` on the valid classes, normalized by `nrm`
  set cond : ℕ → Prop := fun t ↦ N' < a₀ + M * t ∧ a₀ + M * t ≤ 2 * N' ∧
    ∀ i, (a₀ + M * t + b i).Coprime Q with hcond
  set W : ℕ → ℝ := fun t ↦ if cond t then PrimeGaps.weight b l (a₀ + M * t) / nrm else 0
    with hW_def
  have hreg : ∀ f : ℕ → ℝ, ∑ t ∈ Ico N (2 * N), (if cond t then f (a₀ + M * t) else 0) =
      ∑ v ∈ V, ∑ n ∈ Ioc N' (2 * N') with ((n : ℕ) : ZMod Q) = v, f n := fun f ↦ by
    rw [← sum_Ico_eq_sum_validClasses b (dvd_mul_right M W') (by exact_mod_cast hQ.pos) ha₀
      (by omega) rfl f]
  have hsum₁ : ∑ t ∈ Ico N (2 * N), W t = ∑ v ∈ V, PrimeGaps.S₁ b l N' (v : ZMod Q) / nrm :=
    calc ∑ t ∈ Ico N (2 * N), W t
        = ∑ v ∈ V, ∑ n ∈ Ioc N' (2 * N') with ((n : ℕ) : ZMod Q) = v,
            PrimeGaps.weight b l n / nrm := hreg fun n ↦ PrimeGaps.weight b l n / nrm
      _ = _ := sum_congr rfl fun v _ ↦ by rw [PrimeGaps.S₁, sum_div]
  have hW₀ : ∀ t, 0 ≤ W t := fun t ↦ by
    simp only [hW_def]
    split_ifs
    exacts [div_nonneg PrimeGaps.w_nonneg hnrm.le, le_rfl]
  refine ⟨W, hW₀, ?_, ?_, ?_, ?_⟩
  · -- the prime surplus: `∑ W #primes ≥ (m + 1) ∑ W`
    have hsum₂ : ∑ t ∈ Ico N (2 * N), W t *
        ((univ.filter fun i ↦ (a₀ + M * t + b i).Prime).card : ℝ) =
          ∑ v ∈ V, PrimeGaps.S₂ b l N' (v : ZMod Q) / nrm :=
      calc _ = ∑ t ∈ Ico N (2 * N), (if cond t then (fun n ↦
            (#{i | (n + b i).Prime} : ℝ) * PrimeGaps.weight b l n / nrm) (a₀ + M * t) else 0) :=
            sum_congr rfl fun t _ ↦ by
              simp only [hW_def]
              split_ifs
              · ring
              · ring
        _ = _ := hreg fun n ↦ (#{i | (n + b i).Prime} : ℝ) * PrimeGaps.weight b l n / nrm
        _ = _ := sum_congr rfl fun v _ ↦ by rw [PrimeGaps.S₂, sum_div]
    have hle : ((m : ℝ) + 1) * ∑ v ∈ V, PrimeGaps.S₁ b l N' (v : ZMod Q) / nrm ≤
        ∑ v ∈ V, PrimeGaps.S₂ b l N' (v : ZMod Q) / nrm := by
      rw [mul_sum]
      refine sum_le_sum fun v hv ↦ ?_
      rw [mul_div_assoc']
      exact div_le_div_of_nonneg_right (by linarith [hS₂ v hv]) hnrm.le
    have hsplit : ∑ t ∈ Ico N (2 * N), W t *
        (((univ.filter fun i ↦ (a₀ + M * t + b i).Prime).card : ℝ) - (m - 1)) =
          ∑ t ∈ Ico N (2 * N), W t *
            ((univ.filter fun i ↦ (a₀ + M * t + b i).Prime).card : ℝ) -
            (m - 1) * ∑ t ∈ Ico N (2 * N), W t := by
      rw [mul_sum, ← sum_sub_distrib]
      exact sum_congr rfl fun t _ ↦ by ring
    rw [hsplit, hsum₂]
    rw [← hsum₁] at hle
    linarith
  · -- the mass
    have hcard := hV M a₀ W' (by omega) (coprime_sieveCofactor M N')
      (squarefree_sieveCofactor M N') ha₀ hcop
    have hS₁sum : (#V : ℝ) * (I / 2) * mS / nrm ≤
        ∑ v ∈ V, PrimeGaps.S₁ b l N' (v : ZMod Q) / nrm := by
      rw [← sum_div]
      refine div_le_div_of_nonneg_right ?_ hnrm.le
      calc (#V : ℝ) * (I / 2) * mS = ∑ v ∈ V, I / 2 * mS := by
            rw [sum_const, nsmul_eq_mul]
            ring
        _ ≤ _ := sum_le_sum hS₁
    have hX2 : N' ≤ X ^ 2 := by
      have : X * 2 ≤ X * X := Nat.mul_le_mul_left X (by omega)
      rw [sq]
      omega
    rw [hsum₁]
    exact (le_card_mul_mainScale_div hcV hI₀ hα₀ hM₁ (coprime_sieveCofactor M N')
      (squarefree_sieveCofactor M N').ne_zero.bot_lt hN₂ (by omega) hX2 (by omega) hlogR
      hlogR₀ hcard).trans hS₁sum
  · -- the pointwise bound on rough `t`
    intro t ht
    simp only [hW_def]
    split_ifs with hc
    · have hl' : ∀ d, |l d| ≤ Cl * base ^ k := hl N' (by linarith) Q hQ
      have hT : ∀ i, (#(a₀ + M * t + b i).divisors : ℝ) ≤ T := by
        intro i
        refine card_divisors_le_of_rough (by positivity) (by omega)
          (by have := hb₀ i; omega) ?_ (ht i)
        have hbi : b i ≤ k * k.factorial := Nat.mul_le_mul_right _ i.isLt
        have hXX : X * (16 + k * k.factorial) ≤ X * X := Nat.mul_le_mul_left X hX
        have h₂ := hc.2.1
        have hkX : k * k.factorial ≤ X * (k * k.factorial) := Nat.le_mul_of_pos_left _ (by omega)
        rw [Nat.mul_add] at hXX
        rw [sq]
        omega
      have hw := weight_le_of_abs_le b l (a₀ + M * t) hl' hT
      have heq : (T ^ k * (Cl * base ^ k)) ^ 2 = (T ^ k * Cl) ^ 2 * nrm := by
        rw [hnrm_def]
        ring
      calc PrimeGaps.weight b l (a₀ + M * t) / nrm ≤ (T ^ k * (Cl * base ^ k)) ^ 2 / nrm :=
            div_le_div_of_nonneg_right hw hnrm.le
        _ = (T ^ k * Cl) ^ 2 := by rw [heq, mul_div_assoc, div_self hnrm.ne', mul_one]
    · exact sq_nonneg _
  · -- the non-rough `t` carry at most `η ∑ W`
    have hXρ : (X : ℝ) ^ (ρL / 2) ≤ (N' : ℝ) ^ ρL := by
      rw [show ρL / 2 = 1 / 2 * ρL by ring, Real.rpow_mul hX₀'.le]
      exact Real.rpow_le_rpow (by positivity) hsN' hρL.le
    obtain ⟨g, hg_def⟩ : ∃ g : ℕ → ℝ, g = fun n ↦ if (∃ i, ∃ p : ℕ, p.Prime ∧ p ∣ n + b i ∧
        (p : ℝ) ≤ (N' : ℝ) ^ ρL) then PrimeGaps.weight b l n / nrm else 0 := ⟨_, rfl⟩
    have hg₀ : ∀ n, 0 ≤ g n := fun n ↦ by
      simp only [hg_def]
      split_ifs
      exacts [div_nonneg PrimeGaps.w_nonneg hnrm.le, le_rfl]
    have hle : ∀ t ∈ Ico N (2 * N), (if (∃ i, ∃ p : ℕ, p.Prime ∧
        p ∣ a₀ + M * t + b i ∧ (p : ℝ) ≤ (X : ℝ) ^ (ρL / 2)) then W t else 0) ≤
          if cond t then g (a₀ + M * t) else 0 := by
      intro t _
      split_ifs with hP hc hc
      · simp only [hW_def, hg_def, ite_eq_left hc]
        rw [ite_eq_left]
        obtain ⟨i, p, hp, hpd, hpX⟩ := hP
        exact ⟨i, p, hp, hpd, hpX.trans hXρ⟩
      · simp only [hW_def, ite_eq_right hc, le_refl]
      · exact hg₀ _
      · exact le_rfl
    calc ∑ t ∈ (Ico N (2 * N)).filter (fun t ↦ ∃ i, ∃ p : ℕ, p.Prime ∧
            p ∣ a₀ + M * t + b i ∧ (p : ℝ) ≤ (X : ℝ) ^ (ρL / 2)), W t
        ≤ ∑ t ∈ Ico N (2 * N), (if cond t then g (a₀ + M * t) else 0) := by
          rw [sum_filter]
          exact sum_le_sum hle
      _ = ∑ v ∈ V, ∑ n ∈ Ioc N' (2 * N') with ((n : ℕ) : ZMod Q) = v, g n := hreg g
      _ ≤ ∑ v ∈ V, η * (PrimeGaps.S₁ b l N' (v : ZMod Q) / nrm) := by
          refine sum_le_sum fun v hv ↦ ?_
          have h := hrough N' (hXN₄.trans hN'lo) Q hQ (v : ZMod Q) (hval v hv)
          have hgv : ∑ n ∈ Ioc N' (2 * N') with ((n : ℕ) : ZMod Q) = v, g n =
              (∑ n ∈ Ioc N' (2 * N') with ((n : ℕ) : ZMod Q) = v ∧
                ∃ i, ∃ p : ℕ, p.Prime ∧ p ∣ n + b i ∧ (p : ℝ) ≤ (N' : ℝ) ^ ρL,
                  PrimeGaps.weight b l n) / nrm := by
            rw [hg_def, ← sum_filter, filter_filter, sum_div]
          have hηS := mul_le_mul_of_nonneg_left (hS₁ v hv) hη.le
          rw [hgv, mul_div_assoc']
          refine div_le_div_of_nonneg_right ?_ hnrm.le
          linarith only [h, hηS]
      _ = η * ∑ t ∈ Ico N (2 * N), W t := by rw [hsum₁, mul_sum]

end Erdos420
