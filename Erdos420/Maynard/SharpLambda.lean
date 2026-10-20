import PrimeGapsTheory.Endgame.MainProp

/-!
# The sharp bound for Maynard's `λ`

With `y_r` supported on squarefree `r` coprime to `Q` with `∏ rᵢ ≤ R`,

  `|λ_d| ≤ y_max ∏ᵢ dᵢ ∑_{rᵢ ≤ R, dᵢ ∣ rᵢ, (rᵢ, Q) = 1} μ²(rᵢ) / φ(rᵢ)`.

Writing `rᵢ = dᵢ sᵢ` with `(sᵢ, Q dᵢ) = 1` and `m = Q dᵢ`, each factor is
`(φ(Q)/Q) (m/φ(m)) ∑_{s ≤ R/dᵢ, (s, m) = 1} μ²(s)/φ(s)`. Since
`m / φ(m) = ∑_{e ∣ m} μ²(e)/φ(e)` and the products `e s` are distinct squarefree numbers at most
`m R / dᵢ = Q R`, this is at most `(φ(Q)/Q) ∑_{t ≤ Q R} μ²(t)/φ(t) ≤ e⁴ (φ(Q)/Q) log (Q R)`, and
`log Q ≤ η log N ≪ log R`. The library's `lambdaMax_bound` gives only `|λ_d| ≪ (log N)^k`,
which loses `(Q / φ(Q))^k` against the mass `∑ w ≍ (φ(Q)/Q)^k (log R)^k N / Q`.
-/

namespace Erdos420

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius PrimeGaps

/-- `∑_{t ≤ z} μ²(t)/φ(t) ≤ e⁴ log z`. -/
lemma sum_squarefree_inv_totient_le {z : ℕ} (hz : 2 ≤ z) :
    ∑ t ∈ Icc 1 z with Squarefree t, (1 / t.totient : ℝ) ≤ Real.exp 4 * Real.log z := by
  have h := ArithmeticFunction.sum_moebius_sq_mul_tau_div_totient_le 1 hz
  norm_num at h
  refine le_trans ?_ h
  calc ∑ t ∈ Icc 1 z with Squarefree t, (1 / t.totient : ℝ)
      = ∑ t ∈ Icc 1 z, (if t = 0 then 0 else (μ t : ℝ) ^ 2) / t.totient := by
        rw [sum_filter]
        refine sum_congr rfl fun t ht ↦ ?_
        rw [mem_Icc] at ht
        split_ifs with hsq h0
        · omega
        · rw [← Int.cast_pow, moebius_sq_eq_one_of_squarefree hsq, Int.cast_one]
        · omega
        · rw [moebius_eq_zero_of_not_squarefree hsq]
          simp
    _ ≤ ∑ t ∈ range (z + 1), (if t = 0 then 0 else (μ t : ℝ) ^ 2) / t.totient :=
        sum_le_sum_of_subset_of_nonneg (fun t ht ↦ by simp only [mem_Icc, mem_range] at ht ⊢; omega)
          fun t _ _ ↦ by positivity

/-- `(m / φ(m)) ∑_{s ≤ x, (s, m) = 1} μ²(s)/φ(s) ≤ ∑_{t ≤ m x} μ²(t)/φ(t)`: writing
`m / φ(m) = ∑_{e ∣ m} μ²(e)/φ(e)`, the products `e s` are distinct squarefree numbers at most
`m x`, since `e = (e s, m)`. -/
lemma div_totient_mul_sum_coprime_le {m : ℕ} (hm : m ≠ 0) (x : ℕ) :
    (m / m.totient : ℝ) * ∑ s ∈ Icc 1 x with Squarefree s ∧ s.Coprime m, (1 / s.totient : ℝ) ≤
      ∑ t ∈ Icc 1 (m * x) with Squarefree t, (1 / t.totient : ℝ) := by
  set S := {s ∈ Icc 1 x | Squarefree s ∧ s.Coprime m}
  set D := {e ∈ m.divisors | Squarefree e}
  have hmem {e s : ℕ} (he : e ∈ D) (hs : s ∈ S) :
      e ∣ m ∧ Squarefree e ∧ 1 ≤ s ∧ s ≤ x ∧ Squarefree s ∧ s.Coprime m := by
    simp only [D, S, mem_filter, Nat.mem_divisors, mem_Icc] at he hs
    exact ⟨he.1.1, he.2, hs.1.1, hs.1.2, hs.2⟩
  have hcop {e s : ℕ} (he : e ∈ D) (hs : s ∈ S) : e.Coprime s :=
    Nat.Coprime.coprime_dvd_left (hmem he hs).1 (hmem he hs).2.2.2.2.2.symm
  calc (m / m.totient : ℝ) * ∑ s ∈ S, (1 / s.totient : ℝ)
      = ∑ p ∈ D ×ˢ S, (1 / (p.1 * p.2).totient : ℝ) := by
        rw [← ArithmeticFunction.sum_moebius_sq_div_totient, sum_mul_sum, ← sum_product',
          ← sum_filter_add_sum_filter_not _ (fun p : ℕ × ℕ ↦ Squarefree p.1)]
        rw [sum_eq_zero (s := {p ∈ m.divisors ×ˢ S | ¬Squarefree p.1}) fun p hp ↦ by
          rw [mem_filter] at hp
          rw [moebius_eq_zero_of_not_squarefree hp.2]
          simp, add_zero]
        refine sum_congr ?_ fun p hp ↦ ?_
        · ext p
          simp only [D, mem_filter, mem_product]
          tauto
        rw [mem_product] at hp
        rw [← Int.cast_pow, moebius_sq_eq_one_of_squarefree (hmem hp.1 hp.2).2.1, Int.cast_one,
          Nat.totient_mul (hcop hp.1 hp.2), Nat.cast_mul]
        field_simp
    _ = ∑ t ∈ (D ×ˢ S).image (fun p ↦ p.1 * p.2), (1 / t.totient : ℝ) := by
        refine (sum_image (f := fun t : ℕ ↦ (1 / t.totient : ℝ)) fun p hp q hq hpq ↦ ?_).symm
        rw [mem_coe, mem_product] at hp hq
        have hgcd {e s : ℕ} (he : e ∈ D) (hs : s ∈ S) : (e * s).gcd m = e := by
          rw [Nat.Coprime.gcd_mul_right_cancel e (hmem he hs).2.2.2.2.2,
            Nat.gcd_eq_left (hmem he hs).1]
        have h₁ : p.1 = q.1 := by
          rw [← hgcd hp.1 hp.2, ← hgcd hq.1 hq.2]
          exact congrArg (·.gcd m) hpq
        have h₂ : p.2 = q.2 := by
          have hp0 : p.1 ≠ 0 := (hmem hp.1 hp.2).2.1.ne_zero
          rw [h₁] at hpq hp0
          exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hp0) hpq
        exact Prod.ext h₁ h₂
    _ ≤ ∑ t ∈ Icc 1 (m * x) with Squarefree t, (1 / t.totient : ℝ) := by
        refine sum_le_sum_of_subset_of_nonneg (fun t ht ↦ ?_) fun t _ _ ↦ by positivity
        obtain ⟨⟨e, s⟩, hp, rfl⟩ := mem_image.mp ht
        rw [mem_product] at hp
        obtain ⟨hem, he, hs1, hsx, hs, -⟩ := hmem hp.1 hp.2
        have he1 : 1 ≤ e := Nat.pos_of_ne_zero he.ne_zero
        rw [mem_filter, mem_Icc, Nat.squarefree_mul_iff]
        exact ⟨⟨Nat.one_le_iff_ne_zero.mpr (by positivity),
          Nat.mul_le_mul (Nat.le_of_dvd (Nat.pos_of_ne_zero hm) hem) hsx⟩,
          hcop hp.1 hp.2, he, hs⟩

/-- `d ∑_{r ≤ R, d ∣ r, (r, W) = 1} μ²(r)/φ(r) ≤ (φ(W)/W) ∑_{t ≤ W R} μ²(t)/φ(t)`: with
`r = d s`, the left side is `(φ(W)/W) (m/φ(m)) ∑_{s ≤ R/d, (s, m) = 1} μ²(s)/φ(s)` for
`m = W d`. -/
lemma mul_sum_dvd_coprime_le {W : ℕ} (hW : W ≠ 0) (d R : ℕ) :
    d * ∑ r ∈ Icc 1 R with Squarefree r ∧ d ∣ r ∧ r.Coprime W, (1 / r.totient : ℝ) ≤
      W.totient / W * ∑ t ∈ Icc 1 (W * R) with Squarefree t, (1 / t.totient : ℝ) := by
  set T := {r ∈ Icc 1 R | Squarefree r ∧ d ∣ r ∧ r.Coprime W}
  have hrhs : 0 ≤ (W.totient / W : ℝ) * ∑ t ∈ Icc 1 (W * R) with Squarefree t,
      (1 / t.totient : ℝ) := by positivity
  obtain hT | ⟨r₀, hr₀⟩ := T.eq_empty_or_nonempty
  · simpa [hT] using hrhs
  simp only [T, mem_filter, mem_Icc] at hr₀
  have hd : Squarefree d := hr₀.2.1.squarefree_of_dvd hr₀.2.2.1
  have hd0 : d ≠ 0 := hd.ne_zero
  have hdW : d.Coprime W := hr₀.2.2.2.coprime_dvd_left hr₀.2.2.1
  set S := {s ∈ Icc 1 (R / d) | Squarefree s ∧ s.Coprime (W * d)}
  have h₁ : T ⊆ S.image (d * ·) := fun r hr ↦ by
    simp only [T, S, mem_filter, mem_Icc, mem_image] at hr ⊢
    obtain ⟨⟨hr1, hrR⟩, hr, hdr, hrW⟩ := hr
    have hds := Nat.mul_div_cancel' hdr
    have hsr : r / d ∣ r := Nat.div_dvd_of_dvd hdr
    refine ⟨r / d, ⟨⟨Nat.div_pos (Nat.le_of_dvd hr1 hdr) (Nat.pos_of_ne_zero hd0),
      Nat.div_le_div_right hrR⟩, hr.squarefree_of_dvd hsr, ?_⟩, hds⟩
    refine Nat.Coprime.mul_right (hrW.coprime_dvd_left hsr) ?_
    exact (Nat.coprime_of_squarefree_mul (hds ▸ hr :)).symm
  have hcop {s : ℕ} (hs : s ∈ S) : d.Coprime s := by
    simp only [S, mem_filter] at hs
    exact (Nat.Coprime.coprime_mul_left_right hs.2.2).symm
  have hm : W * d ≠ 0 := mul_ne_zero hW hd0
  have h₂ := div_totient_mul_sum_coprime_le hm (R / d)
  have h₃ : ∑ t ∈ Icc 1 (W * d * (R / d)) with Squarefree t, (1 / t.totient : ℝ) ≤
      ∑ t ∈ Icc 1 (W * R) with Squarefree t, (1 / t.totient : ℝ) := by
    refine sum_le_sum_of_subset_of_nonneg (fun t ht ↦ ?_) fun t _ _ ↦ by positivity
    simp only [mem_filter, mem_Icc] at ht ⊢
    refine ⟨⟨ht.1.1, ht.1.2.trans ?_⟩, ht.2⟩
    rw [mul_assoc]
    exact Nat.mul_le_mul_left W (Nat.mul_div_le R d)
  have hφd : (0 : ℝ) < d.totient := by exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero hd0)
  have hφW : (0 : ℝ) < W.totient := by exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero hW)
  have hW0 : (0 : ℝ) < W := by exact_mod_cast Nat.pos_of_ne_zero hW
  calc d * ∑ r ∈ T, (1 / r.totient : ℝ)
      ≤ d * ∑ s ∈ S, (1 / (d * s).totient : ℝ) := by
        grw [sum_le_sum_of_subset_of_nonneg h₁ fun _ _ _ ↦ by positivity,
          sum_image fun _ _ _ _ h ↦ Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hd0) h]
    _ = W.totient / W * ((W * d : ℕ) / (W * d).totient * ∑ s ∈ S, (1 / s.totient : ℝ)) := by
        rw [Nat.totient_mul (hdW.symm), mul_sum, mul_sum, mul_sum]
        refine sum_congr rfl fun s hs ↦ ?_
        rw [Nat.totient_mul (hcop hs)]
        push_cast
        field_simp
    _ ≤ W.totient / W * ∑ t ∈ Icc 1 (W * R) with Squarefree t, (1 / t.totient : ℝ) := by
        gcongr
        exact h₂.trans h₃

/-- **Sharp bound for `λ` from `y`.** If `y` is supported on squarefree tuples coprime to `W` with
product at most `R`, then `|λ_d| ≤ y_max (e⁴ (φ(W)/W) log (W R))^k`. -/
theorem abs_yToL_le {k R W : ℕ} {y : (Fin k → ℕ) →₀ ℝ} (hy : y.HasPermissibleSupport R W)
    (hW : W ≠ 0) (hR : 2 ≤ R) (d : Fin k → ℕ) :
    |PrimeGaps.yToL y d| ≤
      y.maxRealAbs * (W.totient / W * (Real.exp 4 * Real.log (W * R))) ^ k := by
  classical
  set T : ℕ → Finset ℕ := fun e ↦ {r ∈ Icc 1 R | Squarefree r ∧ e ∣ r ∧ r.Coprime W}
  have hWR : 2 ≤ W * R := hR.trans (Nat.le_mul_of_pos_left R (Nat.pos_of_ne_zero hW))
  have h₁ : {r ∈ permissibleSupport k R W | ∀ i, d i ∣ r i} ⊆
      Fintype.piFinset fun i ↦ T (d i) := fun r hr ↦ by
    rw [mem_filter, mem_permissibleSupport_iff'] at hr
    obtain ⟨⟨hr0, hrR, hrW, hr⟩, hdr⟩ := hr
    rw [Fintype.mem_piFinset]
    intro i
    have hri : r i ∣ ∏ j, r j := dvd_prod_of_mem _ (mem_univ i)
    simp only [T, mem_filter, mem_Icc]
    exact ⟨⟨Nat.pos_of_ne_zero (hr0 i),
      (Nat.le_of_dvd (Nat.pos_of_ne_zero hr.ne_zero) hri).trans hrR⟩,
      hr.squarefree_of_dvd hri, hdr i, hrW.coprime_dvd_left hri⟩
  have h₂ : ∀ i, (d i : ℝ) * ∑ r ∈ T (d i), (1 / r.totient : ℝ) ≤
      W.totient / W * (Real.exp 4 * Real.log (W * R)) := fun i ↦ by
    grw [mul_sum_dvd_coprime_le hW (d i) R, sum_squarefree_inv_totient_le hWR, Nat.cast_mul]
  rw [PrimeGaps.yToL_apply hy, Finsupp.sum_of_support_subset y hy _ (by simp)]
  have hM := y.maxRealAbs_nonneg
  have hA : |((∏ i, μ (d i) * (d i : ℤ) : ℤ) : ℝ)| ≤ ∏ i, (d i : ℝ) := by
    rw [← Int.cast_abs, abs_prod]
    push_cast
    refine prod_le_prod₀ (fun _ _ ↦ abs_nonneg _) fun i _ ↦ ?_
    rw [abs_mul, Nat.abs_cast]
    refine mul_le_of_le_one_left (Nat.cast_nonneg _) ?_
    exact_mod_cast abs_moebius_le_one
  have hS : |∑ r ∈ permissibleSupport k R W,
      if ∀ i, d i ∣ r i then y r / ((∏ i, (r i).totient : ℕ) : ℝ) else 0| ≤
      y.maxRealAbs * ∏ i, ∑ r ∈ T (d i), (1 / r.totient : ℝ) := by
    grw [abs_sum_le_sum_abs]
    calc ∑ r ∈ permissibleSupport k R W,
          |if ∀ i, d i ∣ r i then y r / ((∏ i, (r i).totient : ℕ) : ℝ) else 0|
        ≤ ∑ r ∈ permissibleSupport k R W,
          if ∀ i, d i ∣ r i then y.maxRealAbs * ∏ i, (1 / (r i).totient : ℝ) else 0 := by
          refine sum_le_sum fun r _ ↦ ?_
          split_ifs
          · rw [abs_div, Nat.abs_cast, Nat.cast_prod, div_eq_mul_inv, ← prod_inv_distrib]
            simp_rw [one_div]
            gcongr
            exact y.le_maxRealAbs
          · simp
      _ = y.maxRealAbs * ∑ r ∈ permissibleSupport k R W with ∀ i, d i ∣ r i,
          ∏ i, (1 / (r i).totient : ℝ) := by
          rw [sum_filter, mul_sum]
          exact sum_congr rfl fun r _ ↦ by split_ifs <;> simp
      _ ≤ y.maxRealAbs * ∑ r ∈ Fintype.piFinset fun i ↦ T (d i), ∏ i, (1 / (r i).totient : ℝ) := by
          grw [sum_le_sum_of_subset_of_nonneg h₁ fun _ _ _ ↦ by positivity]
      _ = y.maxRealAbs * ∏ i, ∑ r ∈ T (d i), (1 / r.totient : ℝ) := by
          rw [prod_univ_sum]
  rw [abs_mul]
  grw [hA, hS]
  calc (∏ i, (d i : ℝ)) * (y.maxRealAbs * ∏ i, ∑ r ∈ T (d i), (1 / r.totient : ℝ))
      = y.maxRealAbs * ∏ i, ((d i : ℝ) * ∑ r ∈ T (d i), (1 / r.totient : ℝ)) := by
        rw [prod_mul_distrib]
        ring
    _ ≤ y.maxRealAbs * ∏ _i : Fin k, (W.totient / W * (Real.exp 4 * Real.log (W * R)) : ℝ) := by
        gcongr y.maxRealAbs * ?_
        exact prod_le_prod₀ (fun i _ ↦ by positivity) fun i _ ↦ h₂ i
    _ = y.maxRealAbs * (W.totient / W * (Real.exp 4 * Real.log (W * R))) ^ k := by
        rw [prod_const, card_univ, Fintype.card_fin]

/-- **Sharp bound for Maynard's `λ`.** `|λ_d| ≪ ((φ(Q)/Q) log R)^k`, uniformly in `d` and in
the moduli `Q` with `ModulusHyp`. -/
theorem exists_abs_l₀_le {k : ℕ} (hk : 2 ≤ k) (F : EuclideanSpace ℝ (Fin k) → ℝ)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hsupp : Function.support F ⊆ 𝓡 k)
    (θ δ : ℝ) (hδθ : δ < θ / 2) (CQ η : ℝ) :
    ∃ C N₀ : ℝ, ∀ N : ℕ, N₀ ≤ N → ∀ Q : ℕ, PrimeGaps.ModulusHyp CQ η N Q → ∀ d : Fin k → ℕ,
      |PrimeGaps.l₀ (PrimeGaps.sieveTruncation N δ θ) Q (fun x ↦ F (WithLp.toLp 2 x.ofLp)) d| ≤
        C * ((Q.totient : ℝ) / Q * Real.log (PrimeGaps.sieveTruncation N δ θ)) ^ k := by
  set α := θ / 2 - δ with hα
  have hα0 : 0 < α := by linarith
  refine ⟨MaynardSmoothY.Fmax F * (Real.exp 4 * (|η| / α + 1)) ^ k, Real.exp (Real.log 2 / α),
    fun N hN Q hQ d ↦ ?_⟩
  set R := PrimeGaps.sieveTruncation N δ θ
  set l := PrimeGaps.l₀ R Q (fun x ↦ F (WithLp.toLp 2 x.ofLp))
  have hN0 : (0 : ℝ) < N := (Real.exp_pos _).trans_le hN
  have hR2 : (2 : ℝ) ≤ R := PrimeGaps.two_le_rpow_of_exp_log_two_div_le hα0 hN
  have hlogR : Real.log R = α * Real.log N := Real.log_rpow hN0 _
  have hlogR0 : 0 ≤ Real.log R := Real.log_nonneg (by linarith)
  have hlogN0 : 0 ≤ Real.log N := by
    rw [hlogR] at hlogR0
    exact nonneg_of_mul_nonneg_right (by linarith) hα0
  have hFnn := MaynardSmoothY.Fmax_nonneg F hF
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast hQ.pos
  by_cases hld : l d = 0
  · rw [hld, abs_zero]
    positivity
  have hRfloor : 2 ≤ ⌊R⌋₊ := Nat.le_floor (by exact_mod_cast hR2)
  have hrec : l d = PrimeGaps.yToL (PrimeGaps.lToY l) d := by
    rw [PrimeGaps.yToL_lToY,
      ite_eq_left_of_eq_true _ _ (eq_true fun i ↦
        PrimeGaps.hasPermissibleSupport_l₀.squarefree_of_ne_zero hld i)]
  have hlog : Real.log (Q * ⌊R⌋₊) ≤ (|η| / α + 1) * Real.log R := by
    have hR0 : (0 : ℝ) < ⌊R⌋₊ := by exact_mod_cast (by omega : 0 < ⌊R⌋₊)
    rw [Real.log_mul hQ0.ne' hR0.ne']
    have h₁ : Real.log Q ≤ |η| / α * Real.log R := by
      rw [hlogR, div_mul_eq_mul_div, mul_div_assoc, mul_div_cancel_left₀ _ hα0.ne']
      calc Real.log Q ≤ Real.log ((N : ℝ) ^ η) := Real.log_le_log hQ0 hQ.le_rpow
        _ = η * Real.log N := Real.log_rpow hN0 _
        _ ≤ |η| * Real.log N := by gcongr; exact le_abs_self η
    have h₂ : Real.log ⌊R⌋₊ ≤ Real.log R := Real.log_le_log hR0 (Nat.floor_le (by linarith))
    linarith
  have hlog0 : 0 ≤ Real.log (Q * ⌊R⌋₊) := Real.log_nonneg <| by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (mul_ne_zero hQ.ne_zero (by omega))
  rw [hrec]
  refine (abs_yToL_le PrimeGaps.hasPermissibleSupport_l₀.lToY hQ.ne_zero hRfloor d).trans ?_
  calc (PrimeGaps.lToY l).maxRealAbs *
        ((Q.totient : ℝ) / Q * (Real.exp 4 * Real.log (Q * ⌊R⌋₊))) ^ k
      ≤ MaynardSmoothY.Fmax F *
        ((Q.totient : ℝ) / Q * (Real.exp 4 * ((|η| / α + 1) * Real.log R))) ^ k := by
        gcongr
        exact MaynardSmoothY.maxRealAbs_lambda0_le_Fmax R Q F hk (by linarith) hF hsupp
    _ = MaynardSmoothY.Fmax F * (Real.exp 4 * (|η| / α + 1)) ^ k *
        ((Q.totient : ℝ) / Q * Real.log R) ^ k := by
        rw [mul_assoc, ← mul_pow]
        ring_nf

end Erdos420
