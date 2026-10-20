import Erdos420.Maynard.RoughnessBound.FirstMoment
import Erdos420.Maynard.RoughnessBound.ShiftBound

/-!
# The weight on `n` with `p ∣ n + h_m` for one prime `p`

Fix `m` and a prime `p ∤ Q`. For large `N`, `p` divides no `n + hᵢ` with `i ≠ m` when
`p ∣ n + h_m`, since `p ∤ hᵢ − h_m` once `D₀(N) ≥ max |hᵢ − hⱼ|` (and every prime `≤ D₀(N)`
divides `Q`). On such `n` the weight of `λ = yToL y` equals that of `yToL z` for the shifted
variables `z` (`sum_yToL_eq_sum_yToL_shiftY`), which are supported on tuples coprime to `Q p`.
The `n ≡ w₀ (mod Q)` with `p ∣ n + h_m` form one class mod `Q p`, so the weight on them is
`S₁` at the modulus `Q p`, bounded by `exists_S₁_le` with
`y_max ≤ B_p = L log p / log R + (k − 1) F₀ / (p − 1)` (`abs_shiftY_y₀_le`).
-/

namespace Erdos420

open Finset
open scoped PrimeGaps

/-- The class `n ≡ w₀ (mod Q)` with `p ∣ n + b` is a class mod `Q p`. -/
lemma exists_zmod_mul_iff {Q p : ℕ} (hp : p.Prime) (hpQ : ¬p ∣ Q) (w₀ : ZMod Q) (b : ℕ) :
    ∃ v : ZMod (Q * p), ∀ n : ℕ, (n : ZMod (Q * p)) = v ↔ (n : ZMod Q) = w₀ ∧ p ∣ n + b := by
  have hcop : Q.Coprime p :=
    Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpQ)
  set e := ZMod.chineseRemainder hcop
  refine ⟨e.symm (w₀, -(b : ZMod p)), fun n ↦ ?_⟩
  rw [← e.injective.eq_iff, RingEquiv.apply_symm_apply, map_natCast, Prod.ext_iff]
  simp only [Prod.fst_natCast, Prod.snd_natCast]
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, eq_neg_iff_add_eq_zero]

/-- The `n ≡ w₀ (mod Q)` have `n + hᵢ` coprime to `Q` when `w₀ + hᵢ` is. -/
lemma not_dvd_add_of_gcd_eq_one {Q : ℕ} [NeZero Q] {w₀ : ZMod Q} {b n p : ℕ}
    (hw₀ : ((w₀.val : ℤ) + b).gcd Q = 1) (hn : (n : ZMod Q) = w₀) (hp : p.Prime) (hpQ : p ∣ Q) :
    ¬p ∣ n + b := by
  intro hpn
  have hQ : (Q : ℤ) ∣ (n : ℤ) - w₀.val := by
    rw [← ZMod.intCast_eq_intCast_iff_dvd_sub]
    push_cast
    rw [hn, ZMod.natCast_zmod_val]
  have hpw : (p : ℤ) ∣ (w₀.val : ℤ) + b := by
    have := dvd_sub (Int.natCast_dvd_natCast.mpr hpn) ((Int.natCast_dvd_natCast.mpr hpQ).trans hQ)
    push_cast at this
    convert this using 1
    ring
  have h1 : (p : ℤ) ∣ ((w₀.val : ℤ) + b).gcd Q :=
    Int.dvd_coe_gcd hpw (Int.natCast_dvd_natCast.mpr hpQ)
  rw [hw₀, Nat.cast_one] at h1
  exact hp.one_lt.ne' (by exact_mod_cast Int.eq_one_of_dvd_one (by positivity) h1)

/-- `∑_{n ≤ R, (n, Q p) = 1} μ²(n) / φ(n) ≤ ∑_{n ≤ R, (n, Q) = 1} μ²(n) / φ(n)`. -/
lemma sumA_mul_le (Q p : ℕ) (R : ℝ) :
    PrimeGaps.MaynardOffDiagonal.sumA (Q * p) R ≤ PrimeGaps.MaynardOffDiagonal.sumA Q R := by
  unfold PrimeGaps.MaynardOffDiagonal.sumA PrimeGaps.MaynardOffDiagonal.Sset
  refine sum_le_sum_of_subset_of_nonneg (fun n hn ↦ ?_) fun _ _ _ ↦ by positivity
  simp only [mem_filter] at hn ⊢
  exact ⟨hn.1, hn.2.1, Nat.Coprime.coprime_dvd_right (dvd_mul_right Q p) hn.2.2⟩

open PrimeGaps in
open scoped PrimeGaps.sieveTruncation in
/-- **The weight on one prime.** For large `N`, every `Q` with `ModulusHyp`, valid `w₀`, `m`
and prime `p ∤ Q`, the weight on `n ≡ w₀ (mod Q)` with `p ∣ n + h_m` is at most
`C (N / (Q p)) B² A^k + (C B R (log R)^{2k})²` with `B = L log p / log R + (k − 1) F₀ / (p − 1)`
and `A = sumA Q R`. -/
theorem exists_sum_weight_dvd_le {k : ℕ} (hk : 2 ≤ k) (h : Fin k → ℕ)
    (hadm : GPYSieveS1.IsAdmissible h) (F : EuclideanSpace ℝ (Fin k) → ℝ)
    (hsupp : Function.support F ⊆ 𝓡 k) (L : NNReal) (hL : LipschitzWith L F) (F₀ : ℝ)
    (hF₀ : ∀ x, |F x| ≤ F₀) (θ δ : ℝ) (hθ : θ ∈ Set.Ioo (0 : ℝ) 1)
    (hδ : δ ∈ Set.Ioo (0 : ℝ) (θ / 2)) (CQ η : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ N →
      ∀ Q : ℕ, PrimeGaps.ModulusHyp CQ η N Q → ∀ w₀ : ZMod Q,
        (∀ i, ((w₀.val : ℤ) + h i).gcd Q = 1) → ∀ m : Fin k, ∀ p : ℕ, p.Prime → ¬p ∣ Q →
        ∑ n ∈ Ioc N (2 * N) with (n : ℕ) = w₀ ∧ p ∣ n + h m,
            PrimeGaps.weight h (PrimeGaps.l₀ R Q (fun x ↦ F (WithLp.toLp 2 x.ofLp))) n ≤
          C * (N / (Q * p : ℝ)) * (L * (Real.log p / Real.log R) + (k - 1) / (p - 1) * F₀) ^ 2 *
              PrimeGaps.MaynardOffDiagonal.sumA Q R ^ k +
            (C * (L * (Real.log p / Real.log R) + (k - 1) / (p - 1) * F₀) * R *
              Real.log R ^ (2 * k)) ^ 2 := by
  classical
  obtain ⟨C, hC, NS, hS⟩ := exists_S₁_le hk h hadm.1.injective θ δ hθ hδ
  obtain ⟨Nthr, hthr⟩ := GPYSieveS1.exists_thresh h
  have hc₀ : 0 < θ / 2 - δ := by linarith [hδ.2]
  have hRt : Filter.Tendsto (fun N : ℕ ↦ ((N : ℝ) ^ (θ / 2 - δ))) Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop hc₀).comp tendsto_natCast_atTop_atTop
  obtain ⟨NR, hNR⟩ := Filter.eventually_atTop.mp (hRt.eventually_gt_atTop 1)
  refine ⟨C, hC, max (max NS Nthr) NR, ?_⟩
  intro N hN Q hQ w₀ hw₀ m p hp hpQ
  have hNS : NS ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  obtain ⟨-, hthrN⟩ := hthr N (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN)
  have hR1 : 1 < (N : ℝ) ^ (θ / 2 - δ) := hNR N (by exact_mod_cast le_trans (le_max_right _ _) hN)
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  set G : EuclideanSpace ℝ (Fin k) → ℝ := fun x ↦ F (WithLp.toLp 2 x.ofLp)
  have hGF : G = F := funext fun x ↦ by simp [G]
  set T := permissibleSupport k ⌊R⌋₊ Q
  set y := PrimeGaps.y₀ R Q G
  set c : Fin k → ℝ := fun j ↦ if j = m then -1 else 1 / (p - 1)
  set z := shiftY T y p c
  set B := L * (Real.log p / Real.log R) + (k - 1) / (p - 1) * F₀
  obtain ⟨v, hv⟩ := exists_zmod_mul_iff hp hpQ w₀ (h m)
  -- `p ∤ n + hᵢ` for `i ≠ m`
  have hnot : ∀ n : ℕ, (n : ZMod Q) = w₀ → p ∣ n + h m → ∀ j, j ≠ m → ¬p ∣ n + h j := by
    intro n _ hpm j hjm hpj
    have hdvd : (p : ℤ) ∣ (h j : ℤ) - h m := by
      have := dvd_sub (Int.natCast_dvd_natCast.mpr hpj) (Int.natCast_dvd_natCast.mpr hpm)
      push_cast at this
      convert this using 1
      ring
    have hne : (h j : ℤ) - h m ≠ 0 :=
      sub_ne_zero.mpr fun he ↦ hjm (hadm.1.injective (by exact_mod_cast he))
    have hle : (p : ℝ) ≤ |(h j : ℝ) - h m| := by
      have := Int.le_of_dvd (abs_pos.mpr hne) ((dvd_abs _ _).mpr hdvd)
      exact_mod_cast this
    exact hpQ (hQ.prime_dvd_of_le_D₀ hp (hle.trans (hthrN j m hjm)))
  -- the weights agree on the class
  have hweight : ∀ n ∈ (Ioc N (2 * N)).filter (fun n : ℕ ↦ (n : ZMod Q) = w₀ ∧ p ∣ n + h m),
      PrimeGaps.weight h (PrimeGaps.l₀ R Q G) n = PrimeGaps.weight h (PrimeGaps.yToL z) n := by
    intro n hn
    obtain ⟨hnI, hnw, hpm⟩ := mem_filter.mp hn
    have hn0 : ∀ i, n + h i ≠ 0 := fun i ↦ by have := (mem_Ioc.mp hnI).1; omega
    unfold PrimeGaps.weight
    congr 1
    refine sum_yToL_eq_sum_yToL_shiftY hp PrimeGaps.hasPermissibleSupport_y₀ (fun i ↦ n + h i)
      hn0 c fun j ↦ ?_
    by_cases hjm : j = m
    · subst hjm
      simp [c, divKernel_prime_of_dvd hp hpm]
    · simp only [c, ite_eq_right hjm]
      rw [divKernel_prime_of_not_dvd hp (hnot n hnw hpm j hjm)]
  have hsum : ∑ n ∈ Ioc N (2 * N) with (n : ℕ) = w₀ ∧ p ∣ n + h m,
      PrimeGaps.weight h (PrimeGaps.l₀ R Q G) n = PrimeGaps.S₁ h (PrimeGaps.yToL z) N v := by
    rw [sum_congr rfl hweight, PrimeGaps.S₁]
    exact sum_congr (filter_congr fun n _ ↦ (hv n).symm) fun _ _ ↦ rfl
  rw [hsum]
  -- the size of `z`
  have hB : (PrimeGaps.lToY (PrimeGaps.yToL z)).maxRealAbs ≤ B := by
    rw [Finsupp.maxRealAbs_le_iff]
    intro r
    rw [PrimeGaps.lToY_yToL]
    have hz := abs_shiftY_y₀_le hR1 hp hpQ (hGF ▸ hL) (hGF ▸ hF₀) (hGF ▸ hsupp) m c
      (by simp [c]) r
    have hp1' : (0 : ℝ) < p - 1 := by linarith
    have hcsum : ∑ j ∈ univ.erase m, |c j| = (k - 1) / (p - 1) := by
      rw [sum_congr rfl fun j hj ↦ by
          rw [show c j = 1 / (p - 1) from ite_eq_right (ne_of_mem_erase hj),
            abs_of_pos (by positivity)],
        sum_const, card_erase_of_mem (mem_univ m), card_univ, Fintype.card_fin, nsmul_eq_mul]
      push_cast [show 1 ≤ k by omega]
      ring
    rw [hcsum] at hz
    split_ifs
    · exact hz
    · simpa using (abs_nonneg _).trans hz
  have hz : (PrimeGaps.yToL z).HasPermissibleSupport ⌊R⌋₊ (Q * p) :=
    (hasPermissibleSupport_shiftY hp y c).yToL
  refine (hS N hNS (Q * p) (Nat.mul_pos hQ.pos hp.pos)
    (hQ.primorial_dvd.trans (dvd_mul_right Q p)) _ hz v B hB).trans ?_
  have hA := sumA_mul_le Q p R
  have hA0 : 0 ≤ PrimeGaps.MaynardOffDiagonal.sumA (Q * p) R :=
    sum_nonneg fun _ _ ↦ by positivity
  push_cast
  gcongr

end Erdos420
