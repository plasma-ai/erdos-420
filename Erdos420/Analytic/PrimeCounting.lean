import Erdos420.Analytic.PrimesInAP
import PrimeGapsTheory.NumberTheory.PrimeCountingZMod

/-!
# Counting primes by partial summation

`π(x; q, c) = π(x) / φ(q) + O(x^{15/16} log² x)` uniformly for `q ≤ x` and `c`
coprime to `q`, and `π(N) = N / log N + O(N / log² N)`.

With `b_p = (1_{p ≡ c} − 1/φ(q)) log p` on the primes, the partial sums of `b` are
`θ(t; q, c) − θ(t)/φ(q)`, where the main terms `t/φ(q)` cancel. For `t ≥ q` both
are `O(t^{15/16} log² t)` by `exists_abs_thetaAP_sub_le`. For `t < q` both are at
most their values at `q`, where the class holds at most one prime, which also
bounds `q/φ(q)`. Abel's inequality with the weights `1/log p` finishes the proof.

For the prime number theorem, `π(x) − θ(x)/log x = O(x / log² x)` by Mathlib's
partial summation, and `θ(x) − x = O(x^{15/16} log² x)` is the case `q = 1`.
-/

namespace Erdos420

open Real

/-- `π(x; q, c) = #{p ≤ x : p prime, p ≡ c (mod q)}`. -/
noncomputable def primeCountingAP (x : ℝ) (q c : ℕ) : ℕ :=
  ((Finset.Iic ⌊x⌋₊).filter (fun p ↦ p.Prime ∧ p ≡ c [MOD q])).card

/-- **Abel's inequality.** If every partial sum of `b` is at most `M` in absolute value
and `w` is antitone and nonnegative, then `|∑_{k < n} b k w k| ≤ M w 0`. -/
private lemma abs_sum_range_mul_le {b w : ℕ → ℝ} (hw : Antitone w) (hw₀ : ∀ k, 0 ≤ w k) {M : ℝ}
    {n : ℕ} (hB : ∀ m ≤ n, |∑ k ∈ Finset.range m, b k| ≤ M) :
    |∑ k ∈ Finset.range n, b k * w k| ≤ M * w 0 := by
  set B : ℕ → ℝ := fun m ↦ ∑ k ∈ Finset.range m, b k
  -- summation by parts, one term at a time
  have key : ∀ m ≤ n, |∑ k ∈ Finset.range m, b k * w k - B m * w m| ≤ M * (w 0 - w m) := by
    intro m
    induction m with
    | zero => intro _; simp [B]
    | succ m ih =>
      intro hm
      have h : ∑ k ∈ Finset.range (m + 1), b k * w k - B (m + 1) * w (m + 1) =
          (∑ k ∈ Finset.range m, b k * w k - B m * w m) + B (m + 1) * (w m - w (m + 1)) := by
        simp only [B, Finset.sum_range_succ]
        ring
      have hw' : 0 ≤ w m - w (m + 1) := sub_nonneg.mpr (hw (Nat.le_succ m))
      rw [h]
      calc _ ≤ |∑ k ∈ Finset.range m, b k * w k - B m * w m| +
            |B (m + 1) * (w m - w (m + 1))| := abs_add_le _ _
        _ ≤ M * (w 0 - w m) + M * (w m - w (m + 1)) := by
            gcongr
            · exact ih (by omega)
            · rw [abs_mul, abs_of_nonneg hw']
              exact mul_le_mul_of_nonneg_right (hB _ hm) hw'
        _ = M * (w 0 - w (m + 1)) := by ring
  have h₁ := key n le_rfl
  have h₂ : |B n * w n| ≤ M * w n := by
    rw [abs_mul, abs_of_nonneg (hw₀ n)]
    exact mul_le_mul_of_nonneg_right (hB n le_rfl) (hw₀ n)
  have h₃ := abs_sub_abs_le_abs_sub (∑ k ∈ Finset.range n, b k * w k) (B n * w n)
  linarith

/-- `θ(j; q, c)` at a natural number `j`, as a sum over `[0, j]`. -/
lemma thetaAP_natCast (j q c : ℕ) : thetaAP j q c =
    ∑ k ∈ Finset.range (j + 1), if k.Prime ∧ k ≡ c [MOD q] then Real.log k else 0 := by
  rw [thetaAP, Nat.floor_natCast, Finset.sum_filter, Nat.range_succ_eq_Iic]

/-- `θ(Y; q, c)` is monotone in `Y`. -/
lemma thetaAP_mono (q c : ℕ) : Monotone (fun Y ↦ thetaAP Y q c) := fun _ _ h ↦
  Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.filter_subset_filter _ (Finset.Iic_subset_Iic.mpr (Nat.floor_mono h)))
    fun p _ _ ↦ Real.log_natCast_nonneg p

/-- `θ(Y; q, c) ≥ 0`. -/
lemma thetaAP_nonneg (Y : ℝ) (q c : ℕ) : 0 ≤ thetaAP Y q c :=
  Finset.sum_nonneg fun p _ ↦ Real.log_natCast_nonneg p

/-- Below `2` there are no primes. -/
lemma thetaAP_natCast_of_lt_two {j : ℕ} (hj : j < 2) (q c : ℕ) : thetaAP j q c = 0 := by
  rw [thetaAP, Nat.floor_natCast]
  refine Finset.sum_eq_zero fun p hp ↦ ?_
  simp only [Finset.mem_filter, Finset.mem_Iic] at hp
  have := hp.2.1.two_le
  omega

/-- At most one prime up to `q` lies in a given class mod `q`. -/
lemma thetaAP_self_le (q c : ℕ) : thetaAP q q c ≤ Real.log q := by
  rw [thetaAP, Nat.floor_natCast]
  set F := (Finset.Iic q).filter (fun p ↦ p.Prime ∧ p ≡ c [MOD q])
  have hF : F.card ≤ 1 := Finset.card_le_one.mpr fun a ha b hb ↦ by
    simp only [F, Finset.mem_filter, Finset.mem_Iic] at ha hb
    refine (ha.2.2.trans hb.2.2.symm).eq_of_abs_lt ?_
    have := ha.2.1.one_le
    have := hb.2.1.one_le
    rw [abs_sub_lt_iff]
    constructor <;> omega
  have hlog : 0 ≤ Real.log q := Real.log_natCast_nonneg q
  calc ∑ p ∈ F, Real.log p ≤ ∑ _p ∈ F, Real.log q := by
        refine Finset.sum_le_sum fun p hp ↦ ?_
        simp only [F, Finset.mem_filter, Finset.mem_Iic] at hp
        exact Real.log_le_log (by exact_mod_cast hp.2.1.pos) (by exact_mod_cast hp.1)
    _ = F.card * Real.log q := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 1 * Real.log q := by gcongr; exact_mod_cast hF
    _ = Real.log q := one_mul _

/-- `θ(Y; 1, c)` is Chebyshev's `θ(Y)`. -/
lemma thetaAP_one (Y : ℝ) (c : ℕ) : thetaAP Y 1 c = Chebyshev.theta Y := by
  rw [thetaAP, Chebyshev.theta]
  refine Finset.sum_congr ?_ fun _ _ ↦ rfl
  ext p
  simp only [Finset.mem_filter, Finset.mem_Iic, Finset.mem_Ioc, Nat.modEq_one, and_true]
  exact ⟨fun h ↦ ⟨⟨h.2.pos, h.1⟩, h.2⟩, fun h ↦ ⟨h.1.2, h.2⟩⟩

/-- `π(z; q, c) = π(z) / φ(q) + O(x^{15/16} log² x)` uniformly for `z ≤ x`, `q ≤ x`, and
`c` coprime to `q`. -/
theorem exists_abs_primeCountingAP_sub_le_of_le : ∃ K : ℝ, ∀ x : ℝ, 2 ≤ x → ∀ q c : ℕ,
    1 ≤ q → (q : ℝ) ≤ x → c.Coprime q → ∀ z : ℝ, z ≤ x →
      |(primeCountingAP z q c : ℝ) - Nat.primeCounting ⌊z⌋₊ / q.totient| ≤
        K * x ^ (15 / 16 : ℝ) * Real.log x ^ 2 := by
  obtain ⟨K, hK⟩ := exists_abs_thetaAP_sub_le
  have hK₀ : 0 ≤ K := by
    have h := (abs_nonneg _).trans (hK 2 le_rfl 1 0 le_rfl (by norm_num) (Nat.coprime_one_right 0))
    rw [mul_assoc] at h
    exact (mul_nonneg_iff_of_pos_right (by positivity)).mp h
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨(2 / Real.log 2 + 2 * K) / Real.log 2, fun x hx q c hq hqx hc z hzx ↦ ?_⟩
  set X := x ^ (15 / 16 : ℝ) * Real.log x ^ 2
  set M := (2 / Real.log 2 + 2 * K) * X
  set φ : ℝ := (q.totient : ℝ)
  have hφ : 1 ≤ φ := Nat.one_le_cast.mpr (Nat.totient_pos.mpr hq)
  have hX : 0 ≤ X := by positivity
  have hM : 0 ≤ M := by positivity
  have hmono : ∀ t : ℝ, 1 ≤ t → t ≤ x → t ^ (15 / 16 : ℝ) * Real.log t ^ 2 ≤ X := by
    intro t ht htx
    have := Real.log_nonneg ht
    simp only [X]
    gcongr
  -- the partial sums `θ(j; q, c) − θ(j)/φ(q)` are `O(x^{15/16} log² x)`
  have hA : ∀ j : ℕ, (j : ℝ) ≤ x → |thetaAP j q c - thetaAP j 1 0 / φ| ≤ M := by
    intro j hjx
    rcases lt_or_ge j 2 with hj | hj
    · rw [thetaAP_natCast_of_lt_two hj, thetaAP_natCast_of_lt_two hj]
      simpa using hM
    have hj₂ : (2 : ℝ) ≤ j := by exact_mod_cast hj
    have hθ₁ := thetaAP_nonneg j q c
    have hθ₂ := thetaAP_nonneg j 1 0
    rcases le_or_gt q j with hqj | hqj
    · -- the power-saving estimate at `j`, for `q` and for `1`
      have h₁ := hK j hj₂ q c hq (by exact_mod_cast hqj) hc
      have h₂ := hK j hj₂ 1 0 le_rfl (by push_cast; linarith) (Nat.coprime_one_right 0)
      rw [Nat.totient_one, Nat.cast_one, div_one] at h₂
      have h₃ : K * (j : ℝ) ^ (15 / 16 : ℝ) * Real.log j ^ 2 ≤ K * X := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (hmono j (by linarith) hjx) hK₀
      have h₄ : thetaAP j q c - thetaAP j 1 0 / φ =
          (thetaAP j q c - j / φ) - (thetaAP j 1 0 - j) / φ := by ring
      have h₅ : |(thetaAP j 1 0 - j) / φ| ≤ |thetaAP j 1 0 - j| := by
        rw [abs_div, abs_of_pos (by linarith : (0 : ℝ) < φ)]
        exact div_le_self (abs_nonneg _) hφ
      have h₆ := abs_sub (thetaAP j q c - j / φ) ((thetaAP j 1 0 - j) / φ)
      have h₇ : 0 ≤ 2 / Real.log 2 * X := by positivity
      rw [h₄]
      linarith
    · -- `2 ≤ j < q`: compare with `Y = q`, where the class holds at most one prime
      have hq₂ : (2 : ℝ) ≤ q := by exact_mod_cast (by omega : 2 ≤ q)
      have h₁ := hK q hq₂ q c hq le_rfl hc
      have h₂ := hK q hq₂ 1 0 le_rfl (by push_cast; linarith) (Nat.coprime_one_right 0)
      rw [Nat.totient_one, Nat.cast_one, div_one] at h₂
      have h₃ := thetaAP_self_le q c
      have h₄ : thetaAP j q c ≤ thetaAP q q c := thetaAP_mono q c (by exact_mod_cast hqj.le)
      have h₅ : thetaAP j 1 0 ≤ thetaAP q 1 0 := thetaAP_mono 1 0 (by exact_mod_cast hqj.le)
      have hQ : K * (q : ℝ) ^ (15 / 16 : ℝ) * Real.log q ^ 2 ≤ K * X := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (hmono q (by linarith) hqx) hK₀
      have hQ₀ : 0 ≤ K * (q : ℝ) ^ (15 / 16 : ℝ) * Real.log q ^ 2 := by
        have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ q)
        positivity
      set Q := K * (q : ℝ) ^ (15 / 16 : ℝ) * Real.log q ^ 2
      -- `θ(j)/φ(q) ≤ θ(q)/φ(q) ≤ q/φ(q) + Q ≤ log q + 2 Q`
      have h₆ : thetaAP j 1 0 / φ ≤ Real.log q + 2 * Q := by
        have h₇ : thetaAP j 1 0 / φ ≤ (q + Q) / φ :=
          div_le_div_of_nonneg_right (by linarith [(abs_le.mp h₂).2]) (by linarith)
        have h₈ : Q / φ ≤ Q := div_le_self hQ₀ hφ
        have h₉ : (q : ℝ) / φ ≤ Real.log q + Q := by linarith [(abs_le.mp h₁).1]
        rw [add_div] at h₇
        linarith
      -- `log q ≤ q^{15/16} log² q / log 2`
      have h₁₀ : Real.log q ≤ X / Real.log 2 := by
        rw [le_div_iff₀ hlog2]
        have hlq : Real.log 2 ≤ Real.log q := Real.log_le_log (by norm_num) hq₂
        have h₁₁ : (1 : ℝ) ≤ (q : ℝ) ^ (15 / 16 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
        calc Real.log q * Real.log 2 ≤ 1 * Real.log q ^ 2 := by nlinarith
          _ ≤ (q : ℝ) ^ (15 / 16 : ℝ) * Real.log q ^ 2 := by gcongr
          _ ≤ X := hmono q (by linarith) hqx
      have h₁₂ : M = 2 * (X / Real.log 2) + 2 * (K * X) := by
        simp only [M]
        ring
      have h₁₃ : 0 ≤ thetaAP j 1 0 / φ := div_nonneg hθ₂ (by linarith)
      have h₁₄ : 0 ≤ X / Real.log 2 := by positivity
      rw [abs_sub_le_iff]
      constructor <;> linarith
  -- Abel summation against the weights `1 / log k`
  set N := ⌊z⌋₊
  set b : ℕ → ℝ := fun k ↦
    if k.Prime then ((if k ≡ c [MOD q] then 1 else 0) - φ⁻¹) * Real.log k else 0
  set w : ℕ → ℝ := fun k ↦ (Real.log (max (k : ℝ) 2))⁻¹
  have hw₀ : ∀ k, 0 ≤ w k := fun k ↦
    inv_nonneg.mpr (Real.log_nonneg (by linarith [le_max_right (k : ℝ) 2]))
  have hw : Antitone w := by
    intro k l hkl
    refine inv_anti₀ (Real.log_pos (by linarith [le_max_right (k : ℝ) 2])) ?_
    refine Real.log_le_log (by linarith [le_max_right (k : ℝ) 2]) ?_
    exact max_le_max (by exact_mod_cast hkl) le_rfl
  have hsum : (primeCountingAP z q c : ℝ) - Nat.primeCounting N / φ =
      ∑ k ∈ Finset.range (N + 1), b k * w k := by
    have h₁ : (primeCountingAP z q c : ℝ) =
        ∑ k ∈ Finset.range (N + 1), if k.Prime ∧ k ≡ c [MOD q] then (1 : ℝ) else 0 := by
      rw [Finset.sum_boole, primeCountingAP, Nat.range_succ_eq_Iic]
    have h₂ : (Nat.primeCounting N : ℝ) =
        ∑ k ∈ Finset.range (N + 1), if k.Prime then (1 : ℝ) else 0 := by
      rw [Finset.sum_boole, Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]
    rw [h₁, h₂, Finset.sum_div, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    by_cases hp : k.Prime
    · have hk : (2 : ℝ) ≤ k := by exact_mod_cast hp.two_le
      have hlog : Real.log k ≠ 0 := (Real.log_pos (by linarith)).ne'
      simp only [b, w, hp, true_and, ite_true, max_eq_left hk]
      split_ifs <;> field_simp
    · simp [b, hp]
  have hpart : ∀ m ≤ N + 1, |∑ k ∈ Finset.range m, b k| ≤ M := by
    intro m hm
    cases m with
    | zero => simpa using hM
    | succ j =>
      have hjx : (j : ℝ) ≤ x := by
        rcases Nat.eq_zero_or_pos j with rfl | hj
        · simp only [Nat.cast_zero]
          linarith
        · exact ((Nat.le_floor_iff' hj.ne').mp (by omega)).trans hzx
      have h : ∑ k ∈ Finset.range (j + 1), b k = thetaAP j q c - thetaAP j 1 0 / φ := by
        rw [thetaAP_natCast, thetaAP_natCast, Finset.sum_div, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun k _ ↦ ?_
        by_cases hp : k.Prime
        · by_cases hkc : k ≡ c [MOD q]
          · simp [b, hp, hkc, Nat.modEq_one]
            ring
          · simp [b, hp, hkc, Nat.modEq_one]
            ring
        · simp [b, hp]
      rw [h]
      exact hA j hjx
  have h := abs_sum_range_mul_le hw hw₀ hpart
  have hw0 : w 0 = (Real.log 2)⁻¹ := by simp [w]
  rw [hsum]
  calc _ ≤ M * w 0 := h
    _ = (2 / Real.log 2 + 2 * K) / Real.log 2 * x ^ (15 / 16 : ℝ) * Real.log x ^ 2 := by
        rw [hw0]
        ring

/-- **Primes in progressions.** `π(x; q, c) = π(x) / φ(q) + O(x^{15/16} log² x)` uniformly
for `q ≤ x` and `c` coprime to `q`. -/
theorem exists_abs_primeCountingAP_sub_le : ∃ K : ℝ, ∀ x : ℝ, 2 ≤ x → ∀ q c : ℕ, 1 ≤ q →
    (q : ℝ) ≤ x → c.Coprime q →
      |(primeCountingAP x q c : ℝ) - Nat.primeCounting ⌊x⌋₊ / q.totient| ≤
        K * x ^ (15 / 16 : ℝ) * Real.log x ^ 2 := by
  obtain ⟨K, hK⟩ := exists_abs_primeCountingAP_sub_le_of_le
  exact ⟨K, fun x hx q c hq hqx hc ↦ hK x hx q c hq hqx hc x le_rfl⟩

/-- The `ZMod` prime count `π(x; q, a)` is `π(x; q, a.val)`. -/
lemma primeCountingZMod_eq_primeCountingAP (x : ℝ) {q : ℕ} [NeZero q] (a : ZMod q) :
    Real.primeCountingZMod x q a = primeCountingAP x q a.val := by
  rw [Real.primeCountingZMod_eq_card_finset_range, primeCountingAP, Nat.range_succ_eq_Iic]
  refine congrArg Finset.card (Finset.filter_congr fun p _ ↦ ?_)
  rw [← ZMod.natCast_eq_natCast_iff, ZMod.natCast_zmod_val]

/-- **Primes in progressions**, for `Real.primeCountingZMod`:
`π(x; q, a) = π(x) / φ(q) + O(x^{15/16} log² x)` uniformly for `q ≤ x` and units `a`. -/
theorem exists_abs_primeCountingZMod_sub_le : ∃ K : ℝ, ∀ x : ℝ, 2 ≤ x → ∀ q : ℕ, 1 ≤ q →
    (q : ℝ) ≤ x → ∀ a : (ZMod q)ˣ,
      |(Real.primeCountingZMod x q a : ℝ) - Nat.primeCounting ⌊x⌋₊ / q.totient| ≤
        K * x ^ (15 / 16 : ℝ) * Real.log x ^ 2 := by
  obtain ⟨K, hK⟩ := exists_abs_primeCountingAP_sub_le
  refine ⟨K, fun x hx q hq hqx a ↦ ?_⟩
  have : NeZero q := ⟨by omega⟩
  rw [primeCountingZMod_eq_primeCountingAP]
  exact hK x hx q _ hq hqx (ZMod.val_coe_unit_coprime a)

open Nat Real Filter Asymptotics in
/-- **Prime number theorem** with the error `O(N / log² N)`, as in `PNT.primeCounting`. -/
theorem pnt_primeCounting :
    ∃ (C : ℝ) (N₀ : ℕ), ∀ N ≥ N₀, |primeCounting N - N / Real.log N| ≤ C * N / Real.log N ^ 2 := by
  obtain ⟨K, hK⟩ := exists_abs_thetaAP_sub_le
  -- `θ(x)/log x − x/log x = O(x / log² x)`, from `θ(x) − x = O(x^{15/16} log² x)`
  have hθ : (fun x : ℝ ↦ Chebyshev.theta x / Real.log x - x / Real.log x) =O[atTop]
      (fun x ↦ x / Real.log x ^ 2) := by
    refine IsBigO.of_bound (|K| * 48 ^ 3) ?_
    filter_upwards [eventually_ge_atTop 2] with x hx
    have hlog : 0 < Real.log x := Real.log_pos (by linarith)
    have h₁ := hK x hx 1 0 le_rfl (by simpa using (by linarith : (1 : ℝ) ≤ x))
      (Nat.coprime_one_right 0)
    rw [thetaAP_one, Nat.totient_one, Nat.cast_one, div_one] at h₁
    -- `log³ x ≤ 48³ x^{1/16}`
    have h₂ : Real.log x ≤ 48 * x ^ (1 / 48 : ℝ) := by
      calc Real.log x ≤ x ^ (1 / 48 : ℝ) / (1 / 48) := Real.log_le_rpow_div (x := x) (ε := 1 / 48)
            (by linarith) (by norm_num)
        _ = 48 * x ^ (1 / 48 : ℝ) := by ring
    have h₃ : (x : ℝ) ^ (15 / 16 : ℝ) * Real.log x ^ 3 ≤ 48 ^ 3 * x := by
      calc (x : ℝ) ^ (15 / 16 : ℝ) * Real.log x ^ 3 ≤
            x ^ (15 / 16 : ℝ) * (48 * x ^ (1 / 48 : ℝ)) ^ 3 := by gcongr
        _ = 48 ^ 3 * x := by
          rw [mul_pow, ← Real.rpow_natCast (x ^ (1 / 48 : ℝ)), ← Real.rpow_mul (by linarith),
            mul_left_comm, ← Real.rpow_add (by linarith)]
          norm_num
    rw [Real.norm_eq_abs, Real.norm_eq_abs, ← sub_div, abs_div, abs_of_pos hlog,
      abs_of_nonneg (div_nonneg (by linarith : (0 : ℝ) ≤ x) (sq_nonneg (Real.log x))),
      div_le_iff₀ hlog]
    have hlog' := hlog.ne'
    calc |Chebyshev.theta x - x| ≤ K * x ^ (15 / 16 : ℝ) * Real.log x ^ 2 := h₁
      _ ≤ |K| * (x ^ (15 / 16 : ℝ) * Real.log x ^ 3) / Real.log x := by
          rw [show |K| * (x ^ (15 / 16 : ℝ) * Real.log x ^ 3) / Real.log x =
            |K| * x ^ (15 / 16 : ℝ) * Real.log x ^ 2 by field_simp]
          gcongr
          exact le_abs_self K
      _ ≤ |K| * (48 ^ 3 * x) / Real.log x := by gcongr
      _ = |K| * 48 ^ 3 * (x / Real.log x ^ 2) * Real.log x := by
          field_simp
  obtain ⟨C, hC⟩ := (Chebyshev.primeCounting_sub_theta_div_log_isBigO.add hθ).bound
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.mp hC
  refine ⟨C, ⌈x₀⌉₊, fun N hN ↦ ?_⟩
  have h := hx₀ N ((Nat.le_ceil x₀).trans (by exact_mod_cast hN))
  simp only [Nat.floor_natCast, Real.norm_eq_abs, sub_add_sub_cancel] at h
  rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ N / Real.log N ^ 2)] at h
  rw [mul_div_assoc]
  exact h

end Erdos420
