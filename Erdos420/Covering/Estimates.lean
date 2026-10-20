module

public import Erdos420.Asymptotics
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.EulerProduct.Basic
public import Mathlib.NumberTheory.Harmonic.Bounds
public import Mathlib.NumberTheory.SmoothNumbers

/-!
# Prime-counting and smooth-number estimates for the covering

Chebyshev's bounds `θ(x) ≥ x log 2 − o(x)` and `θ(x) ≤ x log 4` give:

* `θ(4t) − θ(t) ≥ t`, so `∑_{t < p ≤ 4t} 1/p ≥ 1 / (8 log t)` for large `t`.
* Summed over the blocks `(4^j X, 4^{j+1} X]`, `∑_{X < p ≤ X²} 1/p ≥ 1/50`, and so
  `∑_{X < p ≤ X^{2^I}} 1/p ≥ I/50` for large `X`.
* At least `u / (4 log u)` primes lie in `(u/4, u]`, and `π(m) ≤ 2 m / log m`.

Rankin's trick bounds the `N`-smooth numbers up to `X` by
`X^σ ∏_{p < N} (1 − p^{−σ})⁻¹ ≤ X^σ exp (4 N^{1−σ} (1 + log N))`. With
`N ≈ (log u)^A` and `σ = 1 − 1/(2A)`, at most `u / log u` of the integers in `[1, C u]`
are `N`-smooth, for large `u`.
-/

@[expose] public section

namespace Erdos420

open Filter Finset Real Chebyshev

/-! ### Asymptotic comparisons -/

/-- Eventually `√x log x ≤ c x`. -/
private lemma eventually_sqrt_mul_log_le {c : ℝ} (hc : 0 < c) :
    ∀ᶠ x : ℝ in atTop, √x * log x ≤ c * x := by
  filter_upwards [tendsto_sqrt_atTop.eventually
      (eventually_log_le_const_mul (c := c / 2) (by positivity)),
    eventually_ge_atTop 0] with x hx hx0
  rw [log_sqrt hx0] at hx
  calc √x * log x = 2 * (√x * (log x / 2)) := by ring
    _ ≤ 2 * (√x * (c / 2 * √x)) := by gcongr
    _ = c * (√x * √x) := by ring
    _ = c * x := by rw [mul_self_sqrt hx0]

/-! ### Sums of `1/p` over ranges of primes -/

/-- `θ n − θ m` is the sum of `log p` over the primes `p ∈ (m, n]`. -/
private lemma theta_sub_theta {m n : ℕ} (h : m ≤ n) :
    θ n - θ m = ∑ p ∈ Ioc m n with p.Prime, log p := by
  simp only [theta, Nat.floor_natCast, sum_filter]
  rw [← sum_Ioc_consecutive _ (Nat.zero_le m) h]
  ring

/-- Eventually `t ≤ θ (4 t) − θ t`. -/
lemma eventually_le_theta_sub : ∀ᶠ t : ℕ in atTop, (t : ℝ) ≤ θ ((4 * t : ℕ) : ℝ) - θ t := by
  have h4 : Tendsto (fun t : ℕ ↦ 4 * (t : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num)
  filter_upwards [h4.eventually (eventually_sqrt_mul_log_le (c := 1 / 40) (by norm_num)),
    h4.eventually ((tendsto_atTop_add_const_right _ 1 tendsto_id).eventually
      (eventually_log_le_const_mul (c := 1 / 80) (by norm_num))),
    eventually_ge_atTop 1] with t h1 h2 ht
  have ht' : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hθ₁ := theta_ge (4 * t)
  have hθ₂ := theta_le_log4_mul_x (Nat.cast_nonneg (α := ℝ) t)
  have hlog4 := log_four_eq
  have hlog2 := log_two_gt_d9
  have hlog2t : 0.6931471803 * (t : ℝ) ≤ log 2 * t := by gcongr
  simp only [id] at h2
  push_cast at hθ₁ h1 h2 ⊢
  nlinarith

/-- Eventually `1 / (8 log t) ≤ ∑_{t < p ≤ 4t} 1/p`. -/
lemma eventually_inv_log_le_sum_Ioc_four_mul :
    ∀ᶠ t : ℕ in atTop, 1 / (8 * log t) ≤ ∑ p ∈ Ioc t (4 * t) with p.Prime, (1 : ℝ) / p := by
  filter_upwards [eventually_le_theta_sub, eventually_ge_atTop 4] with t hθ ht
  have ht' : (4 : ℝ) ≤ t := by exact_mod_cast ht
  have hlogt : 0 < log t := log_pos (by linarith)
  have hlog4t : 0 < log (4 * t) := log_pos (by linarith)
  have hlog : log (4 * t) ≤ 2 * log t := by
    rw [two_mul, ← log_mul (by positivity) (by positivity)]
    exact log_le_log (by positivity) (by nlinarith)
  have hpos : 0 < 4 * (t : ℝ) * log (4 * t) := by positivity
  rw [theta_sub_theta (by omega)] at hθ
  calc 1 / (8 * log t) ≤ 1 / (4 * log (4 * t)) :=
        one_div_le_one_div_of_le (by positivity) (by linarith)
    _ = t / (4 * t * log (4 * t)) := by field_simp
    _ ≤ (∑ p ∈ Ioc t (4 * t) with p.Prime, log p) / (4 * t * log (4 * t)) := by gcongr
    _ = ∑ p ∈ Ioc t (4 * t) with p.Prime, log p / (4 * t * log (4 * t)) := by rw [sum_div]
    _ ≤ ∑ p ∈ Ioc t (4 * t) with p.Prime, (1 : ℝ) / p := by
        refine sum_le_sum fun p hp ↦ ?_
        simp only [mem_filter, mem_Ioc] at hp
        have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.2.pos
        have hp4 : (p : ℝ) ≤ 4 * t := by exact_mod_cast hp.1.2
        rw [div_le_div_iff₀ hpos hp0, one_mul]
        have := mul_le_mul (log_le_log hp0 hp4) hp4 hp0.le hlog4t.le
        linarith

/-- For large `X`, `1/50 ≤ ∑_{X < p ≤ X²} 1/p`. -/
lemma exists_le_sum_Ioc_sq :
    ∃ X₀ : ℕ, ∀ X ≥ X₀, (1 : ℝ) / 50 ≤ ∑ p ∈ Ioc X (X ^ 2) with p.Prime, (1 : ℝ) / p := by
  obtain ⟨t₀, ht₀⟩ := eventually_atTop.1 eventually_inv_log_le_sum_Ioc_four_mul
  refine ⟨max t₀ 16, fun X hX ↦ ?_⟩
  have hXt : t₀ ≤ X := (le_max_left _ _).trans hX
  have hX16 : 16 ≤ X := (le_max_right _ _).trans hX
  have hXr : (16 : ℝ) ≤ X := by exact_mod_cast hX16
  have hlogX : 0 < log X := log_pos (by linarith)
  set f : ℕ → ℝ := fun p ↦ if p.Prime then 1 / p else 0 with hf
  have hf0 : ∀ p, 0 ≤ f p := fun p ↦ by simp only [hf]; split_ifs <;> positivity
  -- the blocks `(4^j X, 4^{j+1} X]` with `j < J` each contribute `1 / (8 log (4^J X))`
  have hblock : ∀ J : ℕ, (J : ℝ) / (8 * log (4 ^ J * X)) ≤ ∑ p ∈ Ioc X (4 ^ J * X), f p := by
    intro J
    induction J with
    | zero => simp
    | succ J ih =>
      have hJX : X ≤ 4 ^ J * X := Nat.le_mul_of_pos_left _ (by positivity)
      have hJX' : (X : ℝ) ≤ 4 ^ J * X := by exact_mod_cast hJX
      have hlog : 0 < log ((4 : ℝ) ^ J * X) := log_pos (by linarith)
      have hmono : log ((4 : ℝ) ^ J * X) ≤ log (4 ^ (J + 1) * X) :=
        log_le_log (by positivity) (by rw [pow_succ]; nlinarith)
      have hb := ht₀ (4 ^ J * X) (hXt.trans hJX)
      rw [sum_filter, show 4 * (4 ^ J * X) = 4 ^ (J + 1) * X by ring] at hb
      push_cast at hb
      rw [← sum_Ioc_consecutive f hJX (by rw [pow_succ]; nlinarith)]
      calc ((J + 1 : ℕ) : ℝ) / (8 * log (4 ^ (J + 1) * X))
          = J / (8 * log (4 ^ (J + 1) * X)) + 1 / (8 * log (4 ^ (J + 1) * X)) := by
            push_cast; ring
        _ ≤ J / (8 * log (4 ^ J * X)) + 1 / (8 * log (4 ^ J * X)) := by gcongr
        _ ≤ _ := add_le_add ih hb
  set J := Nat.log 4 X
  have hJ₁ : 4 ^ J ≤ X := Nat.pow_log_le_self 4 (by omega)
  have hJ₂ : X < 4 ^ (J + 1) := Nat.lt_pow_succ_log_self (by norm_num) X
  have hJ1 : 1 ≤ J := by
    by_contra h
    have : J = 0 := by omega
    rw [this] at hJ₂
    omega
  have hJ : log X < (J + 1) * log 4 := by
    have h := log_lt_log (by positivity) (show (X : ℝ) < (4 : ℝ) ^ (J + 1) by exact_mod_cast hJ₂)
    rw [log_pow] at h
    push_cast at h
    exact h
  have hlog4 : log 4 < 1.4 := by
    rw [log_four_eq]
    linarith [log_two_lt_d9]
  have hJX2 : 4 ^ J * X ≤ X ^ 2 := by rw [sq]; exact Nat.mul_le_mul_right _ hJ₁
  have hJX' : (X : ℝ) ≤ 4 ^ J * X := le_mul_of_one_le_left (by positivity) (one_le_pow₀
    (by norm_num))
  have hlogJX : log ((4 : ℝ) ^ J * X) ≤ 2 * log X := by
    calc log ((4 : ℝ) ^ J * X) ≤ log ((X : ℝ) ^ 2) :=
          log_le_log (by positivity) (by exact_mod_cast hJX2)
      _ = 2 * log X := by rw [log_pow]; norm_num
  have hJ1' : (1 : ℝ) ≤ J := by exact_mod_cast hJ1
  calc (1 : ℝ) / 50 ≤ J / (16 * log X) := by
        rw [div_le_div_iff₀ (by norm_num) (by positivity)]
        nlinarith
    _ ≤ J / (8 * log (4 ^ J * X)) :=
        div_le_div_of_nonneg_left (by positivity)
          (mul_pos (by norm_num) (log_pos (by linarith))) (by linarith)
    _ ≤ ∑ p ∈ Ioc X (4 ^ J * X), f p := hblock J
    _ ≤ ∑ p ∈ Ioc X (X ^ 2), f p :=
        sum_le_sum_of_subset_of_nonneg (Ioc_subset_Ioc_right hJX2) fun p _ _ ↦ hf0 p
    _ = ∑ p ∈ Ioc X (X ^ 2) with p.Prime, (1 : ℝ) / p := by rw [hf, sum_filter]

/-- For large `X`, `I/50 ≤ ∑_{X < p ≤ X^{2^I}} 1/p`. -/
lemma exists_le_sum_Ioc_pow : ∃ X₀ : ℕ, 1 ≤ X₀ ∧ ∀ X ≥ X₀, ∀ I : ℕ,
    (I : ℝ) / 50 ≤ ∑ p ∈ Ioc X (X ^ 2 ^ I) with p.Prime, (1 : ℝ) / p := by
  obtain ⟨X₀, hX₀⟩ := exists_le_sum_Ioc_sq
  refine ⟨max X₀ 1, le_max_right _ _, fun X hX I ↦ ?_⟩
  have hX1 : 1 ≤ X := (le_max_right _ _).trans hX
  induction I with
  | zero => simp
  | succ I ih =>
    have hXY : X ≤ X ^ 2 ^ I := Nat.le_self_pow (by positivity) X
    have hY : X ^ 2 ^ I ≤ (X ^ 2 ^ I) ^ 2 := Nat.le_self_pow (by norm_num) _
    have hY₀ := hX₀ (X ^ 2 ^ I) ((le_max_left _ _).trans (hX.trans hXY))
    rw [← pow_mul, ← pow_succ] at hY₀ hY
    simp only [sum_filter] at ih hY₀ ⊢
    rw [← sum_Ioc_consecutive _ hXY hY]
    push_cast
    linarith

/-! ### Counting primes -/

/-- For large `u`, at least `u / (4 log u)` primes lie in `(u/4, u]`. -/
lemma eventually_div_log_le_card_primes :
    ∀ᶠ u : ℝ in atTop, u / (4 * log u) ≤ #{p ∈ Ioc ⌊u / 4⌋₊ ⌊u⌋₊ | p.Prime} := by
  filter_upwards [eventually_sqrt_mul_log_le (c := 1 / 100) (by norm_num),
    (tendsto_atTop_add_const_right _ 2 tendsto_id).eventually
      (eventually_log_le_const_mul (c := 1 / 200) (by norm_num)),
    eventually_ge_atTop 100] with u h1 h2 hu
  simp only [id] at h2
  have hlogu : 0 < log u := log_pos (by linarith)
  have hθ₁ := theta_ge' (x := u) (by linarith)
  have hθ₂ := theta_le_log4_mul_x (x := u / 4) (by linarith)
  have hlog4 := log_four_eq
  have hlog2 := log_two_gt_d9
  have hlog2' := log_two_lt_d9
  have hlog2u : 0.6931471803 * u ≤ log 2 * u := by gcongr
  have hfl : ⌊u / 4⌋₊ ≤ ⌊u⌋₊ := Nat.floor_le_floor (by linarith)
  have hθ : θ u - θ (u / 4) = ∑ p ∈ Ioc ⌊u / 4⌋₊ ⌊u⌋₊ with p.Prime, log p := by
    rw [theta_eq_theta_coe_floor u, theta_eq_theta_coe_floor (u / 4), theta_sub_theta hfl]
  have hsum : ∑ p ∈ Ioc ⌊u / 4⌋₊ ⌊u⌋₊ with p.Prime, log p ≤
      #{p ∈ Ioc ⌊u / 4⌋₊ ⌊u⌋₊ | p.Prime} * log u := by
    rw [← nsmul_eq_mul, ← sum_const]
    refine sum_le_sum fun p hp ↦ ?_
    simp only [mem_filter, mem_Ioc] at hp
    exact log_le_log (by exact_mod_cast hp.2.pos)
      ((Nat.cast_le.mpr hp.1.2).trans (Nat.floor_le (by linarith)))
  rw [div_le_iff₀ (by positivity)]
  nlinarith

/-- `π(m) ≤ 2 m / log m` for large `m`, so at most `2 m / log m` primes lie in `(k, m]`. -/
lemma exists_card_primes_le : ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ k : ℕ,
    (#{p ∈ Ioc k m | p.Prime} : ℝ) ≤ 2 * m / log m := by
  have h := tendsto_natCast_atTop_atTop.eventually
    (eventually_primeCounting_le (ε := 2 - log 4) (by linarith [log_four_lt_two]))
  obtain ⟨m₀, hm₀⟩ := eventually_atTop.1 h
  refine ⟨m₀, fun m hm k ↦ ?_⟩
  have hπ := hm₀ m hm
  rw [Nat.floor_natCast, add_sub_cancel] at hπ
  refine le_trans ?_ hπ
  have hsub : {p ∈ Ioc k m | p.Prime} ⊆ Nat.primesBelow (m + 1) := fun p hp ↦ by
    simp only [mem_filter, mem_Ioc] at hp
    exact Nat.mem_primesBelow.mpr ⟨by omega, hp.2⟩
  have := card_le_card hsub
  rw [Nat.primesBelow_card_eq_primeCounting'] at this
  exact_mod_cast this

/-! ### Rankin's bound for smooth numbers -/

/-- `n ↦ n^{−σ}` as a multiplicative map. -/
private noncomputable def rpowNegHom (σ : ℝ) : ℕ →* ℝ where
  toFun n := (n : ℝ) ^ (-σ)
  map_one' := by simp
  map_mul' m n := by
    push_cast
    exact mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n)

/-- `(1 − t)⁻¹ ≤ exp (4 t)` for `0 ≤ t ≤ 3/4`. -/
private lemma inv_one_sub_le_exp {t : ℝ} (ht₀ : 0 ≤ t) (ht : t ≤ 3 / 4) :
    (1 - t)⁻¹ ≤ exp (4 * t) := by
  have h1 : 0 < 1 - t := by linarith
  calc (1 - t)⁻¹ = t / (1 - t) + 1 := by field_simp; ring
    _ ≤ exp (t / (1 - t)) := add_one_le_exp _
    _ ≤ exp (4 * t) := by
        gcongr
        rw [div_le_iff₀ h1]
        nlinarith

/-- `p^{−σ} ≤ 3/4` for `p ≥ 2` and `σ ≥ 1/2`. -/
private lemma rpow_neg_le_three_quarters {p σ : ℝ} (hp : 2 ≤ p) (hσ : 1 / 2 ≤ σ) :
    p ^ (-σ) ≤ 3 / 4 := by
  calc p ^ (-σ) ≤ 2 ^ (-σ) := rpow_le_rpow_of_nonpos (by norm_num) hp (by linarith)
    _ ≤ 2 ^ (-(1 / 2) : ℝ) := rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    _ = (√2)⁻¹ := by rw [rpow_neg (by norm_num), sqrt_eq_rpow]
    _ ≤ 3 / 4 := by
        rw [inv_le_comm₀ (by positivity) (by norm_num)]
        nlinarith [sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), sqrt_nonneg 2]

/-- Rankin's bound: at most `X^σ exp (4 N^{1−σ} (1 + log N))` of the integers in `[1, X]`
are `N`-smooth, for `1/2 ≤ σ ≤ 1`. -/
theorem card_smoothNumbersUpTo_le (X N : ℕ) {σ : ℝ} (hσ : 1 / 2 ≤ σ) (hσ1 : σ ≤ 1) :
    (#(X.smoothNumbersUpTo N) : ℝ) ≤ X ^ σ * exp (4 * N ^ (1 - σ) * (1 + log N)) := by
  have hf : ∀ {p : ℕ}, p.Prime → ‖rpowNegHom σ p‖ < 1 := fun hp ↦ by
    simp only [rpowNegHom, MonoidHom.coe_mk, OneHom.coe_mk, norm_eq_abs]
    rw [abs_of_nonneg (by positivity)]
    exact rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt) (by linarith)
  obtain ⟨-, hsum⟩ :=
    EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric hf N
  -- each `n ≤ X` has `(X / n)^σ ≥ 1`
  have h₁ : (#(X.smoothNumbersUpTo N) : ℝ) ≤
      X ^ σ * ∑ n ∈ X.smoothNumbersUpTo N, (n : ℝ) ^ (-σ) := by
    rw [mul_sum, card_eq_sum_ones, Nat.cast_sum]
    refine sum_le_sum fun n hn ↦ ?_
    obtain ⟨hnX, hn⟩ := Nat.mem_smoothNumbersUpTo.mp hn
    have hn0 : (0 : ℝ) < n := by
      exact_mod_cast Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_smoothNumbers hn)
    calc ((1 : ℕ) : ℝ) = (n : ℝ) ^ σ * (n : ℝ) ^ (-σ) := by
          rw [← rpow_add hn0, add_neg_cancel, rpow_zero, Nat.cast_one]
      _ ≤ X ^ σ * (n : ℝ) ^ (-σ) := by gcongr
  -- the Euler product bounds the sum over smooth numbers
  have h₂ : ∑ n ∈ X.smoothNumbersUpTo N, (n : ℝ) ^ (-σ) ≤
      ∏ p ∈ N.primesBelow, (1 - (p : ℝ) ^ (-σ))⁻¹ := by
    have h := sum_le_hasSum ((X.smoothNumbersUpTo N).subtype (· ∈ N.smoothNumbers))
      (fun _ _ ↦ by simp only [rpowNegHom, MonoidHom.coe_mk, OneHom.coe_mk]; positivity) hsum
    rw [sum_subtype_eq_sum_filter (fun n ↦ rpowNegHom σ n),
      filter_true_of_mem fun n hn ↦ (Nat.mem_smoothNumbersUpTo.mp hn).2] at h
    simpa only [rpowNegHom, MonoidHom.coe_mk, OneHom.coe_mk] using h
  have ht : ∀ p ∈ N.primesBelow, 0 ≤ (p : ℝ) ^ (-σ) ∧ (p : ℝ) ^ (-σ) ≤ 3 / 4 := fun p hp ↦
    ⟨by positivity, rpow_neg_le_three_quarters
      (by exact_mod_cast (Nat.prime_of_mem_primesBelow hp).two_le) hσ⟩
  have h₃ : ∏ p ∈ N.primesBelow, (1 - (p : ℝ) ^ (-σ))⁻¹ ≤
      exp (4 * ∑ p ∈ N.primesBelow, (p : ℝ) ^ (-σ)) := by
    rw [mul_sum, exp_sum]
    refine prod_le_prod₀ (fun p hp ↦ inv_nonneg.mpr (by linarith [(ht p hp).2]))
      fun p hp ↦ inv_one_sub_le_exp (ht p hp).1 (ht p hp).2
  -- `n^{−σ} ≤ N^{1−σ} / n` for `n ≤ N`
  have h₄ : ∑ p ∈ N.primesBelow, (p : ℝ) ^ (-σ) ≤ N ^ (1 - σ) * (1 + log N) := by
    calc ∑ p ∈ N.primesBelow, (p : ℝ) ^ (-σ) ≤ ∑ n ∈ Icc 1 N, (n : ℝ) ^ (-σ) := by
          refine sum_le_sum_of_subset_of_nonneg (fun p hp ↦ ?_) fun _ _ _ ↦ by positivity
          have := Nat.mem_primesBelow.mp hp
          exact mem_Icc.mpr ⟨this.2.one_le, this.1.le⟩
      _ ≤ ∑ n ∈ Icc 1 N, (N : ℝ) ^ (1 - σ) * (n : ℝ)⁻¹ := by
          refine sum_le_sum fun n hn ↦ ?_
          obtain ⟨hn1, hnN⟩ := mem_Icc.mp hn
          have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
          calc (n : ℝ) ^ (-σ) = (n : ℝ) ^ (1 - σ) * (n : ℝ)⁻¹ := by
                rw [← rpow_neg_one, ← rpow_add hn0]
                ring_nf
            _ ≤ (N : ℝ) ^ (1 - σ) * (n : ℝ)⁻¹ := by gcongr
      _ = N ^ (1 - σ) * harmonic N := by
          rw [← mul_sum, harmonic_eq_sum_Icc]
          push_cast
          rfl
      _ ≤ N ^ (1 - σ) * (1 + log N) := by
          gcongr
          exact harmonic_le_one_add_log N
  calc (#(X.smoothNumbersUpTo N) : ℝ) ≤ X ^ σ * ∑ n ∈ X.smoothNumbersUpTo N, (n : ℝ) ^ (-σ) := h₁
    _ ≤ X ^ σ * exp (4 * ∑ p ∈ N.primesBelow, (p : ℝ) ^ (-σ)) := by gcongr; exact h₂.trans h₃
    _ ≤ X ^ σ * exp (4 * N ^ (1 - σ) * (1 + log N)) := by
        rw [mul_assoc 4]
        gcongr

/-- For `y = (log u)^A`, at most `u / log u` of the integers in `[1, C u]` are `y`-smooth,
for large `u`. -/
theorem eventually_card_smoothNumbersUpTo_le {A : ℕ} (hA : 1 ≤ A) {C : ℝ} (hC : 1 ≤ C) :
    ∀ᶠ u : ℝ in atTop,
      (#(⌊C * u⌋₊.smoothNumbersUpTo (⌊log u ^ A⌋₊ + 1)) : ℝ) ≤ u / log u := by
  have hA' : (1 : ℝ) ≤ A := by exact_mod_cast hA
  set ε : ℝ := 1 / (2 * A * (18 + 8 * A)) with hε
  have hε0 : 0 < ε := by positivity
  have hε' : (18 + 8 * A) * ε = 1 / (2 * A) := by
    rw [hε]
    field_simp
  have hL : ∀ᶠ L : ℝ in atTop, 3 ≤ L ∧ log C ≤ ε * L ∧ log L ≤ ε * L ∧ √L * log L ≤ ε * L :=
    (eventually_ge_atTop 3).and <|
      ((eventually_ge_atTop (log C / ε)).mono fun L hL ↦ by
        rwa [div_le_iff₀ hε0, mul_comm] at hL).and
        ((eventually_log_le_const_mul hε0).and (eventually_sqrt_mul_log_le hε0))
  filter_upwards [tendsto_log_atTop.eventually hL, eventually_gt_atTop 0] with
    u ⟨hL3, hLC, hLL, hLs⟩ hu
  set L := log u with hL_def
  set σ : ℝ := 1 - 1 / (2 * A) with hσ_def
  have hσ : 1 / 2 ≤ σ := by
    rw [hσ_def]
    have : 1 / (2 * (A : ℝ)) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) (by linarith)
    linarith
  have hσ1 : σ ≤ 1 := by
    rw [hσ_def]
    have : 0 ≤ 1 / (2 * (A : ℝ)) := by positivity
    linarith
  set N := ⌊L ^ A⌋₊ + 1 with hN_def
  have h := card_smoothNumbersUpTo_le ⌊C * u⌋₊ N hσ hσ1
  have hLA : 1 ≤ L ^ A := one_le_pow₀ (by linarith)
  have hN : (N : ℝ) ≤ 2 * L ^ A := by
    have := Nat.floor_le (by positivity : 0 ≤ L ^ A)
    rw [hN_def]
    push_cast
    linarith
  have hN1 : (1 : ℝ) ≤ N := by
    rw [hN_def]
    push_cast
    linarith [Nat.cast_nonneg (α := ℝ) ⌊L ^ A⌋₊]
  have h1σ : 1 - σ = ((2 * A : ℕ) : ℝ)⁻¹ := by
    rw [hσ_def]
    push_cast
    ring
  have hNpow : (N : ℝ) ^ (1 - σ) ≤ 2 * √L := by
    calc (N : ℝ) ^ (1 - σ) ≤ (2 * L ^ A) ^ (1 - σ) := rpow_le_rpow (by positivity) hN (by linarith)
      _ = 2 ^ (1 - σ) * (L ^ A) ^ (1 - σ) := mul_rpow (by norm_num) (by positivity)
      _ ≤ 2 * √L := by
          gcongr
          · calc (2 : ℝ) ^ (1 - σ) ≤ 2 ^ (1 : ℝ) :=
                  rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
              _ = 2 := rpow_one 2
          · rw [h1σ, show L ^ A = √L ^ (2 * A) by rw [pow_mul, sq_sqrt (by linarith)],
              pow_rpow_inv_natCast (sqrt_nonneg _) (by omega)]
  have hlogL : 1 ≤ log L := by
    rw [le_log_iff_exp_le (by linarith)]
    linarith [exp_one_lt_d9]
  have hlogN : log N ≤ 1 + A * log L := by
    calc log N ≤ log (2 * L ^ A) := log_le_log (by positivity) hN
      _ = log 2 + A * log L := by rw [log_mul (by norm_num) (by positivity), log_pow]
      _ ≤ 1 + A * log L := by linarith [log_two_lt_d9]
  have hE : 4 * (N : ℝ) ^ (1 - σ) * (1 + log N) ≤ 8 * √L * (2 + A * log L) := by
    have h₁ : 0 ≤ (N : ℝ) ^ (1 - σ) := by positivity
    have h₂ : 0 ≤ 1 + log (N : ℝ) := by linarith [log_nonneg hN1]
    have h₃ := mul_le_mul hNpow (show 1 + log (N : ℝ) ≤ 2 + A * log L by linarith) h₂
      (by positivity)
    linarith
  -- `X^σ ≤ (C u)^σ = exp (σ (log C + L))`
  have hX : ((⌊C * u⌋₊ : ℕ) : ℝ) ^ σ ≤ exp (log C + L - L / (2 * A)) := by
    have hCu : 0 < C * u := by positivity
    calc ((⌊C * u⌋₊ : ℕ) : ℝ) ^ σ ≤ (C * u) ^ σ :=
          rpow_le_rpow (by positivity) (Nat.floor_le hCu.le) (by linarith)
      _ = exp ((log C + L) * σ) := by rw [rpow_def_of_pos hCu, log_mul (by positivity) hu.ne']
      _ ≤ exp (log C + L - L / (2 * A)) := by
          gcongr
          have := log_nonneg hC
          have : log C * σ ≤ log C := mul_le_of_le_one_right this hσ1
          rw [hσ_def]
          rw [hσ_def] at this
          linarith [show (log C + L) * (1 - 1 / (2 * A)) = log C * (1 - 1 / (2 * A)) + L -
            L / (2 * A) by ring]
  have hLpos : 0 < L := by linarith
  have hfinal : log C + L - L / (2 * A) + 8 * √L * (2 + A * log L) ≤ L - log L := by
    have h₁ : √L ≤ √L * log L := le_mul_of_one_le_right (sqrt_nonneg _) hlogL
    have h₂ : A * (√L * log L) ≤ A * (ε * L) := mul_le_mul_of_nonneg_left hLs (by positivity)
    have h₃ : L / (2 * A) = (18 + 8 * A) * ε * L := by rw [hε']; ring
    nlinarith
  calc (#(⌊C * u⌋₊.smoothNumbersUpTo N) : ℝ)
      ≤ ((⌊C * u⌋₊ : ℕ) : ℝ) ^ σ * exp (4 * N ^ (1 - σ) * (1 + log N)) := h
    _ ≤ exp (log C + L - L / (2 * A)) * exp (8 * √L * (2 + A * log L)) := by gcongr
    _ = exp (log C + L - L / (2 * A) + 8 * √L * (2 + A * log L)) := (exp_add _ _).symm
    _ ≤ exp (L - log L) := exp_le_exp.mpr hfinal
    _ = u / L := by rw [exp_sub, exp_log hLpos, hL_def, exp_log hu]

end Erdos420
