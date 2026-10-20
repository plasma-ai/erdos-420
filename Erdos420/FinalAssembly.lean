import Erdos420.DivisorRatio
import Erdos420.GoodAnchor
import Erdos420.Statement

/-!
# Assembly of Erdős Problem 420: divisor counts of shifted factorials

Fix `R > 1` and a tolerance. Choose `k` with `c_k = log (1 + 1/k)` small and `m`
with `m c_k > log R`. Take a good anchor `A` from `Erdos420.exists_good_anchor`
for `g = ⌊f⌋`, and put `h₀ = g A`. For `0 ≤ e ≤ B`, `n_e = A + e − h₀` has
`⌊f n_e⌋ = h₀`, and its window `(n_e, n_e + h₀]` contains exactly the prime holes
in `(A, A + e]`, since `h₀ > B`.

By `Erdos420.exists_log_divisor_ratio_bounds`, each prime hole `k p` in the
window contributes exactly `c_k` to `log F(f, n_e)`. Every other `x` contributes
at most `bigPrimeRatio A x`, so together they contribute at most the slab tail.
The count of prime holes in `(A, A + e]` starts at `0`, reaches at least `m`, and
grows by at most one at a time. At the first `e` where `c_k` times it reaches
`log R`, `log F(f, n_e)` lies within `c_k` plus the tail and error terms of
`log R`.
-/

namespace Erdos420

open Filter Finset

/-- A prime hole `x = k p` with `p² > Y ≥ k²` gains exactly `log (1 + 1/k)`, from `p`. -/
private lemma sum_log_primeHole {k x Y : ℕ} (hk : 1 ≤ k) (hx : IsPrimeHole k x)
    (hkY : k ^ 2 ≤ Y) (hxY : k ^ 2 * (Y + 1) ≤ x ^ 2) :
    ∑ p ∈ x.primeFactors with Y < p ^ 2, Real.log (1 + p / x) = Real.log (1 + 1 / k) := by
  obtain ⟨p, hp, hkp, rfl⟩ := hx
  have hpY : Y < p ^ 2 := by
    rw [mul_pow] at hxY
    exact Nat.le_of_mul_le_mul_left hxY (by positivity)
  have hpx : p ∈ (k * p).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hp, dvd_mul_left p k, mul_ne_zero (by omega) hp.ne_zero⟩
  rw [sum_eq_single_of_mem p (mem_filter.mpr ⟨hpx, hpY⟩)]
  · have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
    push_cast
    rw [div_mul_cancel_right₀ hp0, one_div]
  -- every other prime factor divides `k`, so its square is at most `k² ≤ Y`
  · intro q hq hqp
    obtain ⟨⟨hq, hqx, -⟩, hqY⟩ := (mem_filter.mp hq).imp_left Nat.mem_primeFactors.mp
    rcases (Nat.Prime.dvd_mul hq).mp hqx with hqk | hqp'
    · have := Nat.le_of_dvd (by omega) hqk
      have := Nat.pow_le_pow_left this 2
      omega
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hq hp).mp hqp') hqp

/-- Each `x` gains at most its large-prime ratio in a window ending at `Y ≥ A`. -/
private lemma sum_log_le_bigPrimeRatio {A Y : ℕ} (hAY : A ≤ Y) (x : ℕ) :
    ∑ p ∈ x.primeFactors with Y < p ^ 2, Real.log (1 + p / x) ≤ bigPrimeRatio A x :=
  calc ∑ p ∈ x.primeFactors with Y < p ^ 2, Real.log (1 + p / x)
      ≤ ∑ p ∈ x.primeFactors with Y < p ^ 2, (p : ℝ) / x :=
        sum_le_sum fun p _ ↦ (Real.log_le_sub_one_of_pos (by positivity)).trans_eq (by ring)
    _ ≤ bigPrimeRatio A x :=
        sum_le_sum_of_subset_of_nonneg (fun p hp ↦ by
          simp only [mem_filter] at hp ⊢
          exact ⟨hp.1, hAY.trans_lt hp.2⟩) fun _ _ _ ↦ by positivity

open scoped Classical in
/-- The window `(A + e − h, A + e]`, for `e ≤ B < h ≤ A`, gains exactly `log (1 + 1/k)` from
each prime hole in `(A, A + e]`, and at most the slab tail from everything else. -/
private lemma window_sum_bounds {k B A h e : ℕ} (hk : 1 ≤ k) (heB : e ≤ B) (hBh : B < h)
    (hhA : h ≤ A) (hBA : B ≤ A) (hkA : 2 * k ^ 2 ≤ A) :
    (((Ioc A (A + e)).filter (IsPrimeHole k)).card : ℝ) * Real.log (1 + 1 / k) ≤
      ∑ x ∈ Ioc (A + e - h) (A + e), ∑ p ∈ x.primeFactors with A + e < p ^ 2,
        Real.log (1 + p / x) ∧
    ∑ x ∈ Ioc (A + e - h) (A + e), ∑ p ∈ x.primeFactors with A + e < p ^ 2,
        Real.log (1 + p / x) ≤
      (((Ioc A (A + e)).filter (IsPrimeHole k)).card : ℝ) * Real.log (1 + 1 / k) +
        slabTail k B A h := by
  rw [← sum_filter_add_sum_filter_not _ (fun x ↦ A < x ∧ IsPrimeHole k x)]
  -- the prime holes of the window are those of `(A, A + e]`, each worth `log (1 + 1/k)`
  have hholes : (Ioc (A + e - h) (A + e)).filter (fun x ↦ A < x ∧ IsPrimeHole k x) =
      (Ioc A (A + e)).filter (IsPrimeHole k) := by
    ext x
    simp only [mem_filter, mem_Ioc]
    constructor
    · rintro ⟨⟨-, hx⟩, hAx, hx'⟩
      exact ⟨⟨hAx, hx⟩, hx'⟩
    · rintro ⟨⟨hAx, hx⟩, hx'⟩
      exact ⟨⟨by omega, hx⟩, hAx, hx'⟩
  have hsum : ∑ x ∈ (Ioc A (A + e)).filter (IsPrimeHole k),
      ∑ p ∈ x.primeFactors with A + e < p ^ 2, Real.log (1 + p / x) =
        (((Ioc A (A + e)).filter (IsPrimeHole k)).card : ℝ) * Real.log (1 + 1 / k) := by
    rw [sum_congr rfl fun x hx ↦ ?_, sum_const, nsmul_eq_mul]
    obtain ⟨hx, hx'⟩ := mem_filter.mp hx
    obtain ⟨hAx, -⟩ := mem_Ioc.mp hx
    refine sum_log_primeHole hk hx' (by nlinarith) ?_
    calc k ^ 2 * (A + e + 1) ≤ k ^ 2 * (2 * A + 1) := Nat.mul_le_mul_left _ (by omega)
      _ ≤ (A + 1) ^ 2 := by nlinarith
      _ ≤ x ^ 2 := Nat.pow_le_pow_left hAx 2
  -- everything else lies in the slab and is not a prime hole of `(A, A + B]`
  have hrest₀ : 0 ≤ ∑ x ∈ (Ioc (A + e - h) (A + e)).filter
      (fun x ↦ ¬ (A < x ∧ IsPrimeHole k x)),
        ∑ p ∈ x.primeFactors with A + e < p ^ 2, Real.log (1 + p / x) :=
    sum_nonneg fun _ _ ↦ sum_nonneg fun _ _ ↦ Real.log_nonneg (by simp; positivity)
  have hrest₁ : ∑ x ∈ (Ioc (A + e - h) (A + e)).filter
      (fun x ↦ ¬ (A < x ∧ IsPrimeHole k x)),
        ∑ p ∈ x.primeFactors with A + e < p ^ 2, Real.log (1 + p / x) ≤
      slabTail k B A h :=
    calc _ ≤ ∑ x ∈ (Ioc (A + e - h) (A + e)).filter
          (fun x ↦ ¬ (A < x ∧ IsPrimeHole k x)), bigPrimeRatio A x :=
          sum_le_sum fun x _ ↦ sum_log_le_bigPrimeRatio (by omega) x
      _ ≤ slabTail k B A h := by
        refine sum_le_sum_of_subset_of_nonneg (fun x hx ↦ ?_) fun x _ _ ↦ ?_
        · simp only [mem_filter, mem_Ioc] at hx ⊢
          exact ⟨⟨by omega, by omega⟩, hx.2⟩
        · exact sum_nonneg fun _ _ ↦ by positivity
  rw [hholes, hsum]
  constructor <;> linarith

/-- If `log x` lies in `[log R, log R + η)` with `η ≤ 1`, then `|x − R| < 2 R η`. -/
private lemma abs_sub_lt_of_log {x R η : ℝ} (hx : 0 < x) (hR : 0 < R) (hη : η ≤ 1)
    (h₁ : Real.log R ≤ Real.log x) (h₂ : Real.log x < Real.log R + η) :
    |x - R| < 2 * R * η := by
  have hxR : x - R = R * (Real.exp (Real.log x - Real.log R) - 1) := by
    rw [Real.exp_sub, Real.exp_log hx, Real.exp_log hR]
    field_simp
  have hd := Real.abs_exp_sub_one_le (x := Real.log x - Real.log R)
    (by rw [abs_of_nonneg (by linarith)]; linarith)
  rw [abs_of_nonneg (show 0 ≤ Real.log x - Real.log R by linarith)] at hd
  rw [hxR, abs_mul, abs_of_pos hR]
  calc R * |Real.exp (Real.log x - Real.log R) - 1|
      ≤ R * (2 * (Real.log x - Real.log R)) := mul_le_mul_of_nonneg_left hd hR.le
    _ < R * (2 * η) := mul_lt_mul_of_pos_left (by linarith) hR
    _ = 2 * R * η := by ring

/-- Part (iii): for monotone `f ≤ log` tending to infinity, the values `F f n` with
`n ≥ N` are dense in `(1, ∞)`. -/
theorem parts_iii_proved (f : ℕ → ℝ) (hf : Monotone f)
    (hf_top : Tendsto f atTop atTop) (hf_log : ∀ᶠ n in atTop, f n ≤ Real.log n)
    (N : ℕ) : Set.Ioi 1 ⊆ closure (F f '' Set.Ici N) := by
  classical
  intro R hR
  rw [Set.mem_Ioi] at hR
  rw [Metric.mem_closure_iff]
  intro ε hε
  have hR0 : 0 < R := by linarith
  have hlogR : 0 < Real.log R := Real.log_pos hR
  -- `g = ⌊f⌋` satisfies the hypotheses of `exists_good_anchor`
  set g : ℕ → ℕ := fun n ↦ ⌊f n⌋₊
  have hg_mono : Monotone g := fun a b hab ↦ Nat.floor_mono (hf hab)
  have hg_top : Tendsto g atTop atTop := tendsto_nat_floor_atTop.comp hf_top
  have hg_log : ∀ᶠ n in atTop, (g n : ℝ) ≤ Real.log n := by
    filter_upwards [hf_log, hf_top.eventually_ge_atTop 0] with n hn h0
    exact (Nat.floor_le h0).trans hn
  -- it suffices to get `log F f n` into `[log R, log R + ε₁)`
  set ε₁ := min 1 (ε / (2 * R))
  have hε₁ : 0 < ε₁ := lt_min one_pos (by positivity)
  have hε₁R : 2 * R * ε₁ ≤ ε :=
    calc 2 * R * ε₁ ≤ 2 * R * (ε / (2 * R)) :=
          mul_le_mul_of_nonneg_left (min_le_right _ _) (by positivity)
      _ = ε := by field_simp
  -- `c = log (1 + 1/k) < ε₁ / 3`, and `m c > log R`
  obtain ⟨k', hk'⟩ := exists_nat_one_div_lt (show 0 < ε₁ / 3 by positivity)
  set k := k' + 1
  have hk : 1 ≤ k := by omega
  set c := Real.log (1 + 1 / (k : ℝ))
  have hc : 0 < c := Real.log_pos (by simp; positivity)
  have hcε : c < ε₁ / 3 :=
    calc c ≤ 1 + 1 / (k : ℝ) - 1 := Real.log_le_sub_one_of_pos (by positivity)
      _ = 1 / ((k' : ℝ) + 1) := by simp [k]
      _ < ε₁ / 3 := hk'
  obtain ⟨m, hm⟩ := exists_nat_gt (Real.log R / c)
  have hmc : Real.log R < m * c := (div_lt_iff₀ hc).mp hm
  obtain ⟨B, hB⟩ := exists_good_anchor k m hk (ε := ε₁ / 3) (by positivity)
  obtain ⟨C, hC⟩ := exists_log_divisor_ratio_bounds
  -- `(log x)² ≤ δ √x` and `2 (log x)² ≤ x` for large `x`, where `4 |C| δ ≤ ε₁ / 3`
  set δ := ε₁ / (12 * (|C| + 1))
  have hδ : 0 < δ := by positivity
  have hCδ : 4 * |C| * δ ≤ ε₁ / 3 := by
    rw [show 4 * |C| * δ = ε₁ / 3 * (|C| / (|C| + 1)) by simp only [δ]; field_simp; ring]
    exact mul_le_of_le_one_right (by positivity) ((div_le_one (by positivity)).mpr (by linarith))
  have hlo₁ : ∀ᶠ x : ℝ in atTop, Real.log x ^ 2 ≤ δ * Real.sqrt x := by
    simpa only [one_mul] using eventually_mul_log_sq_le_mul_sqrt 1 hδ
  have hlo₂ : ∀ᶠ x : ℝ in atTop, 2 * Real.log x ^ 2 ≤ x := eventually_mul_log_pow_le_self 2 2
  obtain ⟨N', hN'⟩ := eventually_atTop.mp (hg_log.and
    ((tendsto_natCast_atTop_atTop.eventually (hlo₁.and hlo₂)).and
      (eventually_ge_atTop (2 * N + 2 * k ^ 2 + B + 2))))
  -- a good anchor `A ≥ N'`, with `h₀ = g A > B` and `2 h₀² ≤ A`
  obtain ⟨A, hNA, hBh, hconst, hcnt, htail⟩ := hB g hg_mono hg_top hg_log N'
  obtain ⟨hA_log, ⟨hA₁, hA₂⟩, hA₃⟩ := hN' A hNA
  set h₀ := g A
  have hlogA : 0 ≤ Real.log A := (Nat.cast_nonneg _).trans hA_log
  have hh₀ : 2 * h₀ ^ 2 ≤ A := by
    have : (2 * h₀ ^ 2 : ℝ) ≤ A := by nlinarith
    exact_mod_cast this
  have hh₀' : 2 * h₀ ≤ A := by nlinarith
  -- `e` is the first point where `c` times the prime-hole count of `(A, A + e]` reaches `log R`
  set cnt : ℕ → ℕ := fun e ↦ ((Ioc A (A + e)).filter (IsPrimeHole k)).card
  have hcntB : Real.log R ≤ cnt B * c :=
    hmc.le.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hcnt) hc.le)
  have hex : ∃ e, Real.log R ≤ cnt e * c := ⟨B, hcntB⟩
  set e := Nat.find hex
  have heB : e ≤ B := Nat.find_min' hex hcntB
  have hlo : Real.log R ≤ cnt e * c := Nat.find_spec hex
  have hhi : cnt e * c < Real.log R + c := by
    have he0 : e ≠ 0 := by
      intro h0
      rw [h0] at hlo
      simp [cnt] at hlo
      linarith
    obtain ⟨e', he'⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
    have hlt : ¬ Real.log R ≤ cnt e' * c := Nat.find_min hex (by omega)
    have hstep : cnt e ≤ cnt e' + 1 := by
      rw [he']
      refine (card_le_card fun x hx ↦ ?_).trans (card_insert_le (A + (e' + 1)) _)
      simp only [mem_filter, mem_Ioc, mem_insert] at hx ⊢
      rcases (show x = A + (e' + 1) ∨ x ≤ A + e' by omega) with hx' | hx'
      · exact Or.inl hx'
      · exact Or.inr ⟨⟨hx.1.1, hx'⟩, hx.2⟩
    have : (cnt e : ℝ) ≤ cnt e' + 1 := by exact_mod_cast hstep
    nlinarith
  -- `n = A + e − h₀` has `⌊f n⌋ = h₀` and window `(n, A + e]`
  have hnh : A + e - h₀ + h₀ = A + e := by omega
  have hgn : g (A + e - h₀) = h₀ := hconst _ (mem_Icc.mpr ⟨by omega, by omega⟩)
  have hn₂ : h₀ ^ 2 ≤ A + e - h₀ := by omega
  have hn₁ : 1 ≤ A + e - h₀ := by nlinarith
  obtain ⟨hlow, hupp⟩ := hC (A + e - h₀) h₀ hn₁ hn₂
  rw [hnh] at hlow hupp
  obtain ⟨hS₁, hS₂⟩ :=
    window_sum_bounds (A := A) hk heB hBh (by omega) (by omega) (by omega)
  -- the error term is at most `4 |C| δ ≤ ε₁ / 3`
  have herr : C * h₀ * Real.log ((A + e - h₀ : ℕ) + h₀) / Real.sqrt (A + e - h₀ : ℕ) ≤
      ε₁ / 3 := by
    have hn : (A : ℝ) ≤ 2 * (A + e - h₀ : ℕ) := by
      have : A ≤ 2 * (A + e - h₀) := by omega
      exact_mod_cast this
    have hsn : 0 < Real.sqrt (A + e - h₀ : ℕ) := Real.sqrt_pos.mpr (by exact_mod_cast hn₁)
    have hsA : Real.sqrt A ≤ 2 * Real.sqrt (A + e - h₀ : ℕ) :=
      calc Real.sqrt A ≤ Real.sqrt ((2 * Real.sqrt (A + e - h₀ : ℕ)) ^ 2) :=
            Real.sqrt_le_sqrt (by rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]; linarith)
        _ = 2 * Real.sqrt (A + e - h₀ : ℕ) := Real.sqrt_sq (by positivity)
    have hL : Real.log ((A + e - h₀ : ℕ) + h₀) ≤ 2 * Real.log A := by
      have : ((A + e - h₀ : ℕ) : ℝ) + h₀ ≤ (A : ℝ) ^ 2 := by
        have : A + e ≤ A ^ 2 := by nlinarith
        exact_mod_cast hnh ▸ this
      calc Real.log ((A + e - h₀ : ℕ) + h₀) ≤ Real.log ((A : ℝ) ^ 2) :=
            Real.log_le_log (by positivity) this
        _ = 2 * Real.log A := by rw [Real.log_pow]; norm_num
    have hL₀ : 0 ≤ Real.log ((A + e - h₀ : ℕ) + h₀) := Real.log_nonneg (by
      have : (1 : ℝ) ≤ (A + e - h₀ : ℕ) := by exact_mod_cast hn₁
      linarith [(Nat.cast_nonneg h₀ : (0 : ℝ) ≤ h₀)])
    rw [div_le_iff₀ hsn]
    calc C * h₀ * Real.log ((A + e - h₀ : ℕ) + h₀)
        ≤ |C| * Real.log A * (2 * Real.log A) :=
          mul_le_mul (mul_le_mul (le_abs_self C) hA_log (Nat.cast_nonneg _) (abs_nonneg C)) hL
            hL₀ (mul_nonneg (abs_nonneg C) hlogA)
      _ = 2 * |C| * Real.log A ^ 2 := by ring
      _ ≤ 2 * |C| * (δ * Real.sqrt A) := mul_le_mul_of_nonneg_left hA₁ (by positivity)
      _ ≤ 2 * |C| * (δ * (2 * Real.sqrt (A + e - h₀ : ℕ))) := by gcongr
      _ = 4 * |C| * δ * Real.sqrt (A + e - h₀ : ℕ) := by ring
      _ ≤ ε₁ / 3 * Real.sqrt (A + e - h₀ : ℕ) := mul_le_mul_of_nonneg_right hCδ hsn.le
  -- `F f n` is the divisor ratio of the window, so `log F f n ∈ [log R, log R + ε₁)`
  have hF : F f (A + e - h₀) = ((A + e).factorial.divisors.card : ℝ) /
      (A + e - h₀).factorial.divisors.card := by
    rw [F, show ⌊f (A + e - h₀)⌋₊ = h₀ from hgn, hnh]
  have hF₀ : 0 < F f (A + e - h₀) := by
    rw [hF]
    exact div_pos
      (Nat.cast_pos.mpr (card_pos.mpr (Nat.nonempty_divisors.mpr (Nat.factorial_ne_zero _))))
      (Nat.cast_pos.mpr (card_pos.mpr (Nat.nonempty_divisors.mpr (Nat.factorial_ne_zero _))))
  have hlog₁ : Real.log R ≤ Real.log (F f (A + e - h₀)) := by
    rw [hF]
    linarith
  have hlog₂ : Real.log (F f (A + e - h₀)) < Real.log R + ε₁ := by
    rw [hF]
    linarith
  refine ⟨F f (A + e - h₀), ⟨A + e - h₀, Set.mem_Ici.mpr (by omega), rfl⟩, ?_⟩
  rw [Real.dist_eq, abs_sub_comm]
  exact (abs_sub_lt_of_log hF₀ hR0 (min_le_left _ _) hlog₁ hlog₂).trans_le hε₁R

/-- Part (ii): `F(log n, n)` is dense in `(1, ∞)`. -/
theorem parts_ii_proved : Set.Ioi 1 ⊆ closure (Set.range (F fun n ↦ Real.log n)) := by
  refine (parts_iii_proved _ ?_ ?_ (Eventually.of_forall fun n ↦ le_rfl) 0).trans
    (closure_mono (Set.image_subset_range _ _))
  -- `log` is monotone on `ℕ`, with `log 0 = 0`
  · intro a b hab
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · simpa using Real.log_natCast_nonneg b
    · exact Real.log_le_log (by exact_mod_cast ha) (by exact_mod_cast hab)
  · exact tendsto_log_natCast_atTop

end Erdos420
