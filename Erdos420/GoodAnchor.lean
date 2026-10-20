import Erdos420.SlabWeights

/-!
# An anchor with many prime holes and a small slab tail

Let `g = ⌊f⌋` be monotone, tend to infinity, and satisfy `g n ≤ log n`
eventually. Take the weights of `Erdos420.exists_slab_weights` with tail
tolerance `η = γ ε / (4 (B + 1))`. Discard two kinds of anchors:
- anchors whose slab `[A_t − H, A_t + B]` meets a jump of `g`. The slabs overlap
  at most `H + B = O(log X)` deep, and `g` rises by at most `2 log X` across
  them, so these anchors carry weight `O(log² X)`, against a total of at least
  `√X`;
- anchors with slab tail above `ε`, which carry weight at most `γ / (4 (B + 1))`
  of the total, by Markov's inequality.

Each anchor has at most `B` prime holes, so discarding these anchors keeps a
positive surplus. Some remaining anchor therefore has at least `m` prime holes.
-/

namespace Erdos420

open Filter Finset

/-- Windows `[A t − H, A t + B]` with distinct `A t ∈ [X, Y]` overlap at most `H + B` deep,
so the increments of a monotone `G` over them total at most `(H + B) (G (Y + B) − G (X − H))`. -/
private lemma sum_window_increment_le {G : ℕ → ℝ} (hG : Monotone G) {T : Finset ℕ} {A : ℕ → ℕ}
    (hA : Set.InjOn A T) {X Y H B : ℕ} (hXY : X ≤ Y) (hAX : ∀ t ∈ T, X ≤ A t ∧ A t ≤ Y) :
    ∑ t ∈ T, (G (A t + B) - G (A t - H)) ≤ (H + B) * (G (Y + B) - G (X - H)) := by
  have hstep : ∀ j, 0 ≤ G (j + 1) - G j := fun j ↦ sub_nonneg.2 (hG (Nat.le_succ j))
  calc ∑ t ∈ T, (G (A t + B) - G (A t - H))
      -- each increment telescopes over the steps `j ∈ [A t − H, A t + B)`
      = ∑ t ∈ T, ∑ j ∈ Ico (A t - H) (A t + B), (G (j + 1) - G j) :=
        sum_congr rfl fun t _ ↦ (sum_Ico_sub G (by omega)).symm
    _ = ∑ j ∈ Ico (X - H) (Y + B), ∑ t ∈ T with j ∈ Ico (A t - H) (A t + B),
          (G (j + 1) - G j) := by
        refine sum_comm' fun t j ↦ ?_
        simp only [mem_filter, mem_Ico]
        constructor
        · rintro ⟨ht, hj⟩
          have := hAX t ht
          exact ⟨⟨ht, hj⟩, by omega, by omega⟩
        · rintro ⟨⟨ht, hj⟩, _⟩
          exact ⟨ht, hj⟩
    _ ≤ ∑ j ∈ Ico (X - H) (Y + B), (H + B) * (G (j + 1) - G j) := by
        refine sum_le_sum fun j _ ↦ ?_
        rw [sum_const, nsmul_eq_mul]
        refine mul_le_mul_of_nonneg_right ?_ (hstep j)
        -- the `t` whose window contains `j` have distinct `A t ∈ [j + 1 − B, j + H]`
        have hcard : #{t ∈ T | j ∈ Ico (A t - H) (A t + B)} ≤ #(Icc (j + 1 - B) (j + H)) :=
          card_le_card_of_injOn A (fun t ht ↦ by
            simp only [coe_filter, Set.mem_ofPred_eq, mem_Ico] at ht
            simp only [coe_Icc, Set.mem_Icc]
            omega) (hA.mono (coe_subset.2 (filter_subset _ _)))
        rw [Nat.card_Icc] at hcard
        exact_mod_cast hcard.trans (by omega)
    _ = (H + B) * (G (Y + B) - G (X - H)) := by rw [← mul_sum, sum_Ico_sub G (by omega)]

open scoped Classical in
/-- Arbitrarily large anchors `A` at which `g` is constant on `[A − g A, A + B]`,
with at least `m` prime holes in `(A, A + B]` and slab tail at most `ε`. -/
theorem exists_good_anchor (k m : ℕ) (hk : 1 ≤ k) {ε : ℝ} (hε : 0 < ε) :
    ∃ B : ℕ, ∀ g : ℕ → ℕ, Monotone g → Tendsto g atTop atTop →
      (∀ᶠ n in atTop, (g n : ℝ) ≤ Real.log n) → ∀ N : ℕ, ∃ A, N ≤ A ∧ B < g A ∧
        (∀ n ∈ Icc (A - g A) (A + B), g n = g A) ∧
        m ≤ ((Ioc A (A + B)).filter (IsPrimeHole k)).card ∧
        slabTail k B A (g A) ≤ ε := by
  obtain ⟨B, γ, hγ, C, hW⟩ := exists_slab_weights k m hk
  refine ⟨B, fun g hg hgt hglog N ↦ ?_⟩
  set δ := γ / (4 * (B + 1)) with hδ_def
  have hδ : 0 < δ := by positivity
  set C' := max C 0
  have hC' : 0 ≤ C' := le_max_right _ _
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.1 (hgt.eventually_gt_atTop B)
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.1 hglog
  obtain ⟨X, ⟨T, A, W, hA, hAX, hW0, hWC, hWsq, hγW, hηW⟩, hXN, hXN₁, hXN₂, hXkB, hXlog, hXsq⟩ :=
    ((hW (δ * ε) (by positivity)).and <| (eventually_ge_atTop N).and <|
      (eventually_ge_atTop N₁).and <| (eventually_ge_atTop N₂).and <|
      (eventually_ge_atTop (8 * k + B + 1)).and <|
      (tendsto_log_natCast_atTop.eventually_ge_atTop ((B : ℝ) + 1)).and <|
      tendsto_natCast_atTop_atTop.eventually (eventually_mul_log_sq_le_mul_sqrt (6 * C') hδ)).exists
  set H := ⌈Real.log (8 * k * X)⌉₊
  set S := ∑ t ∈ T, W t
  have hX0 : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  have hS : 0 < S := (Real.sqrt_pos.2 hX0).trans_le hWsq
  have hX8 : X ≤ 8 * k * X := Nat.le_mul_of_pos_left X (by omega)
  -- the slab and its end points are below `X²`, so their logarithms are below `2 log X`
  have hXX : 8 * k * X + B ≤ X * X := by nlinarith
  have hlogkX : Real.log (8 * k * X) ≤ 2 * Real.log X := by
    rw [two_mul, ← Real.log_mul (by positivity) (by positivity)]
    refine Real.log_le_log (by positivity) ?_
    exact_mod_cast (Nat.le_add_right _ _).trans hXX
  have hlogkXB : Real.log ((8 * k * X + B : ℕ) : ℝ) ≤ 2 * Real.log X := by
    rw [two_mul, ← Real.log_mul (by positivity) (by positivity)]
    exact Real.log_le_log (by exact_mod_cast (by omega : 0 < 8 * k * X + B))
      (by exact_mod_cast hXX)
  have hHB : (H + B : ℝ) ≤ 3 * Real.log X := by
    have hlog0 : 0 ≤ Real.log (8 * k * X) :=
      Real.log_nonneg (by exact_mod_cast (by nlinarith : 1 ≤ 8 * k * X))
    linarith [Nat.ceil_lt_add_one hlog0]
  -- anchors whose slab meets a jump of `g` carry weight `O(log² X)`
  set G : ℕ → ℝ := fun j ↦ (g j : ℝ) with hG_def
  have hG : Monotone G := fun _ _ hab ↦ Nat.cast_le.2 (hg hab)
  have hjump : ∑ t ∈ T with g (A t - H) < g (A t + B), W t ≤ δ * S := by
    calc ∑ t ∈ T with g (A t - H) < g (A t + B), W t
        ≤ ∑ t ∈ T with g (A t - H) < g (A t + B), C' * (G (A t + B) - G (A t - H)) := by
          refine sum_le_sum fun t ht ↦ ?_
          have h1 : (1 : ℝ) ≤ G (A t + B) - G (A t - H) := by
            have : g (A t - H) + 1 ≤ g (A t + B) := (mem_filter.1 ht).2
            have : (g (A t - H) : ℝ) + 1 ≤ g (A t + B) := by exact_mod_cast this
            simp only [hG_def]
            linarith
          calc W t ≤ C' := (hWC t (mem_filter.1 ht).1).trans (le_max_left _ _)
            _ ≤ C' * (G (A t + B) - G (A t - H)) := le_mul_of_one_le_right hC' h1
      _ ≤ ∑ t ∈ T, C' * (G (A t + B) - G (A t - H)) :=
          sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun t _ _ ↦
            mul_nonneg hC' (sub_nonneg.2 (hG (by omega)))
      _ ≤ C' * ((H + B) * (G (8 * k * X + B) - G (X - H))) := by
          rw [← mul_sum]
          exact mul_le_mul_of_nonneg_left (sum_window_increment_le hG hA hX8 hAX) hC'
      _ ≤ C' * ((3 * Real.log X) * (2 * Real.log X)) := by
          have hGY : G (8 * k * X + B) - G (X - H) ≤ 2 * Real.log X := by
            have := hN₂ (8 * k * X + B) (by nlinarith)
            have : 0 ≤ G (X - H) := Nat.cast_nonneg _
            simp only [hG_def] at *
            linarith
          refine mul_le_mul_of_nonneg_left (mul_le_mul hHB hGY ?_ (by linarith)) hC'
          exact sub_nonneg.2 (hG (by omega))
      _ = 6 * C' * Real.log X ^ 2 := by ring
      _ ≤ δ * Real.sqrt X := hXsq
      _ ≤ δ * S := mul_le_mul_of_nonneg_left hWsq hδ.le
  -- anchors with slab tail above `ε` carry weight at most `δ S`, by Markov's inequality
  have htail : ∑ t ∈ T with ε < slabTail k B (A t) H, W t ≤ δ * S := by
    refine le_of_mul_le_mul_left ?_ hε
    calc ε * ∑ t ∈ T with ε < slabTail k B (A t) H, W t
        = ∑ t ∈ T with ε < slabTail k B (A t) H, W t * ε := by
          rw [mul_sum]
          exact sum_congr rfl fun _ _ ↦ mul_comm _ _
      _ ≤ ∑ t ∈ T with ε < slabTail k B (A t) H, W t * slabTail k B (A t) H :=
          sum_le_sum fun t ht ↦ mul_le_mul_of_nonneg_left (mem_filter.1 ht).2.le (hW0 t)
      _ ≤ ∑ t ∈ T, W t * slabTail k B (A t) H :=
          sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun t _ _ ↦
            mul_nonneg (hW0 t) (slabTail_nonneg _ _ _ _)
      _ ≤ δ * ε * S := hηW
      _ = ε * (δ * S) := by ring
  -- each anchor has surplus at most `B + 1`, so some anchor avoiding both kinds has a
  -- positive surplus
  obtain ⟨t, ht, hjt, htt, hpos⟩ : ∃ t ∈ T, ¬ g (A t - H) < g (A t + B) ∧
      ¬ ε < slabTail k B (A t) H ∧
      0 < W t * ((((Ioc (A t) (A t + B)).filter (IsPrimeHole k)).card : ℝ) - (m - 1)) := by
    by_contra! hbad
    have hD : ∀ t ∈ T,
        W t * ((((Ioc (A t) (A t + B)).filter (IsPrimeHole k)).card : ℝ) - (m - 1)) ≤
          (B + 1) * ((if g (A t - H) < g (A t + B) then W t else 0) +
            (if ε < slabTail k B (A t) H then W t else 0)) := by
      intro t ht
      have hcard : (((Ioc (A t) (A t + B)).filter (IsPrimeHole k)).card : ℝ) ≤ B := by
        exact_mod_cast (card_filter_le _ _).trans (by simp)
      have hsur : W t * ((((Ioc (A t) (A t + B)).filter (IsPrimeHole k)).card : ℝ) - (m - 1)) ≤
          W t * (B + 1) :=
        mul_le_mul_of_nonneg_left (by linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]) (hW0 t)
      have hWB : 0 ≤ W t * (B + 1) := mul_nonneg (hW0 t) (by positivity)
      split_ifs with h1 h2 h2
      · linarith
      · linarith
      · linarith
      · simpa using hbad t ht (not_lt.1 h1) (not_lt.1 h2)
    have hsum := hγW.trans (sum_le_sum hD)
    rw [← mul_sum, sum_add_distrib, ← sum_filter, ← sum_filter] at hsum
    have h2 := mul_le_mul_of_nonneg_left (add_le_add hjump htail) (by positivity : (0 : ℝ) ≤ B + 1)
    have h3 : (B + 1 : ℝ) * (δ * S + δ * S) = γ * S / 2 := by
      rw [hδ_def]
      field_simp
      ring
    linarith [mul_pos hγ hS]
  have hAt := hAX t ht
  -- `g (A t) ≤ log (A t) ≤ log (8 k X) ≤ H`
  have hgA : g (A t) ≤ H := by
    have h1 : (g (A t) : ℝ) ≤ Real.log (A t) := hN₂ _ (by omega)
    have h2 : Real.log (A t) ≤ Real.log (8 * k * X) :=
      Real.log_le_log (by exact_mod_cast (by omega : 0 < A t)) (by exact_mod_cast hAt.2)
    exact Nat.cast_le.1 (h1.trans (h2.trans (Nat.le_ceil _)))
  refine ⟨A t, by omega, hN₁ _ (by omega), fun n hn ↦ ?_, ?_,
    (slabTail_mono k B (A t) hgA).trans (not_lt.1 htt)⟩
  · -- `g` is constant on `[A t − H, A t + B]`, which contains `[A t − g (A t), A t + B]`
    rw [mem_Icc] at hn
    have h1 := hg (show A t - H ≤ n by omega)
    have h2 := hg (show n ≤ A t + B by omega)
    have h3 := hg (show A t - H ≤ A t by omega)
    have h4 := hg (show A t ≤ A t + B by omega)
    omega
  · -- a positive surplus means more than `m − 1` prime holes
    have := pos_of_mul_pos_right hpos (hW0 t)
    have : (m : ℝ) < ((Ioc (A t) (A t + B)).filter (IsPrimeHole k)).card + 1 := by linarith
    have : m < ((Ioc (A t) (A t + B)).filter (IsPrimeHole k)).card + 1 := by exact_mod_cast this
    omega

end Erdos420
