import Erdos420.FinalAssembly

/-!
# Proof of Erdős Problem 420: divisor counts of shifted factorials

Comparator checks the two theorems in this module against the Mathlib-only
statements in `Challenge.lean`.
-/

open Filter

namespace Erdos420

/-- If `f` is monotone, tends to infinity, and is eventually at most `log n`,
then for every `N` the values `F f n` with `n ≥ N` are dense in `(1, ∞)`. -/
theorem erdos_420.parts.iii (f : ℕ → ℝ) (hf : Monotone f)
    (hf_top : Tendsto f atTop atTop) (hf_log : ∀ᶠ n in atTop, f n ≤ Real.log n)
    (N : ℕ) : Set.Ioi 1 ⊆ closure (F f '' Set.Ici N) :=
  parts_iii_proved f hf hf_top hf_log N

/-- `F(log n, n)` is dense in `(1, ∞)`. -/
theorem erdos_420.parts.ii :
    Set.Ioi 1 ⊆ closure (Set.range (F fun n ↦ Real.log n)) :=
  parts_ii_proved

end Erdos420
