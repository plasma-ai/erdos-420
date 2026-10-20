/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.NumberTheory.Chebyshev


/-!
# Prime Number Theorem

The estimate `π(N) = N / log N + O(N / (log N) ^ 2)`, recorded as the hypothesis
`PNT.PrimeCountingEstimate` and threaded to the main sieve theorems. Upstream proves it from Alex
Kontorovich's library `PrimeNumberTheoremAnd`; here it is discharged by the user of the library.
-/

@[expose] public section

open Nat Real Filter Asymptotics
open scoped Chebyshev

namespace PNT

/-- The prime number theorem in the form `π(N) = N/log N + O(N/(log N)^2)` as `N → ∞`. -/
def PrimeCountingEstimate : Prop :=
  ∃ (C : ℝ) (N₀ : ℕ), ∀ N ≥ N₀, |primeCounting N - N / Real.log N| ≤ C * N / Real.log N ^ 2

end PNT
