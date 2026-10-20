import Erdos420.Analytic.QuasiRH

/-!
# Zero-free strips for primitive Dirichlet L-functions

The functional equation reflects the seven-eighths half-plane of
`Erdos420.LFunction_ne_zero_of_seven_eighths_lt_re` to the strip
`0 < re s < 1 / 8`. This includes the Riemann zeta function, the L-function of the
primitive character mod `1`.
-/

namespace Erdos420

open DirichletCharacter

/-- A primitive Dirichlet L-function does not vanish in `0 < re s < 1 / 8`. -/
theorem LFunction_ne_zero_of_re_lt_one_eighth {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) {s : ℂ}
    (hs₀ : 0 < s.re) (hs₁ : s.re < 1 / 8) : LFunction χ s ≠ 0 := by
  intro hL
  -- the gamma factor is nonzero to the right of zero
  have hΓ : gammaFactor χ s ≠ 0 := by
    rcases χ.even_or_odd with hev | hodd
    · rw [hev.gammaFactor_def]
      exact Complex.Gammaℝ_ne_zero_of_re_pos hs₀
    · rw [hodd.gammaFactor_def]
      exact Complex.Gammaℝ_ne_zero_of_re_pos (by simp; linarith)
  -- so the completed L-function vanishes at `s`
  have hΛ : completedLFunction χ s = 0 := by
    rw [LFunction_eq_completed_div_gammaFactor χ s (Or.inl (by rintro rfl; simp at hs₀)),
      div_eq_zero_iff] at hL
    exact hL.resolve_right hΓ
  -- the functional equation for `χ⁻¹` reflects the zero to `1 - s`
  have hχinv : χ⁻¹.IsPrimitive := by
    rwa [IsPrimitive, conductor_inv]
  have hΛ' : completedLFunction χ⁻¹ (1 - s) = 0 := by
    rw [hχinv.completedLFunction_one_sub, inv_inv, hΛ, mul_zero]
  have hL' : LFunction χ⁻¹ (1 - s) = 0 := by
    rw [LFunction_eq_completed_div_gammaFactor χ⁻¹ (1 - s)
      (Or.inl (by intro h; have := congrArg Complex.re h; simp at this; linarith)), hΛ',
      zero_div]
  -- this contradicts the seven-eighths zero-free half-plane
  refine LFunction_ne_zero_of_seven_eighths_lt_re χ⁻¹ (s := 1 - s) (by simp; linarith)
    (fun h ↦ by have := congrArg Complex.re h.2; simp at this; linarith) hL'

end Erdos420
