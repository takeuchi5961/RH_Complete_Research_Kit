import Mathlib
import RHLean.DeltaCore

noncomputable section

namespace RHLean
open RHLean.ABCD

/-- R∈[0,1] で R≠1/2 なら、θ=π の Δ は正。 -/
theorem delta_at_pi_positive_if_R_ne_half (R : ℝ)
    (hR : 0 ≤ R ∧ R ≤ 1) (hRneq : R ≠ (1 / 2 : ℝ)) :
    0 < Δgeom R Real.pi := by
  have hneq0 : Δgeom R Real.pi ≠ 0 := by
    intro h0
    have hhalf : R = (1 / 2 : ℝ) := (deltaAtPi_eq_zero_iff R hR.2).1 h0
    exact hRneq hhalf
  have hnonneg : 0 ≤ Δgeom R Real.pi := delta_nonneg R Real.pi
  exact lt_of_le_of_ne hnonneg (Ne.symm hneq0)

/-- R∈[0,1] で R≠1/2 なら、(2R-1)^2 は正（=Δ(π)）。 -/
theorem delta_lower_bound_by_distance_to_half (R : ℝ)
    (_hR0 : 0 ≤ R) (_hRle : R ≤ 1) (hRneq : R ≠ (1 / 2 : ℝ)) :
    0 < (2 * R - 1)^2 := by
  have hneq : 2 * R - 1 ≠ 0 := by
    intro hz
    apply hRneq
    linarith
  have hsq : 0 ≤ (2 * R - 1)^2 := pow_two_nonneg (2 * R - 1)
  exact lt_of_le_of_ne hsq (Ne.symm (pow_ne_zero 2 hneq))

end RHLean