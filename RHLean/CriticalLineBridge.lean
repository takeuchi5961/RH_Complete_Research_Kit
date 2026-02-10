import Mathlib
import RHLean.ZetaABCDBridge

noncomputable section
namespace RHLean

def H1_onCL (zeta : ℂ → ℂ) (PhiR : ℂ → ℝ) : Prop :=
  ∀ t : ℝ, zeta (sOnCritical t) = 0 → GeoZero PhiR (sOnCritical t)

def H2_onCL (zeta : ℂ → ℂ) (PhiR : ℂ → ℝ) : Prop :=
  ∀ t : ℝ, GeoZero PhiR (sOnCritical t) → zeta (sOnCritical t) = 0

theorem bridge_onCL_iff
    (zeta : ℂ → ℂ) (PhiR : ℂ → ℝ) :
    (H1_onCL zeta PhiR ∧ H2_onCL zeta PhiR) ↔
    (∀ t : ℝ, zeta (sOnCritical t) = 0 ↔ GeoZero PhiR (sOnCritical t)) := by
  constructor
  · intro h t
    constructor
    · exact h.1 t
    · exact h.2 t
  · intro h
    constructor
    · intro t hz
      exact (h t).1 hz
    · intro t hg
      exact (h t).2 hg

end RHLean
