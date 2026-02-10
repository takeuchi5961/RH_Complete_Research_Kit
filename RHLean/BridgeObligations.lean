import Mathlib
import RHLean.ZetaABCDBridge

noncomputable section
namespace RHLean

def H1 (zeta : ℂ → ℂ) (PhiR : ℂ → ℝ) : Prop :=
  ∀ s : ℂ, zeta s = 0 → GeoZero PhiR s

def H2 (zeta : ℂ → ℂ) (PhiR : ℂ → ℝ) : Prop :=
  ∀ s : ℂ, GeoZero PhiR s → zeta s = 0

theorem bridge_forward
    (zeta : ℂ → ℂ) (PhiR : ℂ → ℝ) :
    (H1 zeta PhiR ∧ H2 zeta PhiR) →
    (∀ t : ℝ, zeta (sOnCritical t) = 0 ↔ GeoZero PhiR (sOnCritical t)) := by
  intro h t
  exact zeta_zero_iff_geo_zero_on_critical zeta PhiR h.1 h.2 t

theorem bridge_reverse_with_cover
    (zeta : ℂ → ℂ) (PhiR : ℂ → ℝ)
    (hcover : ∀ s : ℂ, ∃ t : ℝ, s = sOnCritical t) :
    (∀ t : ℝ, zeta (sOnCritical t) = 0 ↔ GeoZero PhiR (sOnCritical t)) →
    (H1 zeta PhiR ∧ H2 zeta PhiR) := by
  intro h
  constructor
  · intro s hs
    rcases hcover s with ⟨t, rfl⟩
    exact (h t).1 hs
  · intro s hs
    rcases hcover s with ⟨t, rfl⟩
    exact (h t).2 hs

end RHLean
