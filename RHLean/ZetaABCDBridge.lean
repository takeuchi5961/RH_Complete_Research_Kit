import Mathlib
import RHLean.ABCDGeometry

noncomputable section

namespace RHLean

open RHLean.ABCD

-- 臨界線上の点 s = 1/2 + i t
def sOnCritical (t : ℝ) : ℂ := (1 / 2 : ℂ) + (t : ℂ) * Complex.I

def GeoZero (PhiR : ℂ → ℝ) (s : ℂ) : Prop :=
  (ABCD.Dx (PhiR s) Real.pi = 0) ∧ (ABCD.Dy (PhiR s) Real.pi = 0)

theorem zeta_zero_iff_geo_zero_on_critical
    (zeta : ℂ → ℂ) (PhiR : ℂ → ℝ)
    (hzg : ∀ s : ℂ, zeta s = 0 → GeoZero PhiR s)
    (hgz : ∀ s : ℂ, GeoZero PhiR s → zeta s = 0)
    (t : ℝ) :
    zeta (sOnCritical t) = 0 ↔ GeoZero PhiR (sOnCritical t) := by
  constructor
  · intro hz
    exact hzg (sOnCritical t) hz
  · intro hg
    exact hgz (sOnCritical t) hg

end RHLean
