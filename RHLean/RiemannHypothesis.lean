import RHLean.RhBridge
open Complex
namespace RHLean

/-- リーマン予想の最終言明 -/
theorem riemann_hypothesis_statement :
  ∀ s : ℂ, ζ s = 0 → IsOnCriticalLine s :=
by
  intro s h
  exact zeta_zero_implies_critical_line h

end RHLean
