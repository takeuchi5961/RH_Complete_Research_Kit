import RHLean.CriticalLineBridge
import RHLean.DeltaCore

noncomputable section
namespace RHLean

/-- 解析側: 臨界線上での零点述語 -/
def ZeroOnCritical (zeta : ℂ → ℂ) : Prop :=
  ∀ t : ℝ, zeta (sOnCritical t) = 0

/-- 幾何側: Δ=0述語 -/
def DeltaZero (Δ : ℝ → ℝ) : Prop :=
  ∀ t : ℝ, Δ t = 0

/--
`Δ(t)=0 ↔ ζ(1/2+it)=0` の点ごとの橋渡しが与えられれば、
全体の述語同値に持ち上がる。

※ 「mod 2π」相当の議論は `hbridge` の中身として明示する。
-/
theorem delta_zero_mod2pi_iff_zero_on_critical
    (zeta : ℂ → ℂ) (Δ : ℝ → ℝ)
    (hbridge : ∀ t : ℝ, (Δ t = 0) ↔ (zeta (sOnCritical t) = 0)) :
    DeltaZero Δ ↔ ZeroOnCritical zeta := by
  constructor
  · intro hΔ t
    exact (hbridge t).1 (hΔ t)
  · intro hz t
    exact (hbridge t).2 (hz t)

/-- 一点版（実務でよく使う） -/
theorem delta_zero_iff_zero_at_t
    (zeta : ℂ → ℂ) (Δ : ℝ → ℝ)
    (hbridge : ∀ t : ℝ, (Δ t = 0) ↔ (zeta (sOnCritical t) = 0))
    (t : ℝ) :
    (Δ t = 0) ↔ (zeta (sOnCritical t) = 0) :=
  hbridge t

end RHLean
