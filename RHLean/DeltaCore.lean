import Mathlib
import RHLean.ABCDGeometry

noncomputable section

namespace RHLean
open RHLean.ABCD

/-- 幾何的Δ（原点からの二乗距離） -/
def Δgeom (R θ : ℝ) : ℝ := (Dx R θ)^2 + (Dy R θ)^2

/-- 状態（R, θ） -/
structure DeltaState where
  R : ℝ
  θ : ℝ

/-- 状態のΔ値 -/
noncomputable def DeltaState.Δ (S : DeltaState) : ℝ := Δgeom S.R S.θ

/-- ここでは有効性条件は将来拡張用のプレースホルダとして `True` にしておく。 -/
def DeltaState.Valid (_S : DeltaState) : Prop := True

/-- Δ=0 と (Dx,Dy)=(0,0) は同値 -/
theorem delta_eq_zero_iff_xy_zero (S : DeltaState) (_hV : S.Valid) :
    S.Δ = 0 ↔ (Dx S.R S.θ = 0 ∧ Dy S.R S.θ = 0) := by
  constructor
  · intro hΔ
    have hsum : (Dx S.R S.θ)^2 + (Dy S.R S.θ)^2 = 0 := by
      simpa [DeltaState.Δ, Δgeom] using hΔ
    have hx2_nonneg : 0 ≤ (Dx S.R S.θ)^2 := sq_nonneg _
    have hy2_nonneg : 0 ≤ (Dy S.R S.θ)^2 := sq_nonneg _
    have hx2_zero : (Dx S.R S.θ)^2 = 0 := by linarith
    have hy2_zero : (Dy S.R S.θ)^2 = 0 := by linarith
    exact ⟨sq_eq_zero_iff.mp hx2_zero, sq_eq_zero_iff.mp hy2_zero⟩
  · rintro ⟨hx, hy⟩
    unfold DeltaState.Δ Δgeom
    simp [hx, hy]

/-- θ=π かつ R≤1 のとき、Δ=0 は R=1/2 と同値 -/
theorem deltaAtPi_eq_zero_iff (R : ℝ) (hRle : R ≤ 1) :
    Δgeom R Real.pi = 0 ↔ R = (1 / 2 : ℝ) := by
  constructor
  · intro hΔ
    let S : DeltaState := ⟨R, Real.pi⟩
    have hS : S.Δ = 0 := by
      simpa [S, DeltaState.Δ, Δgeom] using hΔ
    have hxy : Dx S.R S.θ = 0 ∧ Dy S.R S.θ = 0 :=
      (delta_eq_zero_iff_xy_zero S (by trivial)).1 hS
    have hxy' : Dx R Real.pi = 0 ∧ Dy R Real.pi = 0 := by
      simpa [S] using hxy
    exact (origin_at_pi_iff_Rhalf R hRle).1 hxy'
  · intro hRhalf
    have hxy : Dx R Real.pi = 0 ∧ Dy R Real.pi = 0 :=
      (origin_at_pi_iff_Rhalf R hRle).2 hRhalf
    rcases hxy with ⟨hx, hy⟩
    unfold Δgeom
    simp [hx, hy]

/-- θ=π での Δ の明示式（R≤1 の領域） -/
theorem deltaAtPi_eq_dist_sq (R : ℝ) (hRle : R ≤ 1) :
    Δgeom R Real.pi = (2 * R - 1)^2 := by
  unfold Δgeom
  rw [Dx_pi R hRle, Dy_pi R]
  ring

/-- Δ は常に非負 -/
theorem delta_nonneg (R θ : ℝ) : 0 ≤ Δgeom R θ := by
  unfold Δgeom
  have h1 : 0 ≤ (Dx R θ)^2 := sq_nonneg _
  have h2 : 0 ≤ (Dy R θ)^2 := sq_nonneg _
  linarith

/-- 状態版：θ=π, R≤1 で Δ=0 ↔ R=1/2 -/
theorem deltaAtPi_state_eq_zero_iff (S : DeltaState)
    (hθ : S.θ = Real.pi) (hRle : S.R ≤ 1) :
    S.Δ = 0 ↔ S.R = (1 / 2 : ℝ) := by
  simpa [DeltaState.Δ, hθ] using (deltaAtPi_eq_zero_iff S.R hRle)

end RHLean
