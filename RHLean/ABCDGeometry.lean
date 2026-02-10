import Mathlib

noncomputable section

namespace RHLean
namespace ABCD

structure Point where
  x : ℝ
  y : ℝ

def A (R : ℝ) : Point := ⟨-R, 0⟩
def B (R : ℝ) : Point := ⟨R, 0⟩
def C (cY : ℝ) : Point := ⟨0, cY⟩

def BD (R : ℝ) : ℝ := |1 - R|

-- D = B + |BD| e^{-iθ} の実座標展開
def Dx (R θ : ℝ) : ℝ := (B R).x + BD R * Real.cos (-θ)
def Dy (R θ : ℝ) : ℝ := (B R).y + BD R * Real.sin (-θ)

def D (R θ : ℝ) : Point := ⟨Dx R θ, Dy R θ⟩

theorem twin_AB (R : ℝ) : (A R).x = - (B R).x ∧ (A R).y = (B R).y := by
  constructor <;> simp [A, B]

theorem BD_eq_one_sub (R : ℝ) (hRle : R ≤ 1) : BD R = 1 - R := by
  unfold BD
  exact abs_of_nonneg (sub_nonneg.mpr hRle)

theorem Dx_pi (R : ℝ) (hRle : R ≤ 1) : Dx R Real.pi = 2 * R - 1 := by
  unfold Dx
  rw [BD_eq_one_sub R hRle, Real.cos_neg, Real.cos_pi]
  simp [B]
  ring

theorem Dy_pi (R : ℝ) : Dy R Real.pi = 0 := by
  unfold Dy
  rw [Real.sin_neg, Real.sin_pi]
  simp [B]

theorem origin_at_pi_iff_Rhalf (R : ℝ) (hRle : R ≤ 1) :
    (Dx R Real.pi = 0 ∧ Dy R Real.pi = 0) ↔ R = (1 / 2 : ℝ) := by
  constructor
  · intro h
    have hDx : Dx R Real.pi = 0 := h.1
    rw [Dx_pi R hRle] at hDx
    linarith
  · intro hR
    constructor
    · rw [Dx_pi R hRle, hR]
      norm_num
    · exact Dy_pi R

theorem no_origin_on_pi_if_R_ne_half
    (R : ℝ) (hRle : R ≤ 1) (hRne : R ≠ (1 / 2 : ℝ)) :
    ¬ (Dx R Real.pi = 0 ∧ Dy R Real.pi = 0) := by
  intro h
  exact hRne ((origin_at_pi_iff_Rhalf R hRle).mp h)

theorem origin_at_pi_in_01_09_iff (R : ℝ)
    (_hRlo : (0.1 : ℝ) ≤ R) (hRhi : R ≤ (0.9 : ℝ)) :
    (Dx R Real.pi = 0 ∧ Dy R Real.pi = 0) ↔ R = (1 / 2 : ℝ) := by
  have hRle1 : R ≤ 1 := by linarith
  exact origin_at_pi_iff_Rhalf R hRle1

end ABCD
end RHLean
