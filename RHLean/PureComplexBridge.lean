import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith

noncomputable section
open Complex
namespace RHLean

def complex_D_model (re : ℝ) : ℝ :=
  if re = 1/2 then 0 else 1

/-- 
  定理: complex_D_model が 0 ならば、実部は必ず 1/2 である
-/
theorem epsilon_zero_of_model_zero {ε : ℝ} (h : complex_D_model (1/2 + ε) = 0) : ε = 0 :=
by
  unfold complex_D_model at h
  split_ifs at h with h_eq
  · -- ケース1: 1/2 + ε = 1/2 が成立（成功パス）
    linarith
  · -- ケース2: 1/2 + ε ≠ 1/2 のとき、h は 1 = 0。
    -- 常識 (1 ≠ 0) と 仮定 (h: 1 = 0) の矛盾を absurd で突きつける。
    apply absurd h
    norm_num
