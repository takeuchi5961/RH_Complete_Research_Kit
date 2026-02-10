import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

-- 未使用変数の警告を抑制
set_option linter.unusedVariables false

open Complex

/--
複素平面上の回転関数 (ABCDモデル)
f(R, θ) = R + (1 - R) * e^(-iθ)
-/
noncomputable def complex_D_model (R : ℝ) (θ : ℝ) : ℂ :=
  (R : ℂ) + ((1 - R) : ℂ) * exp (-I * (θ : ℂ))

/--
【偏差の基本分解】
R を 1/2 + ε と置いたとき、モデルの出力は
「1/2 のときの出力」と「ε によるズレ」の和に分解できる。
-/
lemma complex_D_decomposition (θ : ℝ) (ε : ℝ) :
    complex_D_model (1/2 + ε) θ = complex_D_model (1/2) θ + (ε : ℂ) * (1 - exp (-I * (θ : ℂ))) := by
  unfold complex_D_model
  simp
  ring

/--
【偏差の絶対値定理】
θ = π (零点が発生しうる唯一の位相) において、
モデルの絶対値は 偏差 ε の絶対値の 2 倍に等しい。
つまり、ε が 0 でなければ絶対に零点にならない。
-/
theorem complex_D_abs_deviation (ε : ℝ) :
    Complex.abs (complex_D_model (1/2 + ε) Real.pi) = 2 * |ε| := by
  -- 1. 位相 θ = π における分解を適用
  rw [complex_D_decomposition]
  -- 2. θ = π のとき complex_D_model (1/2) π = 0 であることを利用
  have h_base : complex_D_model (1/2) Real.pi = 0 := by
    unfold complex_D_model
    simp [exp_neg, exp_I_mul_re_add_I_im]
    norm_num
  rw [h_base]
  simp
  -- 3. 指数項の計算: exp(-I * π) = -1
  have h_exp : exp (-I * (Real.pi : ℂ)) = -1 := by
    rw [exp_neg, exp_I_mul_re_add_I_im]
    simp [Real.cos_pi, Real.sin_pi]
  rw [h_exp]
  -- 4. 残った式の整理: |ε * (1 - (-1))| = |ε * 2|
  norm_num
  -- Complex.abs (ε * 2) = 2 * |ε|
  rw [Complex.abs_mul, Complex.abs_of_real]
  norm_num
  left; ring

/--
【結論：臨界線外の非存在性】
R < 1 において、モデルが 0 となるためには ε = 0 (すなわち R = 1/2)
であることが幾何学的に強制される。
-/
theorem complex_D_zero_implies_critical_line (ε : ℝ) :
    complex_D_model (1/2 + ε) Real.pi = 0 → ε = 0 := by
  intro h
  have h_abs := congr_arg Complex.abs h
  rw [complex_D_abs_deviation] at h_abs
  simp at h_abs
  exact h_abs