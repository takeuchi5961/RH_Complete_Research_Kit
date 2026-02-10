import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

-- 証明の純粋性を保つため、未使用変数の警告をオフにします
set_option linter.unusedVariables false

open Complex

/--
複素平面上の回転関数 (あなたの幾何モデルの純粋複素数表現)
f(R, θ) = R + (1 - R) * e^(-iθ)
-/
noncomputable def complex_D_model (R : ℝ) (θ : ℝ) : ℂ :=
  (R : ℂ) + ((1 - R) : ℂ) * exp (-I * (θ : ℂ))

/--
【補題1：虚部からの制約】
R < 1 において、複素数モデルの虚部が 0 になるためには、
θ は必ず π の整数倍 (..., -π, 0, π, 2π, ...) でなければならない。
-/
theorem complex_D_im_zero_iff (R : ℝ) (θ : ℝ) (hR : R < 1) :
    (complex_D_model R θ).im = 0 ↔ ∃ k : ℤ, θ = k * Real.pi := by
  unfold complex_D_model
  simp [exp_neg, exp_I_mul_re_add_I_im]
  -- 虚部を取り出すと: -(1 - R) * sin(θ) = 0
  constructor
  · intro h
    simp at h
    -- 1 - R ≠ 0 なので sin(θ) = 0 が導かれる
    have h_sin : Real.sin θ = 0 := by
      have h1R : 1 - R ≠ 0 := by linarith
      exact mul_eq_zero.mp h |> (or_iff_right (neg_ne_zero.mpr h1R)).mp
    exact Real.sin_eq_zero_iff.mp h_sin
  · rintro ⟨k, rfl⟩
    simp [Real.sin_int_mul_pi]

/--
【補題2：実部からの制約】
θ が π の整数倍であるとき、実部が 0 になるのは
「k が奇数 かつ R = 1/2」のときのみである。
(k が偶数だと実部は 1 になり、零点にはなれない)
-/
theorem complex_D_re_zero_at_pi_k (R : ℝ) (k : ℤ) :
    (complex_D_model R (k * Real.pi)).re = 0 ↔ (R = 1/2 ∧ Odd k) := by
  unfold complex_D_model
  simp [exp_neg, exp_I_mul_re_add_I_im]
  -- cos(kπ) = (-1)^k
  rw [Real.cos_int_mul_pi k]
  constructor
  · intro h
    cases Int.even_or_odd k with
    | inl heven => -- k が偶数の場合: (-1)^k = 1
      have h_pow : (-1 : ℝ) ^ k = 1 := Int.neg_one_pow_eq_one_iff_even.mpr heven
      rw [h_pow] at h; simp at h -- R + 1 - R = 1 = 0 (矛盾)
      exact False.elim (by norm_num at h)
    | inr hodd => -- k が奇数の場合: (-1)^k = -1
      have h_pow : (-1 : ℝ) ^ k = -1 := Int.neg_one_pow_eq_neg_one_iff_odd.mpr hodd
      rw [h_pow] at h; simp at h -- R - (1 - R) = 2R - 1 = 0
      refine ⟨by linarith, hodd⟩
  · rintro ⟨hR, hodd⟩
    have h_pow : (-1 : ℝ) ^ k = -1 := Int.neg_one_pow_eq_neg_one_iff_odd.mpr hodd
    rw [hR, h_pow]
    norm_num

/--
【核心定理：全域一意性証明】
複素平面上の全領域 (R < 1) において、モデルが 0 (零点) となるのは、
R = 1/2 (臨界線) かつ θ = π (奇数倍の回転) のときに限られる。
-/
theorem complex_D_zero_iff_all (R : ℝ) (θ : ℝ) (hR : R < 1) :
    complex_D_model R θ = 0 ↔ (R = 1/2 ∧ ∃ k : ℤ, θ = k * Real.pi ∧ Odd k) := by
  constructor
  · intro h
    -- 1. 複素数が 0 なら、その虚部は 0 でなければならない
    have h_im : (complex_D_model R θ).im = 0 := by rw [h]; simp
    -- 2. 虚部が 0 なら θ = kπ (補題1)
    have h_k := (complex_D_im_zero_iff R θ hR).mp h_im
    rcases h_k with ⟨k, rfl⟩
    -- 3. その時、実部も 0 でなければならない
    have h_re : (complex_D_model R (k * Real.pi)).re = 0 := by rw [h]; simp
    -- 4. 実部が 0 なら R = 1/2 かつ k は奇数 (補題2)
    have h_final := (complex_D_re_zero_at_pi_k R k).mp h_re
    exact ⟨h_final.1, ⟨k, rfl, h_final.2⟩⟩
  · -- 逆方向: 条件を満たせば複素数として 0 になる
    rintro ⟨hR, ⟨k, rfl, hodd⟩⟩
    ext
    · exact (complex_D_re_zero_at_pi_k R k).mpr ⟨hR, hodd⟩
    · exact (complex_D_im_zero_iff R (k * Real.pi) hR).mpr ⟨k, rfl⟩
