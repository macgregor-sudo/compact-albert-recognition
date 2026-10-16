module
public import Glennie.Compact.NativeNormKernelR01

/- Sharp quadratic polarization. -/
@[expose] public section
namespace Glennie.Compact.NativeNormKernel
open Glennie
noncomputable section
set_option autoImplicit false

 theorem crossU_smul_first (t : ℝ) (x y w : Albert) :
    crossU (t • x) y w = t • crossU x y w := by
  simp only [crossU, jordan_smul_left, jordan_smul_right]
  module

 theorem crossU_polarization (x y w : Albert) :
    crossU x y w = (1/2 : ℝ) • (U (x+y) w - U (x-y) w) := by
  simp only [crossU, U, jordan_add_left, jordan_add_right,
    jordan_sub_left, jordan_sub_right, jordan_comm y x]
  module

 theorem crossU_norm_sum_sq (x y w : Albert) :
    ‖crossU x y w‖ ≤ (‖x‖ ^ 2 + ‖y‖ ^ 2) * ‖w‖ := by
  rw [crossU_polarization, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by norm_num : (0:ℝ) < 1/2)]
  calc
    (1/2:ℝ) * ‖U (x+y) w - U (x-y) w‖
      ≤ (1/2:ℝ) * (‖U (x+y) w‖ + ‖U (x-y) w‖) := by
        gcongr; exact norm_sub_le _ _
    _ ≤ (1/2:ℝ) * (‖x+y‖^2 * ‖w‖ + ‖x-y‖^2 * ‖w‖) := by
        gcongr <;> exact U_norm _ _
    _ = (‖x‖^2 + ‖y‖^2) * ‖w‖ := by
        calc
          _ = (1/2:ℝ) * (‖x+y‖^2 + ‖x-y‖^2) * ‖w‖ := by ring
          _ = _ := by rw [parallelogram_law_with_norm ℝ x y]; ring

 theorem crossU_norm (x y w : Albert) :
    ‖crossU x y w‖ ≤ 2 * ‖x‖ * ‖y‖ * ‖w‖ := by
  by_cases hx : x = 0
  · subst x
    simp [crossU, jordan_zero_left, jordan_zero_right]
  by_cases hy : y = 0
  · subst y
    simp [crossU, jordan_zero_left, jordan_zero_right]
  have hnx : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hny : ‖y‖ ≠ 0 := norm_ne_zero_iff.mpr hy
  have hx1 : ‖(‖x‖⁻¹ : ℝ) • x‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
    exact inv_mul_cancel₀ hnx
  have hy1 : ‖(‖y‖⁻¹ : ℝ) • y‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
    exact inv_mul_cancel₀ hny
  have H := crossU_norm_sum_sq ((‖x‖⁻¹ : ℝ) • x) ((‖y‖⁻¹ : ℝ) • y) w
  rw [hx1,hy1] at H
  have hrec : crossU x y w = (‖x‖ * ‖y‖) •
      crossU ((‖x‖⁻¹ : ℝ) • x) ((‖y‖⁻¹ : ℝ) • y) w := by
    simp only [crossU_smul_first, crossU_smul_second, smul_smul]
    have hs : (‖x‖ * ‖y‖) * (‖y‖⁻¹ * ‖x‖⁻¹) = 1 := by
      field_simp [hnx,hny]
    rw [hs, one_smul]
  rw [hrec, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
  calc
    (‖x‖*‖y‖) * ‖crossU ((‖x‖⁻¹:ℝ) • x) ((‖y‖⁻¹:ℝ) • y) w‖
      ≤ (‖x‖*‖y‖) * (2*‖w‖) := by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
        norm_num at H
        exact H
    _ = 2*‖x‖*‖y‖*‖w‖ := by ring

 theorem U_sub_base_polarized (a b w : Albert) :
    U a w - U b w = (1/2:ℝ) • crossU (a+b) (a-b) w := by
  simp only [U, crossU, jordan_add_left, jordan_add_right,
    jordan_sub_left, jordan_sub_right, jordan_comm b a]
  module

 theorem U_sub_base_norm (a b w : Albert) :
    ‖U a w - U b w‖ ≤ (‖a‖+‖b‖) * ‖a-b‖ * ‖w‖ := by
  rw [U_sub_base_polarized, norm_smul, Real.norm_eq_abs]
  calc
    |(1/2:ℝ)| * ‖crossU (a+b) (a-b) w‖
      ≤ (1/2:ℝ) * (2*‖a+b‖*‖a-b‖*‖w‖) := by
        simpa only [abs_of_pos (by norm_num : (0:ℝ) < 1/2)] using
          mul_le_mul_of_nonneg_left (crossU_norm (a+b) (a-b) w)
            (by norm_num : (0:ℝ) ≤ 1/2)
    _ = ‖a+b‖ * ‖a-b‖ * ‖w‖ := by ring
    _ ≤ (‖a‖+‖b‖) * ‖a-b‖ * ‖w‖ := by
        gcongr; exact norm_add_le _ _

 theorem U_sub_base_radius (a b w : Albert) (R : ℝ)
    (ha : ‖a‖ ≤ R) (hb : ‖b‖ ≤ R) :
    ‖U a w-U b w‖ ≤ 2*R*‖a-b‖*‖w‖ := by
  calc
    _ ≤ (‖a‖+‖b‖)*‖a-b‖*‖w‖ := U_sub_base_norm _ _ _
    _ ≤ 2*R*‖a-b‖*‖w‖ := by gcongr; linarith

end
end Glennie.Compact.NativeNormKernel
