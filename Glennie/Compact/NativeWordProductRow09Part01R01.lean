/- Native word row 9 product certificate, part 1. -/
module
public import Glennie.Compact.NativeWordProductCommonR01

@[expose] public section
namespace Glennie.Compact.NativeWordTableR01
noncomputable section
open Glennie AlbertGeometry.NativeOperatorTrace
open scoped BigOperators Matrix
set_option autoImplicit false

def productCoeff_09_14 : Fin 27 → ℝ := ![0, (-9/2), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (9/2), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def productColumn_09_14 : Fin 27 → ℝ := ![(-9/2), 0, (9/2), 0, 0, 0, 0, 0, 0, 0, (-9/4), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-9/4), 0, 0, 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_09_14 :
    jordan value9 value14 = decode productColumn_09_14 := by
  simp only [value9_decode, value14_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_09_14, column9, column14, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_09_14 :
    productColumn_09_14 = ∑ k : Fin 27, productCoeff_09_14 k • columns k := by
  funext r
  change productColumn_09_14 r = ∑ k : Fin 27, productCoeff_09_14 k * columns k r
  fin_cases r <;> norm_num [productColumn_09_14, productCoeff_09_14, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_09_14 :
    jordan (nativeWords 9) (nativeWords 14) =
      ∑ k : Fin 27, productCoeff_09_14 k • nativeWords k := by
  change jordan value9 value14 = _
  rw [native_product_decode_09_14, productColumn_sum_09_14, decode_sum_columns]

def productCoeff_09_15 : Fin 27 → ℝ := ![-1, 0, 0, 0, (3/2), 0, 0, (1/2), 0, 0, 0, 0, 0, (-1/2), 0, 2, 0, 0, (-3/4), 0, 0, 0, 0, 0, 0, 0, 0]
def productColumn_09_15 : Fin 27 → ℝ := ![0, 0, 0, 0, (1/8), (-5/8), 0, (-1/8), 0, 0, 0, (-1/4), 0, 0, (-1/2), 0, 0, (-1/2), 0, 0, (1/8), 0, 0, (1/8), 0, 0, (5/8)]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_09_15 :
    jordan value9 value15 = decode productColumn_09_15 := by
  simp only [value9_decode, value15_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_09_15, column9, column15, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_09_15 :
    productColumn_09_15 = ∑ k : Fin 27, productCoeff_09_15 k • columns k := by
  funext r
  change productColumn_09_15 r = ∑ k : Fin 27, productCoeff_09_15 k * columns k r
  fin_cases r <;> norm_num [productColumn_09_15, productCoeff_09_15, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_09_15 :
    jordan (nativeWords 9) (nativeWords 15) =
      ∑ k : Fin 27, productCoeff_09_15 k • nativeWords k := by
  change jordan value9 value15 = _
  rw [native_product_decode_09_15, productColumn_sum_09_15, decode_sum_columns]

def productCoeff_09_16 : Fin 27 → ℝ := ![0, 0, 0, (3/4), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (3/2), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def productColumn_09_16 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, (-3/8), 0, (3/8), (3/2), 0, 0, 0, (-3/8), 0, (-3/2), 0, 0, (-3/8), 0, 0, 0, (-3/2), 0, (-3/8), (3/8), 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_09_16 :
    jordan value9 value16 = decode productColumn_09_16 := by
  simp only [value9_decode, value16_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_09_16, column9, column16, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_09_16 :
    productColumn_09_16 = ∑ k : Fin 27, productCoeff_09_16 k • columns k := by
  funext r
  change productColumn_09_16 r = ∑ k : Fin 27, productCoeff_09_16 k * columns k r
  fin_cases r <;> norm_num [productColumn_09_16, productCoeff_09_16, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_09_16 :
    jordan (nativeWords 9) (nativeWords 16) =
      ∑ k : Fin 27, productCoeff_09_16 k • nativeWords k := by
  change jordan value9 value16 = _
  rw [native_product_decode_09_16, productColumn_sum_09_16, decode_sum_columns]

def productCoeff_09_17 : Fin 27 → ℝ := ![0, 0, (-9/2), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (9/2), 0, 0, 0, 0, 0, 0, 0, 0, 0]
def productColumn_09_17 : Fin 27 → ℝ := ![0, 0, 0, (9/2), 0, 0, (9/4), 0, (9/4), 0, 0, 0, (9/2), (-9/4), 0, 0, 0, 0, (9/4), (9/2), 0, 0, 0, 0, (9/4), (9/4), 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_09_17 :
    jordan value9 value17 = decode productColumn_09_17 := by
  simp only [value9_decode, value17_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_09_17, column9, column17, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_09_17 :
    productColumn_09_17 = ∑ k : Fin 27, productCoeff_09_17 k • columns k := by
  funext r
  change productColumn_09_17 r = ∑ k : Fin 27, productCoeff_09_17 k * columns k r
  fin_cases r <;> norm_num [productColumn_09_17, productCoeff_09_17, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_09_17 :
    jordan (nativeWords 9) (nativeWords 17) =
      ∑ k : Fin 27, productCoeff_09_17 k • nativeWords k := by
  change jordan value9 value17 = _
  rw [native_product_decode_09_17, productColumn_sum_09_17, decode_sum_columns]

def productCoeff_09_18 : Fin 27 → ℝ := ![(8/3), 0, 0, 0, -4, 0, 0, (-4/3), 0, (-4/3), 0, 0, 0, (1/3), 0, (-1/3), 0, 0, 2, 0, 2, 0, 0, (2/3), 0, 0, 0]
def productColumn_09_18 : Fin 27 → ℝ := ![4, 0, 4, 0, 1, (1/2), 0, (-1/4), 0, 0, 1, 2, 0, 0, (-1/4), 0, 2, (-1/4), 0, 0, 1, -1, 0, (1/4), 0, 0, (-1/2)]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_09_18 :
    jordan value9 value18 = decode productColumn_09_18 := by
  simp only [value9_decode, value18_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_09_18, column9, column18, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_09_18 :
    productColumn_09_18 = ∑ k : Fin 27, productCoeff_09_18 k • columns k := by
  funext r
  change productColumn_09_18 r = ∑ k : Fin 27, productCoeff_09_18 k * columns k r
  fin_cases r <;> norm_num [productColumn_09_18, productCoeff_09_18, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_09_18 :
    jordan (nativeWords 9) (nativeWords 18) =
      ∑ k : Fin 27, productCoeff_09_18 k • nativeWords k := by
  change jordan value9 value18 = _
  rw [native_product_decode_09_18, productColumn_sum_09_18, decode_sum_columns]

end
end Glennie.Compact.NativeWordTableR01
