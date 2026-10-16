/- Native word row 9 product certificate, part 0. -/
module
public import Glennie.Compact.NativeWordProductCommonR01

@[expose] public section
namespace Glennie.Compact.NativeWordTableR01
noncomputable section
open Glennie AlbertGeometry.NativeOperatorTrace
open scoped BigOperators Matrix
set_option autoImplicit false

def productCoeff_09_09 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def productColumn_09_09 : Fin 27 → ℝ := ![6, 6, 6, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, -3, 0, 0, 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_09_09 :
    jordan value9 value9 = decode productColumn_09_09 := by
  simp only [value9_decode, value9_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_09_09, column9, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_09_09 :
    productColumn_09_09 = ∑ k : Fin 27, productCoeff_09_09 k • columns k := by
  funext r
  change productColumn_09_09 r = ∑ k : Fin 27, productCoeff_09_09 k * columns k r
  fin_cases r <;> norm_num [productColumn_09_09, productCoeff_09_09, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_09_09 :
    jordan (nativeWords 9) (nativeWords 9) =
      ∑ k : Fin 27, productCoeff_09_09 k • nativeWords k := by
  change jordan value9 value9 = _
  rw [native_product_decode_09_09, productColumn_sum_09_09, decode_sum_columns]

def productCoeff_09_10 : Fin 27 → ℝ := ![0, 0, (-1/3), 0, 0, 0, (1/4), 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, (1/6), 0, 0, 0, (1/3), 0, 0, 0, (-1/3), 0]
def productColumn_09_10 : Fin 27 → ℝ := ![0, 0, 0, (1/2), 0, 0, 0, 0, (1/8), 0, 0, 0, 0, (-1/8), 0, 0, 0, 0, (1/8), (1/2), 0, 0, 0, 0, (1/8), 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_09_10 :
    jordan value9 value10 = decode productColumn_09_10 := by
  simp only [value9_decode, value10_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_09_10, column9, column10, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_09_10 :
    productColumn_09_10 = ∑ k : Fin 27, productCoeff_09_10 k • columns k := by
  funext r
  change productColumn_09_10 r = ∑ k : Fin 27, productCoeff_09_10 k * columns k r
  fin_cases r <;> norm_num [productColumn_09_10, productCoeff_09_10, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_09_10 :
    jordan (nativeWords 9) (nativeWords 10) =
      ∑ k : Fin 27, productCoeff_09_10 k • nativeWords k := by
  change jordan value9 value10 = _
  rw [native_product_decode_09_10, productColumn_sum_09_10, decode_sum_columns]

def productCoeff_09_11 : Fin 27 → ℝ := ![0, 0, 0, (1/4), 0, 0, 0, 0, 0, 0, 0, (3/2), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def productColumn_09_11 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, (5/8), 0, 0, 0, 0, 0, (-1/4), 0, 0, 0, 0, 0, 0, (-5/8), 0, 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_09_11 :
    jordan value9 value11 = decode productColumn_09_11 := by
  simp only [value9_decode, value11_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_09_11, column9, column11, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_09_11 :
    productColumn_09_11 = ∑ k : Fin 27, productCoeff_09_11 k • columns k := by
  funext r
  change productColumn_09_11 r = ∑ k : Fin 27, productCoeff_09_11 k * columns k r
  fin_cases r <;> norm_num [productColumn_09_11, productCoeff_09_11, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_09_11 :
    jordan (nativeWords 9) (nativeWords 11) =
      ∑ k : Fin 27, productCoeff_09_11 k • nativeWords k := by
  change jordan value9 value11 = _
  rw [native_product_decode_09_11, productColumn_sum_09_11, decode_sum_columns]

def productCoeff_09_12 : Fin 27 → ℝ := ![0, -4, 0, 0, 0, 0, 0, 0, (3/2), 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, -2, 0, 0, 0, 0, 2, 0, 0]
def productColumn_09_12 : Fin 27 → ℝ := ![-4, 0, 4, 0, -1, 0, 0, (-1/4), 0, 0, -1, 0, 0, 0, (1/4), 0, 0, (-1/4), 0, 0, 1, -1, 0, (-1/4), 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_09_12 :
    jordan value9 value12 = decode productColumn_09_12 := by
  simp only [value9_decode, value12_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_09_12, column9, column12, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_09_12 :
    productColumn_09_12 = ∑ k : Fin 27, productCoeff_09_12 k • columns k := by
  funext r
  change productColumn_09_12 r = ∑ k : Fin 27, productCoeff_09_12 k * columns k r
  fin_cases r <;> norm_num [productColumn_09_12, productCoeff_09_12, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_09_12 :
    jordan (nativeWords 9) (nativeWords 12) =
      ∑ k : Fin 27, productCoeff_09_12 k • nativeWords k := by
  change jordan value9 value12 = _
  rw [native_product_decode_09_12, productColumn_sum_09_12, decode_sum_columns]

def productCoeff_09_13 : Fin 27 → ℝ := ![1, 0, 0, 0, (-3/2), 0, 0, (-1/2), 0, 0, 0, 0, 0, 2, 0, (-1/2), 0, 0, (3/4), 0, 0, 0, 0, 0, 0, 0, 0]
def productColumn_09_13 : Fin 27 → ℝ := ![0, 0, 0, 0, (-1/8), (5/8), 0, (1/2), 0, 0, 0, (1/4), 0, 0, (1/8), 0, 0, (1/8), 0, 0, (-1/8), 0, 0, (-1/2), 0, 0, (-5/8)]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_09_13 :
    jordan value9 value13 = decode productColumn_09_13 := by
  simp only [value9_decode, value13_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_09_13, column9, column13, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_09_13 :
    productColumn_09_13 = ∑ k : Fin 27, productCoeff_09_13 k • columns k := by
  funext r
  change productColumn_09_13 r = ∑ k : Fin 27, productCoeff_09_13 k * columns k r
  fin_cases r <;> norm_num [productColumn_09_13, productCoeff_09_13, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_09_13 :
    jordan (nativeWords 9) (nativeWords 13) =
      ∑ k : Fin 27, productCoeff_09_13 k • nativeWords k := by
  change jordan value9 value13 = _
  rw [native_product_decode_09_13, productColumn_sum_09_13, decode_sum_columns]

end
end Glennie.Compact.NativeWordTableR01
