/- Native word row 1 product certificate, part 1. -/
module
public import Glennie.Compact.NativeWordProductCommonR01

@[expose] public section
namespace Glennie.Compact.NativeWordTableR01
noncomputable section
open Glennie AlbertGeometry.NativeOperatorTrace
open scoped BigOperators Matrix
set_option autoImplicit false

def productCoeff_01_09 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def productColumn_01_09 : Fin 27 → ℝ := ![-2, 0, 2, 0, 0, 0, 0, 0, 0, 0, (-1/2), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1/2), 0, 0, 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_01_09 :
    jordan value1 value9 = decode productColumn_01_09 := by
  simp only [value1_decode, value9_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_01_09, column1, column9, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_01_09 :
    productColumn_01_09 = ∑ k : Fin 27, productCoeff_01_09 k • columns k := by
  funext r
  change productColumn_01_09 r = ∑ k : Fin 27, productCoeff_01_09 k * columns k r
  fin_cases r <;> norm_num [productColumn_01_09, productCoeff_01_09, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_01_09 :
    jordan (nativeWords 1) (nativeWords 9) =
      ∑ k : Fin 27, productCoeff_01_09 k • nativeWords k := by
  change jordan value1 value9 = _
  rw [native_product_decode_01_09, productColumn_sum_01_09, decode_sum_columns]

def productCoeff_01_10 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, (1/4), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def productColumn_01_10 : Fin 27 → ℝ := ![0, 0, 0, (-1/8), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (1/8), 0, 0, 0, 0, 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_01_10 :
    jordan value1 value10 = decode productColumn_01_10 := by
  simp only [value1_decode, value10_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_01_10, column1, column10, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_01_10 :
    productColumn_01_10 = ∑ k : Fin 27, productCoeff_01_10 k • columns k := by
  funext r
  change productColumn_01_10 r = ∑ k : Fin 27, productCoeff_01_10 k * columns k r
  fin_cases r <;> norm_num [productColumn_01_10, productCoeff_01_10, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_01_10 :
    jordan (nativeWords 1) (nativeWords 10) =
      ∑ k : Fin 27, productCoeff_01_10 k • nativeWords k := by
  change jordan value1 value10 = _
  rw [native_product_decode_01_10, productColumn_sum_01_10, decode_sum_columns]

def productCoeff_01_11 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, (1/4), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def productColumn_01_11 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, (-1/8), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1/8), 0, 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_01_11 :
    jordan value1 value11 = decode productColumn_01_11 := by
  simp only [value1_decode, value11_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_01_11, column1, column11, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_01_11 :
    productColumn_01_11 = ∑ k : Fin 27, productCoeff_01_11 k • columns k := by
  funext r
  change productColumn_01_11 r = ∑ k : Fin 27, productCoeff_01_11 k * columns k r
  fin_cases r <;> norm_num [productColumn_01_11, productCoeff_01_11, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_01_11 :
    jordan (nativeWords 1) (nativeWords 11) =
      ∑ k : Fin 27, productCoeff_01_11 k • nativeWords k := by
  change jordan value1 value11 = _
  rw [native_product_decode_01_11, productColumn_sum_01_11, decode_sum_columns]

def productCoeff_01_12 : Fin 27 → ℝ := ![-1, 0, 0, 0, 3, 0, 0, (1/2), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1/2), 0, 0, 0, 0, 0, 0, 0, 0]
def productColumn_01_12 : Fin 27 → ℝ := ![2, 0, 2, 0, (1/4), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (1/4), 0, 0, 0, 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_01_12 :
    jordan value1 value12 = decode productColumn_01_12 := by
  simp only [value1_decode, value12_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_01_12, column1, column12, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_01_12 :
    productColumn_01_12 = ∑ k : Fin 27, productCoeff_01_12 k • columns k := by
  funext r
  change productColumn_01_12 r = ∑ k : Fin 27, productCoeff_01_12 k * columns k r
  fin_cases r <;> norm_num [productColumn_01_12, productCoeff_01_12, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_01_12 :
    jordan (nativeWords 1) (nativeWords 12) =
      ∑ k : Fin 27, productCoeff_01_12 k • nativeWords k := by
  change jordan value1 value12 = _
  rw [native_product_decode_01_12, productColumn_sum_01_12, decode_sum_columns]

def productCoeff_01_13 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, 0, 0, (1/2), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1/2), 0, 0, 0, 0, 0, 0, 0]
def productColumn_01_13 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, (-1/8), 0, (-1/8), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1/8), 0, 0, (-1/8)]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_01_13 :
    jordan value1 value13 = decode productColumn_01_13 := by
  simp only [value1_decode, value13_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_01_13, column1, column13, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_01_13 :
    productColumn_01_13 = ∑ k : Fin 27, productCoeff_01_13 k • columns k := by
  funext r
  change productColumn_01_13 r = ∑ k : Fin 27, productCoeff_01_13 k * columns k r
  fin_cases r <;> norm_num [productColumn_01_13, productCoeff_01_13, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_01_13 :
    jordan (nativeWords 1) (nativeWords 13) =
      ∑ k : Fin 27, productCoeff_01_13 k • nativeWords k := by
  change jordan value1 value13 = _
  rw [native_product_decode_01_13, productColumn_sum_01_13, decode_sum_columns]

def productCoeff_01_14 : Fin 27 → ℝ := ![-1, 0, 0, 0, 3, 0, 0, 0, 0, (1/2), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1/2), 0, 0, 0, 0, 0, 0]
def productColumn_01_14 : Fin 27 → ℝ := ![2, 0, 2, 0, 0, 0, 0, 0, 0, 0, (1/4), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1/4), 0, 0, 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_01_14 :
    jordan value1 value14 = decode productColumn_01_14 := by
  simp only [value1_decode, value14_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_01_14, column1, column14, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_01_14 :
    productColumn_01_14 = ∑ k : Fin 27, productCoeff_01_14 k • columns k := by
  funext r
  change productColumn_01_14 r = ∑ k : Fin 27, productCoeff_01_14 k * columns k r
  fin_cases r <;> norm_num [productColumn_01_14, productCoeff_01_14, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_01_14 :
    jordan (nativeWords 1) (nativeWords 14) =
      ∑ k : Fin 27, productCoeff_01_14 k • nativeWords k := by
  change jordan value1 value14 = _
  rw [native_product_decode_01_14, productColumn_sum_01_14, decode_sum_columns]

def productCoeff_01_15 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0]
def productColumn_01_15 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, (1/8), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (1/8)]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_01_15 :
    jordan value1 value15 = decode productColumn_01_15 := by
  simp only [value1_decode, value15_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_01_15, column1, column15, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_01_15 :
    productColumn_01_15 = ∑ k : Fin 27, productCoeff_01_15 k • columns k := by
  funext r
  change productColumn_01_15 r = ∑ k : Fin 27, productCoeff_01_15 k * columns k r
  fin_cases r <;> norm_num [productColumn_01_15, productCoeff_01_15, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_01_15 :
    jordan (nativeWords 1) (nativeWords 15) =
      ∑ k : Fin 27, productCoeff_01_15 k • nativeWords k := by
  change jordan value1 value15 = _
  rw [native_product_decode_01_15, productColumn_sum_01_15, decode_sum_columns]

def productCoeff_01_16 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0]
def productColumn_01_16 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, (1/8), 0, (-1/8), (-1/4), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1/4), 0, (-1/8), (1/8), 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_01_16 :
    jordan value1 value16 = decode productColumn_01_16 := by
  simp only [value1_decode, value16_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_01_16, column1, column16, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_01_16 :
    productColumn_01_16 = ∑ k : Fin 27, productCoeff_01_16 k • columns k := by
  funext r
  change productColumn_01_16 r = ∑ k : Fin 27, productCoeff_01_16 k * columns k r
  fin_cases r <;> norm_num [productColumn_01_16, productCoeff_01_16, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_01_16 :
    jordan (nativeWords 1) (nativeWords 16) =
      ∑ k : Fin 27, productCoeff_01_16 k • nativeWords k := by
  change jordan value1 value16 = _
  rw [native_product_decode_01_16, productColumn_sum_01_16, decode_sum_columns]

end
end Glennie.Compact.NativeWordTableR01
