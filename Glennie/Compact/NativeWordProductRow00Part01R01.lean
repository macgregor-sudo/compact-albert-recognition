/- Native word row 0 product certificate, part 1. -/
module
public import Glennie.Compact.NativeWordProductCommonR01

@[expose] public section
namespace Glennie.Compact.NativeWordTableR01
noncomputable section
open Glennie AlbertGeometry.NativeOperatorTrace
open scoped BigOperators Matrix
set_option autoImplicit false

def productCoeff_00_08 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def productColumn_00_08 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, (-1/2), 0, (-1/2), 0, 0, 0, 0, 0, 0, (-1/2), 0, 0, (1/2), 0, 0, 0, 0, 0, (-1/2), 0, 0, (-1/2)]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_00_08 :
    jordan value0 value8 = decode productColumn_00_08 := by
  simp only [value0_decode, value8_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_00_08, column0, column8, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_00_08 :
    productColumn_00_08 = ∑ k : Fin 27, productCoeff_00_08 k • columns k := by
  funext r
  change productColumn_00_08 r = ∑ k : Fin 27, productCoeff_00_08 k * columns k r
  fin_cases r <;> norm_num [productColumn_00_08, productCoeff_00_08, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_00_08 :
    jordan (nativeWords 0) (nativeWords 8) =
      ∑ k : Fin 27, productCoeff_00_08 k • nativeWords k := by
  change jordan value0 value8 = _
  rw [native_product_decode_00_08, productColumn_sum_00_08, decode_sum_columns]

def productCoeff_00_09 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def productColumn_00_09 : Fin 27 → ℝ := ![2, 2, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_00_09 :
    jordan value0 value9 = decode productColumn_00_09 := by
  simp only [value0_decode, value9_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_00_09, column0, column9, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_00_09 :
    productColumn_00_09 = ∑ k : Fin 27, productCoeff_00_09 k • columns k := by
  funext r
  change productColumn_00_09 r = ∑ k : Fin 27, productCoeff_00_09 k * columns k r
  fin_cases r <;> norm_num [productColumn_00_09, productCoeff_00_09, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_00_09 :
    jordan (nativeWords 0) (nativeWords 9) =
      ∑ k : Fin 27, productCoeff_00_09 k • nativeWords k := by
  change jordan value0 value9 = _
  rw [native_product_decode_00_09, productColumn_sum_00_09, decode_sum_columns]

def productCoeff_00_10 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def productColumn_00_10 : Fin 27 → ℝ := ![0, 0, 0, (1/4), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (1/4), 0, 0, 0, 0, 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_00_10 :
    jordan value0 value10 = decode productColumn_00_10 := by
  simp only [value0_decode, value10_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_00_10, column0, column10, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_00_10 :
    productColumn_00_10 = ∑ k : Fin 27, productCoeff_00_10 k • columns k := by
  funext r
  change productColumn_00_10 r = ∑ k : Fin 27, productCoeff_00_10 k * columns k r
  fin_cases r <;> norm_num [productColumn_00_10, productCoeff_00_10, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_00_10 :
    jordan (nativeWords 0) (nativeWords 10) =
      ∑ k : Fin 27, productCoeff_00_10 k • nativeWords k := by
  change jordan value0 value10 = _
  rw [native_product_decode_00_10, productColumn_sum_00_10, decode_sum_columns]

def productCoeff_00_11 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def productColumn_00_11 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, (1/4), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1/4), 0, 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_00_11 :
    jordan value0 value11 = decode productColumn_00_11 := by
  simp only [value0_decode, value11_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_00_11, column0, column11, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_00_11 :
    productColumn_00_11 = ∑ k : Fin 27, productCoeff_00_11 k • columns k := by
  funext r
  change productColumn_00_11 r = ∑ k : Fin 27, productCoeff_00_11 k * columns k r
  fin_cases r <;> norm_num [productColumn_00_11, productCoeff_00_11, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_00_11 :
    jordan (nativeWords 0) (nativeWords 11) =
      ∑ k : Fin 27, productCoeff_00_11 k • nativeWords k := by
  change jordan value0 value11 = _
  rw [native_product_decode_00_11, productColumn_sum_00_11, decode_sum_columns]

def productCoeff_00_12 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def productColumn_00_12 : Fin 27 → ℝ := ![-2, 0, 2, 0, (-1/2), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (1/2), 0, 0, 0, 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_00_12 :
    jordan value0 value12 = decode productColumn_00_12 := by
  simp only [value0_decode, value12_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_00_12, column0, column12, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_00_12 :
    productColumn_00_12 = ∑ k : Fin 27, productCoeff_00_12 k • columns k := by
  funext r
  change productColumn_00_12 r = ∑ k : Fin 27, productCoeff_00_12 k * columns k r
  fin_cases r <;> norm_num [productColumn_00_12, productCoeff_00_12, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_00_12 :
    jordan (nativeWords 0) (nativeWords 12) =
      ∑ k : Fin 27, productCoeff_00_12 k • nativeWords k := by
  change jordan value0 value12 = _
  rw [native_product_decode_00_12, productColumn_sum_00_12, decode_sum_columns]

def productCoeff_00_13 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def productColumn_00_13 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, (1/4), 0, (1/4), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1/4), 0, 0, (-1/4)]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_00_13 :
    jordan value0 value13 = decode productColumn_00_13 := by
  simp only [value0_decode, value13_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_00_13, column0, column13, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_00_13 :
    productColumn_00_13 = ∑ k : Fin 27, productCoeff_00_13 k • columns k := by
  funext r
  change productColumn_00_13 r = ∑ k : Fin 27, productCoeff_00_13 k * columns k r
  fin_cases r <;> norm_num [productColumn_00_13, productCoeff_00_13, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_00_13 :
    jordan (nativeWords 0) (nativeWords 13) =
      ∑ k : Fin 27, productCoeff_00_13 k • nativeWords k := by
  change jordan value0 value13 = _
  rw [native_product_decode_00_13, productColumn_sum_00_13, decode_sum_columns]

def productCoeff_00_14 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def productColumn_00_14 : Fin 27 → ℝ := ![-2, 0, 2, 0, 0, 0, 0, 0, 0, 0, (-1/2), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1/2), 0, 0, 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_00_14 :
    jordan value0 value14 = decode productColumn_00_14 := by
  simp only [value0_decode, value14_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_00_14, column0, column14, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_00_14 :
    productColumn_00_14 = ∑ k : Fin 27, productCoeff_00_14 k • columns k := by
  funext r
  change productColumn_00_14 r = ∑ k : Fin 27, productCoeff_00_14 k * columns k r
  fin_cases r <;> norm_num [productColumn_00_14, productCoeff_00_14, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_00_14 :
    jordan (nativeWords 0) (nativeWords 14) =
      ∑ k : Fin 27, productCoeff_00_14 k • nativeWords k := by
  change jordan value0 value14 = _
  rw [native_product_decode_00_14, productColumn_sum_00_14, decode_sum_columns]

def productCoeff_00_15 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def productColumn_00_15 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, (-1/4), 0, 0, 0, 0, 0, 0, 0, 0, (-1/4), 0, 0, (-1/4), 0, 0, 0, 0, 0, 0, 0, 0, (1/4)]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_00_15 :
    jordan value0 value15 = decode productColumn_00_15 := by
  simp only [value0_decode, value15_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_00_15, column0, column15, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_00_15 :
    productColumn_00_15 = ∑ k : Fin 27, productCoeff_00_15 k • columns k := by
  funext r
  change productColumn_00_15 r = ∑ k : Fin 27, productCoeff_00_15 k * columns k r
  fin_cases r <;> norm_num [productColumn_00_15, productCoeff_00_15, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_00_15 :
    jordan (nativeWords 0) (nativeWords 15) =
      ∑ k : Fin 27, productCoeff_00_15 k • nativeWords k := by
  change jordan value0 value15 = _
  rw [native_product_decode_00_15, productColumn_sum_00_15, decode_sum_columns]

end
end Glennie.Compact.NativeWordTableR01
