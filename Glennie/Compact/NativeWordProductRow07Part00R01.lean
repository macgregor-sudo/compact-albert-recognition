/- Native word row 7 product certificate, part 0. -/
module
public import Glennie.Compact.NativeWordProductCommonR01

@[expose] public section
namespace Glennie.Compact.NativeWordTableR01
noncomputable section
open Glennie AlbertGeometry.NativeOperatorTrace
open scoped BigOperators Matrix
set_option autoImplicit false

def productCoeff_07_07 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def productColumn_07_07 : Fin 27 → ℝ := ![6, 6, 6, 0, 3, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_07_07 :
    jordan value7 value7 = decode productColumn_07_07 := by
  simp only [value7_decode, value7_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_07_07, column7, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_07_07 :
    productColumn_07_07 = ∑ k : Fin 27, productCoeff_07_07 k • columns k := by
  funext r
  change productColumn_07_07 r = ∑ k : Fin 27, productCoeff_07_07 k * columns k r
  fin_cases r <;> norm_num [productColumn_07_07, productCoeff_07_07, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_07_07 :
    jordan (nativeWords 7) (nativeWords 7) =
      ∑ k : Fin 27, productCoeff_07_07 k • nativeWords k := by
  change jordan value7 value7 = _
  rw [native_product_decode_07_07, productColumn_sum_07_07, decode_sum_columns]

def productCoeff_07_08 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, 0, 0, (3/2), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def productColumn_07_08 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, (-3/4), 0, (-3/4), 0, 0, 0, 0, 0, 0, (-3/4), 0, 0, (3/4), 0, 0, 0, 0, 0, (-3/4), 0, 0, (-3/4)]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_07_08 :
    jordan value7 value8 = decode productColumn_07_08 := by
  simp only [value7_decode, value8_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_07_08, column7, column8, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_07_08 :
    productColumn_07_08 = ∑ k : Fin 27, productCoeff_07_08 k • columns k := by
  funext r
  change productColumn_07_08 r = ∑ k : Fin 27, productCoeff_07_08 k * columns k r
  fin_cases r <;> norm_num [productColumn_07_08, productCoeff_07_08, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_07_08 :
    jordan (nativeWords 7) (nativeWords 8) =
      ∑ k : Fin 27, productCoeff_07_08 k • nativeWords k := by
  change jordan value7 value8 = _
  rw [native_product_decode_07_08, productColumn_sum_07_08, decode_sum_columns]

def productCoeff_07_09 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0]
def productColumn_07_09 : Fin 27 → ℝ := ![4, 4, 4, 0, 2, (1/2), 0, (-1/2), 0, 0, 2, 2, 0, 0, (-1/2), 0, 2, (-1/2), 0, 0, 2, -2, 0, (1/2), 0, 0, (-1/2)]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_07_09 :
    jordan value7 value9 = decode productColumn_07_09 := by
  simp only [value7_decode, value9_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_07_09, column7, column9, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_07_09 :
    productColumn_07_09 = ∑ k : Fin 27, productCoeff_07_09 k • columns k := by
  funext r
  change productColumn_07_09 r = ∑ k : Fin 27, productCoeff_07_09 k * columns k r
  fin_cases r <;> norm_num [productColumn_07_09, productCoeff_07_09, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_07_09 :
    jordan (nativeWords 7) (nativeWords 9) =
      ∑ k : Fin 27, productCoeff_07_09 k • nativeWords k := by
  change jordan value7 value9 = _
  rw [native_product_decode_07_09, productColumn_sum_07_09, decode_sum_columns]

def productCoeff_07_10 : Fin 27 → ℝ := ![0, 0, (1/4), 0, 0, 0, 0, 0, 0, 0, (3/2), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def productColumn_07_10 : Fin 27 → ℝ := ![0, 0, 0, (5/8), 0, 0, 0, 0, 0, 0, 0, 0, (1/4), 0, 0, 0, 0, 0, 0, (5/8), 0, 0, 0, 0, 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_07_10 :
    jordan value7 value10 = decode productColumn_07_10 := by
  simp only [value7_decode, value10_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_07_10, column7, column10, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_07_10 :
    productColumn_07_10 = ∑ k : Fin 27, productCoeff_07_10 k • columns k := by
  funext r
  change productColumn_07_10 r = ∑ k : Fin 27, productCoeff_07_10 k * columns k r
  fin_cases r <;> norm_num [productColumn_07_10, productCoeff_07_10, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_07_10 :
    jordan (nativeWords 7) (nativeWords 10) =
      ∑ k : Fin 27, productCoeff_07_10 k • nativeWords k := by
  change jordan value7 value10 = _
  rw [native_product_decode_07_10, productColumn_sum_07_10, decode_sum_columns]

def productCoeff_07_11 : Fin 27 → ℝ := ![0, 0, 0, (1/6), 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, (-1/3), 0, 0, 0, 0, 0, (1/6), 0, 0, 0, (-1/6)]
def productColumn_07_11 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, (1/8), 0, 0, (1/2), 0, 0, 0, (1/8), 0, 0, 0, 0, (1/8), 0, 0, 0, (-1/2), 0, 0, (-1/8), 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_07_11 :
    jordan value7 value11 = decode productColumn_07_11 := by
  simp only [value7_decode, value11_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_07_11, column7, column11, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_07_11 :
    productColumn_07_11 = ∑ k : Fin 27, productCoeff_07_11 k • columns k := by
  funext r
  change productColumn_07_11 r = ∑ k : Fin 27, productCoeff_07_11 k * columns k r
  fin_cases r <;> norm_num [productColumn_07_11, productCoeff_07_11, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_07_11 :
    jordan (nativeWords 7) (nativeWords 11) =
      ∑ k : Fin 27, productCoeff_07_11 k • nativeWords k := by
  change jordan value7 value11 = _
  rw [native_product_decode_07_11, productColumn_sum_07_11, decode_sum_columns]

def productCoeff_07_12 : Fin 27 → ℝ := ![0, (-9/2), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (9/2), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def productColumn_07_12 : Fin 27 → ℝ := ![(-9/2), 0, (9/2), 0, (-9/4), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (9/4), 0, 0, 0, 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_07_12 :
    jordan value7 value12 = decode productColumn_07_12 := by
  simp only [value7_decode, value12_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_07_12, column7, column12, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_07_12 :
    productColumn_07_12 = ∑ k : Fin 27, productCoeff_07_12 k • columns k := by
  funext r
  change productColumn_07_12 r = ∑ k : Fin 27, productCoeff_07_12 k * columns k r
  fin_cases r <;> norm_num [productColumn_07_12, productCoeff_07_12, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_07_12 :
    jordan (nativeWords 7) (nativeWords 12) =
      ∑ k : Fin 27, productCoeff_07_12 k • nativeWords k := by
  change jordan value7 value12 = _
  rw [native_product_decode_07_12, productColumn_sum_07_12, decode_sum_columns]

def productCoeff_07_13 : Fin 27 → ℝ := ![-1, 0, 0, 0, (3/2), 0, 0, 0, 0, (1/2), 0, 0, 0, (5/2), 0, (1/2), 0, 0, 0, 0, (-3/4), 0, 0, 0, 0, 0, 0]
def productColumn_07_13 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, (1/2), 0, (5/8), 0, 0, (1/8), 0, 0, 0, (-1/8), 0, (-1/4), (-1/8), 0, 0, 0, (-1/8), 0, (-5/8), 0, 0, (-1/2)]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_07_13 :
    jordan value7 value13 = decode productColumn_07_13 := by
  simp only [value7_decode, value13_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_07_13, column7, column13, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_07_13 :
    productColumn_07_13 = ∑ k : Fin 27, productCoeff_07_13 k • columns k := by
  funext r
  change productColumn_07_13 r = ∑ k : Fin 27, productCoeff_07_13 k * columns k r
  fin_cases r <;> norm_num [productColumn_07_13, productCoeff_07_13, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_07_13 :
    jordan (nativeWords 7) (nativeWords 13) =
      ∑ k : Fin 27, productCoeff_07_13 k • nativeWords k := by
  change jordan value7 value13 = _
  rw [native_product_decode_07_13, productColumn_sum_07_13, decode_sum_columns]

def productCoeff_07_14 : Fin 27 → ℝ := ![0, -4, 0, 0, 0, 0, 0, 0, (-1/2), 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2, 0, 0]
def productColumn_07_14 : Fin 27 → ℝ := ![-4, 0, 4, 0, -1, (1/4), 0, 0, 0, 0, -1, 0, 0, 0, (-1/4), 0, 0, (1/4), 0, 0, 1, -1, 0, 0, 0, 0, (1/4)]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_07_14 :
    jordan value7 value14 = decode productColumn_07_14 := by
  simp only [value7_decode, value14_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_07_14, column7, column14, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_07_14 :
    productColumn_07_14 = ∑ k : Fin 27, productCoeff_07_14 k • columns k := by
  funext r
  change productColumn_07_14 r = ∑ k : Fin 27, productCoeff_07_14 k * columns k r
  fin_cases r <;> norm_num [productColumn_07_14, productCoeff_07_14, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_07_14 :
    jordan (nativeWords 7) (nativeWords 14) =
      ∑ k : Fin 27, productCoeff_07_14 k • nativeWords k := by
  change jordan value7 value14 = _
  rw [native_product_decode_07_14, productColumn_sum_07_14, decode_sum_columns]

end
end Glennie.Compact.NativeWordTableR01
