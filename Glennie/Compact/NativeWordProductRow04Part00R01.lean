/- Native word row 4 product certificate, part 0. -/
module
public import Glennie.Compact.NativeWordProductCommonR01

@[expose] public section
namespace Glennie.Compact.NativeWordTableR01
noncomputable section
open Glennie AlbertGeometry.NativeOperatorTrace
open scoped BigOperators Matrix
set_option autoImplicit false

def productCoeff_04_04 : Fin 27 → ℝ := ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def productColumn_04_04 : Fin 27 → ℝ := ![1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_04_04 :
    jordan value4 value4 = decode productColumn_04_04 := by
  simp only [value4_decode, value4_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_04_04, column4, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_04_04 :
    productColumn_04_04 = ∑ k : Fin 27, productCoeff_04_04 k • columns k := by
  funext r
  change productColumn_04_04 r = ∑ k : Fin 27, productCoeff_04_04 k * columns k r
  fin_cases r <;> norm_num [productColumn_04_04, productCoeff_04_04, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_04_04 :
    jordan (nativeWords 4) (nativeWords 4) =
      ∑ k : Fin 27, productCoeff_04_04 k • nativeWords k := by
  change jordan value4 value4 = _
  rw [native_product_decode_04_04, productColumn_sum_04_04, decode_sum_columns]

def productCoeff_04_05 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, (1/2), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def productColumn_04_05 : Fin 27 → ℝ := ![0, 0, 0, (-1/4), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (1/4), 0, 0, 0, 0, 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_04_05 :
    jordan value4 value5 = decode productColumn_04_05 := by
  simp only [value4_decode, value5_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_04_05, column4, column5, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_04_05 :
    productColumn_04_05 = ∑ k : Fin 27, productCoeff_04_05 k • columns k := by
  funext r
  change productColumn_04_05 r = ∑ k : Fin 27, productCoeff_04_05 k * columns k r
  fin_cases r <;> norm_num [productColumn_04_05, productCoeff_04_05, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_04_05 :
    jordan (nativeWords 4) (nativeWords 5) =
      ∑ k : Fin 27, productCoeff_04_05 k • nativeWords k := by
  change jordan value4 value5 = _
  rw [native_product_decode_04_05, productColumn_sum_04_05, decode_sum_columns]

def productCoeff_04_06 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, (1/2), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def productColumn_04_06 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, (-1/4), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1/4), 0, 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_04_06 :
    jordan value4 value6 = decode productColumn_04_06 := by
  simp only [value4_decode, value6_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_04_06, column4, column6, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_04_06 :
    productColumn_04_06 = ∑ k : Fin 27, productCoeff_04_06 k • columns k := by
  funext r
  change productColumn_04_06 r = ∑ k : Fin 27, productCoeff_04_06 k * columns k r
  fin_cases r <;> norm_num [productColumn_04_06, productCoeff_04_06, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_04_06 :
    jordan (nativeWords 4) (nativeWords 6) =
      ∑ k : Fin 27, productCoeff_04_06 k • nativeWords k := by
  change jordan value4 value6 = _
  rw [native_product_decode_04_06, productColumn_sum_04_06, decode_sum_columns]

def productCoeff_04_07 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]
def productColumn_04_07 : Fin 27 → ℝ := ![2, 0, 2, 0, (1/2), 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, (1/2), 0, 0, 0, 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_04_07 :
    jordan value4 value7 = decode productColumn_04_07 := by
  simp only [value4_decode, value7_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_04_07, column4, column7, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_04_07 :
    productColumn_04_07 = ∑ k : Fin 27, productCoeff_04_07 k • columns k := by
  funext r
  change productColumn_04_07 r = ∑ k : Fin 27, productCoeff_04_07 k * columns k r
  fin_cases r <;> norm_num [productColumn_04_07, productCoeff_04_07, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_04_07 :
    jordan (nativeWords 4) (nativeWords 7) =
      ∑ k : Fin 27, productCoeff_04_07 k • nativeWords k := by
  change jordan value4 value7 = _
  rw [native_product_decode_04_07, productColumn_sum_04_07, decode_sum_columns]

def productCoeff_04_08 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
def productColumn_04_08 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, (-1/4), 0, (-1/4), 0, 0, 0, 0, 0, 0, (-1/2), 0, 0, (1/2), 0, 0, 0, 0, 0, (-1/4), 0, 0, (-1/4)]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_04_08 :
    jordan value4 value8 = decode productColumn_04_08 := by
  simp only [value4_decode, value8_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_04_08, column4, column8, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_04_08 :
    productColumn_04_08 = ∑ k : Fin 27, productCoeff_04_08 k • columns k := by
  funext r
  change productColumn_04_08 r = ∑ k : Fin 27, productCoeff_04_08 k * columns k r
  fin_cases r <;> norm_num [productColumn_04_08, productCoeff_04_08, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_04_08 :
    jordan (nativeWords 4) (nativeWords 8) =
      ∑ k : Fin 27, productCoeff_04_08 k • nativeWords k := by
  change jordan value4 value8 = _
  rw [native_product_decode_04_08, productColumn_sum_04_08, decode_sum_columns]

def productCoeff_04_09 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]
def productColumn_04_09 : Fin 27 → ℝ := ![2, 0, 2, 0, 0, 0, 0, 0, 0, 0, (1/2), 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, (-1/2), 0, 0, 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_04_09 :
    jordan value4 value9 = decode productColumn_04_09 := by
  simp only [value4_decode, value9_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_04_09, column4, column9, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_04_09 :
    productColumn_04_09 = ∑ k : Fin 27, productCoeff_04_09 k • columns k := by
  funext r
  change productColumn_04_09 r = ∑ k : Fin 27, productCoeff_04_09 k * columns k r
  fin_cases r <;> norm_num [productColumn_04_09, productCoeff_04_09, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_04_09 :
    jordan (nativeWords 4) (nativeWords 9) =
      ∑ k : Fin 27, productCoeff_04_09 k • nativeWords k := by
  change jordan value4 value9 = _
  rw [native_product_decode_04_09, productColumn_sum_04_09, decode_sum_columns]

def productCoeff_04_10 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (1/2), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def productColumn_04_10 : Fin 27 → ℝ := ![0, 0, 0, (1/8), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (1/8), 0, 0, 0, 0, 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_04_10 :
    jordan value4 value10 = decode productColumn_04_10 := by
  simp only [value4_decode, value10_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_04_10, column4, column10, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_04_10 :
    productColumn_04_10 = ∑ k : Fin 27, productCoeff_04_10 k • columns k := by
  funext r
  change productColumn_04_10 r = ∑ k : Fin 27, productCoeff_04_10 k * columns k r
  fin_cases r <;> norm_num [productColumn_04_10, productCoeff_04_10, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_04_10 :
    jordan (nativeWords 4) (nativeWords 10) =
      ∑ k : Fin 27, productCoeff_04_10 k • nativeWords k := by
  change jordan value4 value10 = _
  rw [native_product_decode_04_10, productColumn_sum_04_10, decode_sum_columns]

def productCoeff_04_11 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (1/2), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def productColumn_04_11 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, (1/8), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1/8), 0, 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_04_11 :
    jordan value4 value11 = decode productColumn_04_11 := by
  simp only [value4_decode, value11_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_04_11, column4, column11, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_04_11 :
    productColumn_04_11 = ∑ k : Fin 27, productCoeff_04_11 k • columns k := by
  funext r
  change productColumn_04_11 r = ∑ k : Fin 27, productCoeff_04_11 k * columns k r
  fin_cases r <;> norm_num [productColumn_04_11, productCoeff_04_11, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_04_11 :
    jordan (nativeWords 4) (nativeWords 11) =
      ∑ k : Fin 27, productCoeff_04_11 k • nativeWords k := by
  change jordan value4 value11 = _
  rw [native_product_decode_04_11, productColumn_sum_04_11, decode_sum_columns]

end
end Glennie.Compact.NativeWordTableR01
