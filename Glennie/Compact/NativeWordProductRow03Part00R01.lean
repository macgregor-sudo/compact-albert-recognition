/- Native word row 3 product certificate, part 0. -/
module
public import Glennie.Compact.NativeWordProductCommonR01

@[expose] public section
namespace Glennie.Compact.NativeWordTableR01
noncomputable section
open Glennie AlbertGeometry.NativeOperatorTrace
open scoped BigOperators Matrix
set_option autoImplicit false

def productCoeff_03_03 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def productColumn_03_03 : Fin 27 → ℝ := ![2, 2, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_03_03 :
    jordan value3 value3 = decode productColumn_03_03 := by
  simp only [value3_decode, value3_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_03_03, column3, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_03_03 :
    productColumn_03_03 = ∑ k : Fin 27, productCoeff_03_03 k • columns k := by
  funext r
  change productColumn_03_03 r = ∑ k : Fin 27, productCoeff_03_03 k * columns k r
  fin_cases r <;> norm_num [productColumn_03_03, productCoeff_03_03, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_03_03 :
    jordan (nativeWords 3) (nativeWords 3) =
      ∑ k : Fin 27, productCoeff_03_03 k • nativeWords k := by
  change jordan value3 value3 = _
  rw [native_product_decode_03_03, productColumn_sum_03_03, decode_sum_columns]

def productCoeff_03_04 : Fin 27 → ℝ := ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def productColumn_03_04 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, (1/2), 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, (-1/2), 0, 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_03_04 :
    jordan value3 value4 = decode productColumn_03_04 := by
  simp only [value3_decode, value4_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_03_04, column3, column4, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_03_04 :
    productColumn_03_04 = ∑ k : Fin 27, productCoeff_03_04 k • columns k := by
  funext r
  change productColumn_03_04 r = ∑ k : Fin 27, productCoeff_03_04 k * columns k r
  fin_cases r <;> norm_num [productColumn_03_04, productCoeff_03_04, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_03_04 :
    jordan (nativeWords 3) (nativeWords 4) =
      ∑ k : Fin 27, productCoeff_03_04 k • nativeWords k := by
  change jordan value3 value4 = _
  rw [native_product_decode_03_04, productColumn_sum_03_04, decode_sum_columns]

def productCoeff_03_05 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def productColumn_03_05 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, 0, (-1/4), 0, 0, 0, 0, 0, 0, (1/4), 0, 0, (1/4), 0, 0, 0, 0, 0, (1/4), 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_03_05 :
    jordan value3 value5 = decode productColumn_03_05 := by
  simp only [value3_decode, value5_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_03_05, column3, column5, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_03_05 :
    productColumn_03_05 = ∑ k : Fin 27, productCoeff_03_05 k • columns k := by
  funext r
  change productColumn_03_05 r = ∑ k : Fin 27, productCoeff_03_05 k * columns k r
  fin_cases r <;> norm_num [productColumn_03_05, productCoeff_03_05, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_03_05 :
    jordan (nativeWords 3) (nativeWords 5) =
      ∑ k : Fin 27, productCoeff_03_05 k • nativeWords k := by
  change jordan value3 value5 = _
  rw [native_product_decode_03_05, productColumn_sum_03_05, decode_sum_columns]

def productCoeff_03_06 : Fin 27 → ℝ := ![0, (3/2), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1/2), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def productColumn_03_06 : Fin 27 → ℝ := ![(-1/2), 0, (1/2), 0, 0, 0, 0, 0, 0, 0, (1/4), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (1/4), 0, 0, 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_03_06 :
    jordan value3 value6 = decode productColumn_03_06 := by
  simp only [value3_decode, value6_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_03_06, column3, column6, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_03_06 :
    productColumn_03_06 = ∑ k : Fin 27, productCoeff_03_06 k • columns k := by
  funext r
  change productColumn_03_06 r = ∑ k : Fin 27, productCoeff_03_06 k * columns k r
  fin_cases r <;> norm_num [productColumn_03_06, productCoeff_03_06, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_03_06 :
    jordan (nativeWords 3) (nativeWords 6) =
      ∑ k : Fin 27, productCoeff_03_06 k • nativeWords k := by
  change jordan value3 value6 = _
  rw [native_product_decode_03_06, productColumn_sum_03_06, decode_sum_columns]

def productCoeff_03_07 : Fin 27 → ℝ := ![0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def productColumn_03_07 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, (1/2), 0, (-1/2), 2, 0, 0, 0, (1/2), 0, -2, 0, 0, (1/2), 0, 0, 0, -2, 0, (1/2), (-1/2), 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_03_07 :
    jordan value3 value7 = decode productColumn_03_07 := by
  simp only [value3_decode, value7_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_03_07, column3, column7, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_03_07 :
    productColumn_03_07 = ∑ k : Fin 27, productCoeff_03_07 k • columns k := by
  funext r
  change productColumn_03_07 r = ∑ k : Fin 27, productCoeff_03_07 k * columns k r
  fin_cases r <;> norm_num [productColumn_03_07, productCoeff_03_07, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_03_07 :
    jordan (nativeWords 3) (nativeWords 7) =
      ∑ k : Fin 27, productCoeff_03_07 k • nativeWords k := by
  change jordan value3 value7 = _
  rw [native_product_decode_03_07, productColumn_sum_03_07, decode_sum_columns]

def productCoeff_03_08 : Fin 27 → ℝ := ![0, 0, (3/2), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1/2), 0, 0, 0, 0, 0, 0, 0, 0, 0]
def productColumn_03_08 : Fin 27 → ℝ := ![0, 0, 0, (1/2), 0, 0, (-1/4), 0, (-1/4), 0, 0, 0, (1/2), (1/4), 0, 0, 0, 0, (-1/4), (1/2), 0, 0, 0, 0, (-1/4), (-1/4), 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_03_08 :
    jordan value3 value8 = decode productColumn_03_08 := by
  simp only [value3_decode, value8_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_03_08, column3, column8, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_03_08 :
    productColumn_03_08 = ∑ k : Fin 27, productCoeff_03_08 k • columns k := by
  funext r
  change productColumn_03_08 r = ∑ k : Fin 27, productCoeff_03_08 k * columns k r
  fin_cases r <;> norm_num [productColumn_03_08, productCoeff_03_08, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_03_08 :
    jordan (nativeWords 3) (nativeWords 8) =
      ∑ k : Fin 27, productCoeff_03_08 k • nativeWords k := by
  change jordan value3 value8 = _
  rw [native_product_decode_03_08, productColumn_sum_03_08, decode_sum_columns]

def productCoeff_03_09 : Fin 27 → ℝ := ![0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def productColumn_03_09 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, -3, 0, 0, 0, 0, 0, 0, -3, 0, 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_03_09 :
    jordan value3 value9 = decode productColumn_03_09 := by
  simp only [value3_decode, value9_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_03_09, column3, column9, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_03_09 :
    productColumn_03_09 = ∑ k : Fin 27, productCoeff_03_09 k • columns k := by
  funext r
  change productColumn_03_09 r = ∑ k : Fin 27, productCoeff_03_09 k * columns k r
  fin_cases r <;> norm_num [productColumn_03_09, productCoeff_03_09, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_03_09 :
    jordan (nativeWords 3) (nativeWords 9) =
      ∑ k : Fin 27, productCoeff_03_09 k • nativeWords k := by
  change jordan value3 value9 = _
  rw [native_product_decode_03_09, productColumn_sum_03_09, decode_sum_columns]

def productCoeff_03_10 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, 0, 0, (1/4), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0]
def productColumn_03_10 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, 0, (-1/8), 0, 0, 0, 0, 0, 0, (-1/8), 0, 0, (1/8), 0, 0, 0, 0, 0, (-1/8), 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_03_10 :
    jordan value3 value10 = decode productColumn_03_10 := by
  simp only [value3_decode, value10_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_03_10, column3, column10, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_03_10 :
    productColumn_03_10 = ∑ k : Fin 27, productCoeff_03_10 k • columns k := by
  funext r
  change productColumn_03_10 r = ∑ k : Fin 27, productCoeff_03_10 k * columns k r
  fin_cases r <;> norm_num [productColumn_03_10, productCoeff_03_10, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_03_10 :
    jordan (nativeWords 3) (nativeWords 10) =
      ∑ k : Fin 27, productCoeff_03_10 k • nativeWords k := by
  change jordan value3 value10 = _
  rw [native_product_decode_03_10, productColumn_sum_03_10, decode_sum_columns]

end
end Glennie.Compact.NativeWordTableR01
