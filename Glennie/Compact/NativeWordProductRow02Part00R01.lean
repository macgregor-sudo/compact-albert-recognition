/- Native word row 2 product certificate, part 0. -/
module
public import Glennie.Compact.NativeWordProductCommonR01

@[expose] public section
namespace Glennie.Compact.NativeWordTableR01
noncomputable section
open Glennie AlbertGeometry.NativeOperatorTrace
open scoped BigOperators Matrix
set_option autoImplicit false

def productCoeff_02_02 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def productColumn_02_02 : Fin 27 → ℝ := ![2, 2, 2, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_02_02 :
    jordan value2 value2 = decode productColumn_02_02 := by
  simp only [value2_decode, value2_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_02_02, column2, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_02_02 :
    productColumn_02_02 = ∑ k : Fin 27, productCoeff_02_02 k • columns k := by
  funext r
  change productColumn_02_02 r = ∑ k : Fin 27, productCoeff_02_02 k * columns k r
  fin_cases r <;> norm_num [productColumn_02_02, productCoeff_02_02, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_02_02 :
    jordan (nativeWords 2) (nativeWords 2) =
      ∑ k : Fin 27, productCoeff_02_02 k • nativeWords k := by
  change jordan value2 value2 = _
  rw [native_product_decode_02_02, productColumn_sum_02_02, decode_sum_columns]

def productCoeff_02_03 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def productColumn_02_03 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, (-1/2), 0, (-1/2), 0, 0, 0, 0, 0, 0, (-1/2), 0, 0, (1/2), 0, 0, 0, 0, 0, (-1/2), 0, 0, (-1/2)]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_02_03 :
    jordan value2 value3 = decode productColumn_02_03 := by
  simp only [value2_decode, value3_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_02_03, column2, column3, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_02_03 :
    productColumn_02_03 = ∑ k : Fin 27, productCoeff_02_03 k • columns k := by
  funext r
  change productColumn_02_03 r = ∑ k : Fin 27, productCoeff_02_03 k * columns k r
  fin_cases r <;> norm_num [productColumn_02_03, productCoeff_02_03, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_02_03 :
    jordan (nativeWords 2) (nativeWords 3) =
      ∑ k : Fin 27, productCoeff_02_03 k • nativeWords k := by
  change jordan value2 value3 = _
  rw [native_product_decode_02_03, productColumn_sum_02_03, decode_sum_columns]

def productCoeff_02_04 : Fin 27 → ℝ := ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def productColumn_02_04 : Fin 27 → ℝ := ![0, 0, 0, (1/2), 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, (1/2), 0, 0, 0, 0, 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_02_04 :
    jordan value2 value4 = decode productColumn_02_04 := by
  simp only [value2_decode, value4_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_02_04, column2, column4, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_02_04 :
    productColumn_02_04 = ∑ k : Fin 27, productCoeff_02_04 k • columns k := by
  funext r
  change productColumn_02_04 r = ∑ k : Fin 27, productCoeff_02_04 k * columns k r
  fin_cases r <;> norm_num [productColumn_02_04, productCoeff_02_04, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_02_04 :
    jordan (nativeWords 2) (nativeWords 4) =
      ∑ k : Fin 27, productCoeff_02_04 k • nativeWords k := by
  change jordan value2 value4 = _
  rw [native_product_decode_02_04, productColumn_sum_02_04, decode_sum_columns]

def productCoeff_02_05 : Fin 27 → ℝ := ![0, (3/2), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1/2), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def productColumn_02_05 : Fin 27 → ℝ := ![(-1/2), 0, (1/2), 0, (1/4), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1/4), 0, 0, 0, 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_02_05 :
    jordan value2 value5 = decode productColumn_02_05 := by
  simp only [value2_decode, value5_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_02_05, column2, column5, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_02_05 :
    productColumn_02_05 = ∑ k : Fin 27, productCoeff_02_05 k • columns k := by
  funext r
  change productColumn_02_05 r = ∑ k : Fin 27, productCoeff_02_05 k * columns k r
  fin_cases r <;> norm_num [productColumn_02_05, productCoeff_02_05, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_02_05 :
    jordan (nativeWords 2) (nativeWords 5) =
      ∑ k : Fin 27, productCoeff_02_05 k • nativeWords k := by
  change jordan value2 value5 = _
  rw [native_product_decode_02_05, productColumn_sum_02_05, decode_sum_columns]

def productCoeff_02_06 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def productColumn_02_06 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, (-1/4), 0, 0, 0, 0, 0, 0, 0, 0, (-1/4), 0, 0, (-1/4), 0, 0, 0, 0, 0, 0, 0, 0, (1/4)]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_02_06 :
    jordan value2 value6 = decode productColumn_02_06 := by
  simp only [value2_decode, value6_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_02_06, column2, column6, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_02_06 :
    productColumn_02_06 = ∑ k : Fin 27, productCoeff_02_06 k • columns k := by
  funext r
  change productColumn_02_06 r = ∑ k : Fin 27, productCoeff_02_06 k * columns k r
  fin_cases r <;> norm_num [productColumn_02_06, productCoeff_02_06, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_02_06 :
    jordan (nativeWords 2) (nativeWords 6) =
      ∑ k : Fin 27, productCoeff_02_06 k • nativeWords k := by
  change jordan value2 value6 = _
  rw [native_product_decode_02_06, productColumn_sum_02_06, decode_sum_columns]

def productCoeff_02_07 : Fin 27 → ℝ := ![0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def productColumn_02_07 : Fin 27 → ℝ := ![0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_02_07 :
    jordan value2 value7 = decode productColumn_02_07 := by
  simp only [value2_decode, value7_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_02_07, column2, column7, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_02_07 :
    productColumn_02_07 = ∑ k : Fin 27, productCoeff_02_07 k • columns k := by
  funext r
  change productColumn_02_07 r = ∑ k : Fin 27, productCoeff_02_07 k * columns k r
  fin_cases r <;> norm_num [productColumn_02_07, productCoeff_02_07, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_02_07 :
    jordan (nativeWords 2) (nativeWords 7) =
      ∑ k : Fin 27, productCoeff_02_07 k • nativeWords k := by
  change jordan value2 value7 = _
  rw [native_product_decode_02_07, productColumn_sum_02_07, decode_sum_columns]

def productCoeff_02_08 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def productColumn_02_08 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, (-1/4), 0, (1/4), (1/2), 0, 0, 0, (-1/4), 0, (-1/2), 0, 0, (-1/4), 0, 0, 0, (-1/2), 0, (-1/4), (1/4), 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_02_08 :
    jordan value2 value8 = decode productColumn_02_08 := by
  simp only [value2_decode, value8_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_02_08, column2, column8, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_02_08 :
    productColumn_02_08 = ∑ k : Fin 27, productCoeff_02_08 k • columns k := by
  funext r
  change productColumn_02_08 r = ∑ k : Fin 27, productCoeff_02_08 k * columns k r
  fin_cases r <;> norm_num [productColumn_02_08, productCoeff_02_08, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_02_08 :
    jordan (nativeWords 2) (nativeWords 8) =
      ∑ k : Fin 27, productCoeff_02_08 k • nativeWords k := by
  change jordan value2 value8 = _
  rw [native_product_decode_02_08, productColumn_sum_02_08, decode_sum_columns]

def productCoeff_02_09 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def productColumn_02_09 : Fin 27 → ℝ := ![0, 0, 0, 2, 0, 0, (1/2), 0, (1/2), 0, 0, 0, 2, (-1/2), 0, 0, 0, 0, (1/2), 2, 0, 0, 0, 0, (1/2), (1/2), 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_02_09 :
    jordan value2 value9 = decode productColumn_02_09 := by
  simp only [value2_decode, value9_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_02_09, column2, column9, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_02_09 :
    productColumn_02_09 = ∑ k : Fin 27, productCoeff_02_09 k • columns k := by
  funext r
  change productColumn_02_09 r = ∑ k : Fin 27, productCoeff_02_09 k * columns k r
  fin_cases r <;> norm_num [productColumn_02_09, productCoeff_02_09, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_02_09 :
    jordan (nativeWords 2) (nativeWords 9) =
      ∑ k : Fin 27, productCoeff_02_09 k • nativeWords k := by
  change jordan value2 value9 = _
  rw [native_product_decode_02_09, productColumn_sum_02_09, decode_sum_columns]

end
end Glennie.Compact.NativeWordTableR01
