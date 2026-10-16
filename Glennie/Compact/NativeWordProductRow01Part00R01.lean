/- Native word row 1 product certificate, part 0. -/
module
public import Glennie.Compact.NativeWordProductCommonR01

@[expose] public section
namespace Glennie.Compact.NativeWordTableR01
noncomputable section
open Glennie AlbertGeometry.NativeOperatorTrace
open scoped BigOperators Matrix
set_option autoImplicit false

def productCoeff_01_01 : Fin 27 → ℝ := ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def productColumn_01_01 : Fin 27 → ℝ := ![1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_01_01 :
    jordan value1 value1 = decode productColumn_01_01 := by
  simp only [value1_decode, value1_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_01_01, column1, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_01_01 :
    productColumn_01_01 = ∑ k : Fin 27, productCoeff_01_01 k • columns k := by
  funext r
  change productColumn_01_01 r = ∑ k : Fin 27, productCoeff_01_01 k * columns k r
  fin_cases r <;> norm_num [productColumn_01_01, productCoeff_01_01, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_01_01 :
    jordan (nativeWords 1) (nativeWords 1) =
      ∑ k : Fin 27, productCoeff_01_01 k • nativeWords k := by
  change jordan value1 value1 = _
  rw [native_product_decode_01_01, productColumn_sum_01_01, decode_sum_columns]

def productCoeff_01_02 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def productColumn_01_02 : Fin 27 → ℝ := ![0, 0, 0, (-1/2), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (1/2), 0, 0, 0, 0, 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_01_02 :
    jordan value1 value2 = decode productColumn_01_02 := by
  simp only [value1_decode, value2_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_01_02, column1, column2, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_01_02 :
    productColumn_01_02 = ∑ k : Fin 27, productCoeff_01_02 k • columns k := by
  funext r
  change productColumn_01_02 r = ∑ k : Fin 27, productCoeff_01_02 k * columns k r
  fin_cases r <;> norm_num [productColumn_01_02, productCoeff_01_02, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_01_02 :
    jordan (nativeWords 1) (nativeWords 2) =
      ∑ k : Fin 27, productCoeff_01_02 k • nativeWords k := by
  change jordan value1 value2 = _
  rw [native_product_decode_01_02, productColumn_sum_01_02, decode_sum_columns]

def productCoeff_01_03 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def productColumn_01_03 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, (-1/2), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1/2), 0, 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_01_03 :
    jordan value1 value3 = decode productColumn_01_03 := by
  simp only [value1_decode, value3_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_01_03, column1, column3, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_01_03 :
    productColumn_01_03 = ∑ k : Fin 27, productCoeff_01_03 k • columns k := by
  funext r
  change productColumn_01_03 r = ∑ k : Fin 27, productCoeff_01_03 k * columns k r
  fin_cases r <;> norm_num [productColumn_01_03, productCoeff_01_03, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_01_03 :
    jordan (nativeWords 1) (nativeWords 3) =
      ∑ k : Fin 27, productCoeff_01_03 k • nativeWords k := by
  change jordan value1 value3 = _
  rw [native_product_decode_01_03, productColumn_sum_01_03, decode_sum_columns]

def productCoeff_01_04 : Fin 27 → ℝ := ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def productColumn_01_04 : Fin 27 → ℝ := ![-1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_01_04 :
    jordan value1 value4 = decode productColumn_01_04 := by
  simp only [value1_decode, value4_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_01_04, column1, column4, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_01_04 :
    productColumn_01_04 = ∑ k : Fin 27, productCoeff_01_04 k • columns k := by
  funext r
  change productColumn_01_04 r = ∑ k : Fin 27, productCoeff_01_04 k * columns k r
  fin_cases r <;> norm_num [productColumn_01_04, productCoeff_01_04, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_01_04 :
    jordan (nativeWords 1) (nativeWords 4) =
      ∑ k : Fin 27, productCoeff_01_04 k • nativeWords k := by
  change jordan value1 value4 = _
  rw [native_product_decode_01_04, productColumn_sum_01_04, decode_sum_columns]

def productCoeff_01_05 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def productColumn_01_05 : Fin 27 → ℝ := ![0, 0, 0, (1/4), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (1/4), 0, 0, 0, 0, 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_01_05 :
    jordan value1 value5 = decode productColumn_01_05 := by
  simp only [value1_decode, value5_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_01_05, column1, column5, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_01_05 :
    productColumn_01_05 = ∑ k : Fin 27, productCoeff_01_05 k • columns k := by
  funext r
  change productColumn_01_05 r = ∑ k : Fin 27, productCoeff_01_05 k * columns k r
  fin_cases r <;> norm_num [productColumn_01_05, productCoeff_01_05, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_01_05 :
    jordan (nativeWords 1) (nativeWords 5) =
      ∑ k : Fin 27, productCoeff_01_05 k • nativeWords k := by
  change jordan value1 value5 = _
  rw [native_product_decode_01_05, productColumn_sum_01_05, decode_sum_columns]

def productCoeff_01_06 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def productColumn_01_06 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, (1/4), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1/4), 0, 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_01_06 :
    jordan value1 value6 = decode productColumn_01_06 := by
  simp only [value1_decode, value6_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_01_06, column1, column6, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_01_06 :
    productColumn_01_06 = ∑ k : Fin 27, productCoeff_01_06 k • columns k := by
  funext r
  change productColumn_01_06 r = ∑ k : Fin 27, productCoeff_01_06 k * columns k r
  fin_cases r <;> norm_num [productColumn_01_06, productCoeff_01_06, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_01_06 :
    jordan (nativeWords 1) (nativeWords 6) =
      ∑ k : Fin 27, productCoeff_01_06 k • nativeWords k := by
  change jordan value1 value6 = _
  rw [native_product_decode_01_06, productColumn_sum_01_06, decode_sum_columns]

def productCoeff_01_07 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def productColumn_01_07 : Fin 27 → ℝ := ![-2, 0, 2, 0, (-1/2), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (1/2), 0, 0, 0, 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_01_07 :
    jordan value1 value7 = decode productColumn_01_07 := by
  simp only [value1_decode, value7_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_01_07, column1, column7, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_01_07 :
    productColumn_01_07 = ∑ k : Fin 27, productCoeff_01_07 k • columns k := by
  funext r
  change productColumn_01_07 r = ∑ k : Fin 27, productCoeff_01_07 k * columns k r
  fin_cases r <;> norm_num [productColumn_01_07, productCoeff_01_07, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_01_07 :
    jordan (nativeWords 1) (nativeWords 7) =
      ∑ k : Fin 27, productCoeff_01_07 k • nativeWords k := by
  change jordan value1 value7 = _
  rw [native_product_decode_01_07, productColumn_sum_01_07, decode_sum_columns]

def productCoeff_01_08 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def productColumn_01_08 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, (1/4), 0, (1/4), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1/4), 0, 0, (-1/4)]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_01_08 :
    jordan value1 value8 = decode productColumn_01_08 := by
  simp only [value1_decode, value8_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_01_08, column1, column8, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_01_08 :
    productColumn_01_08 = ∑ k : Fin 27, productCoeff_01_08 k • columns k := by
  funext r
  change productColumn_01_08 r = ∑ k : Fin 27, productCoeff_01_08 k * columns k r
  fin_cases r <;> norm_num [productColumn_01_08, productCoeff_01_08, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_01_08 :
    jordan (nativeWords 1) (nativeWords 8) =
      ∑ k : Fin 27, productCoeff_01_08 k • nativeWords k := by
  change jordan value1 value8 = _
  rw [native_product_decode_01_08, productColumn_sum_01_08, decode_sum_columns]

end
end Glennie.Compact.NativeWordTableR01
