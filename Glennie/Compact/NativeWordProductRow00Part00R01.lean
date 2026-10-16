/- Native word row 0 product certificate, part 0. -/
module
public import Glennie.Compact.NativeWordProductCommonR01

@[expose] public section
namespace Glennie.Compact.NativeWordTableR01
noncomputable section
open Glennie AlbertGeometry.NativeOperatorTrace
open scoped BigOperators Matrix
set_option autoImplicit false

def productCoeff_00_00 : Fin 27 → ℝ := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def productColumn_00_00 : Fin 27 → ℝ := ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_00_00 :
    jordan value0 value0 = decode productColumn_00_00 := by
  simp only [value0_decode, value0_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_00_00, column0, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_00_00 :
    productColumn_00_00 = ∑ k : Fin 27, productCoeff_00_00 k • columns k := by
  funext r
  change productColumn_00_00 r = ∑ k : Fin 27, productCoeff_00_00 k * columns k r
  fin_cases r <;> norm_num [productColumn_00_00, productCoeff_00_00, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_00_00 :
    jordan (nativeWords 0) (nativeWords 0) =
      ∑ k : Fin 27, productCoeff_00_00 k • nativeWords k := by
  change jordan value0 value0 = _
  rw [native_product_decode_00_00, productColumn_sum_00_00, decode_sum_columns]

def productCoeff_00_01 : Fin 27 → ℝ := ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def productColumn_00_01 : Fin 27 → ℝ := ![-1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_00_01 :
    jordan value0 value1 = decode productColumn_00_01 := by
  simp only [value0_decode, value1_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_00_01, column0, column1, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_00_01 :
    productColumn_00_01 = ∑ k : Fin 27, productCoeff_00_01 k • columns k := by
  funext r
  change productColumn_00_01 r = ∑ k : Fin 27, productCoeff_00_01 k * columns k r
  fin_cases r <;> norm_num [productColumn_00_01, productCoeff_00_01, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_00_01 :
    jordan (nativeWords 0) (nativeWords 1) =
      ∑ k : Fin 27, productCoeff_00_01 k • nativeWords k := by
  change jordan value0 value1 = _
  rw [native_product_decode_00_01, productColumn_sum_00_01, decode_sum_columns]

def productCoeff_00_02 : Fin 27 → ℝ := ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def productColumn_00_02 : Fin 27 → ℝ := ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_00_02 :
    jordan value0 value2 = decode productColumn_00_02 := by
  simp only [value0_decode, value2_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_00_02, column0, column2, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_00_02 :
    productColumn_00_02 = ∑ k : Fin 27, productCoeff_00_02 k • columns k := by
  funext r
  change productColumn_00_02 r = ∑ k : Fin 27, productCoeff_00_02 k * columns k r
  fin_cases r <;> norm_num [productColumn_00_02, productCoeff_00_02, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_00_02 :
    jordan (nativeWords 0) (nativeWords 2) =
      ∑ k : Fin 27, productCoeff_00_02 k • nativeWords k := by
  change jordan value0 value2 = _
  rw [native_product_decode_00_02, productColumn_sum_00_02, decode_sum_columns]

def productCoeff_00_03 : Fin 27 → ℝ := ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def productColumn_00_03 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_00_03 :
    jordan value0 value3 = decode productColumn_00_03 := by
  simp only [value0_decode, value3_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_00_03, column0, column3, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_00_03 :
    productColumn_00_03 = ∑ k : Fin 27, productCoeff_00_03 k • columns k := by
  funext r
  change productColumn_00_03 r = ∑ k : Fin 27, productCoeff_00_03 k * columns k r
  fin_cases r <;> norm_num [productColumn_00_03, productCoeff_00_03, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_00_03 :
    jordan (nativeWords 0) (nativeWords 3) =
      ∑ k : Fin 27, productCoeff_00_03 k • nativeWords k := by
  change jordan value0 value3 = _
  rw [native_product_decode_00_03, productColumn_sum_00_03, decode_sum_columns]

def productCoeff_00_04 : Fin 27 → ℝ := ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def productColumn_00_04 : Fin 27 → ℝ := ![1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_00_04 :
    jordan value0 value4 = decode productColumn_00_04 := by
  simp only [value0_decode, value4_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_00_04, column0, column4, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_00_04 :
    productColumn_00_04 = ∑ k : Fin 27, productCoeff_00_04 k • columns k := by
  funext r
  change productColumn_00_04 r = ∑ k : Fin 27, productCoeff_00_04 k * columns k r
  fin_cases r <;> norm_num [productColumn_00_04, productCoeff_00_04, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_00_04 :
    jordan (nativeWords 0) (nativeWords 4) =
      ∑ k : Fin 27, productCoeff_00_04 k • nativeWords k := by
  change jordan value0 value4 = _
  rw [native_product_decode_00_04, productColumn_sum_00_04, decode_sum_columns]

def productCoeff_00_05 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def productColumn_00_05 : Fin 27 → ℝ := ![0, 0, 0, (-1/2), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (1/2), 0, 0, 0, 0, 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_00_05 :
    jordan value0 value5 = decode productColumn_00_05 := by
  simp only [value0_decode, value5_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_00_05, column0, column5, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_00_05 :
    productColumn_00_05 = ∑ k : Fin 27, productCoeff_00_05 k • columns k := by
  funext r
  change productColumn_00_05 r = ∑ k : Fin 27, productCoeff_00_05 k * columns k r
  fin_cases r <;> norm_num [productColumn_00_05, productCoeff_00_05, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_00_05 :
    jordan (nativeWords 0) (nativeWords 5) =
      ∑ k : Fin 27, productCoeff_00_05 k • nativeWords k := by
  change jordan value0 value5 = _
  rw [native_product_decode_00_05, productColumn_sum_00_05, decode_sum_columns]

def productCoeff_00_06 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def productColumn_00_06 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, (-1/2), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1/2), 0, 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_00_06 :
    jordan value0 value6 = decode productColumn_00_06 := by
  simp only [value0_decode, value6_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_00_06, column0, column6, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_00_06 :
    productColumn_00_06 = ∑ k : Fin 27, productCoeff_00_06 k • columns k := by
  funext r
  change productColumn_00_06 r = ∑ k : Fin 27, productCoeff_00_06 k * columns k r
  fin_cases r <;> norm_num [productColumn_00_06, productCoeff_00_06, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_00_06 :
    jordan (nativeWords 0) (nativeWords 6) =
      ∑ k : Fin 27, productCoeff_00_06 k • nativeWords k := by
  change jordan value0 value6 = _
  rw [native_product_decode_00_06, productColumn_sum_00_06, decode_sum_columns]

def productCoeff_00_07 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def productColumn_00_07 : Fin 27 → ℝ := ![2, 2, 2, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_00_07 :
    jordan value0 value7 = decode productColumn_00_07 := by
  simp only [value0_decode, value7_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_00_07, column0, column7, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_00_07 :
    productColumn_00_07 = ∑ k : Fin 27, productCoeff_00_07 k • columns k := by
  funext r
  change productColumn_00_07 r = ∑ k : Fin 27, productCoeff_00_07 k * columns k r
  fin_cases r <;> norm_num [productColumn_00_07, productCoeff_00_07, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_00_07 :
    jordan (nativeWords 0) (nativeWords 7) =
      ∑ k : Fin 27, productCoeff_00_07 k • nativeWords k := by
  change jordan value0 value7 = _
  rw [native_product_decode_00_07, productColumn_sum_00_07, decode_sum_columns]

end
end Glennie.Compact.NativeWordTableR01
