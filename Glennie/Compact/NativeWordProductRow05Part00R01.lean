/- Native word row 5 product certificate, part 0. -/
module
public import Glennie.Compact.NativeWordProductCommonR01

@[expose] public section
namespace Glennie.Compact.NativeWordTableR01
noncomputable section
open Glennie AlbertGeometry.NativeOperatorTrace
open scoped BigOperators Matrix
set_option autoImplicit false

def productCoeff_05_05 : Fin 27 → ℝ := ![0, 0, 0, 0, (3/4), 0, 0, (1/4), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1/2), 0, 0, 0, 0, 0, 0, 0, 0]
def productColumn_05_05 : Fin 27 → ℝ := ![(1/4), (1/2), (1/4), 0, 0, 0, 0, 0, 0, 0, 0, (-1/4), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_05_05 :
    jordan value5 value5 = decode productColumn_05_05 := by
  simp only [value5_decode, value5_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_05_05, column5, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_05_05 :
    productColumn_05_05 = ∑ k : Fin 27, productCoeff_05_05 k • columns k := by
  funext r
  change productColumn_05_05 r = ∑ k : Fin 27, productCoeff_05_05 k * columns k r
  fin_cases r <;> norm_num [productColumn_05_05, productCoeff_05_05, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_05_05 :
    jordan (nativeWords 5) (nativeWords 5) =
      ∑ k : Fin 27, productCoeff_05_05 k • nativeWords k := by
  change jordan value5 value5 = _
  rw [native_product_decode_05_05, productColumn_sum_05_05, decode_sum_columns]

def productCoeff_05_06 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, 0, 0, (1/4), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1/2), 0, 0, 0, 0, 0, 0, 0]
def productColumn_05_06 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (1/8), 0, 0, (-1/8), 0, 0, 0, 0, 0, 0, 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_05_06 :
    jordan value5 value6 = decode productColumn_05_06 := by
  simp only [value5_decode, value6_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_05_06, column5, column6, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_05_06 :
    productColumn_05_06 = ∑ k : Fin 27, productCoeff_05_06 k • columns k := by
  funext r
  change productColumn_05_06 r = ∑ k : Fin 27, productCoeff_05_06 k * columns k r
  fin_cases r <;> norm_num [productColumn_05_06, productCoeff_05_06, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_05_06 :
    jordan (nativeWords 5) (nativeWords 6) =
      ∑ k : Fin 27, productCoeff_05_06 k • nativeWords k := by
  change jordan value5 value6 = _
  rw [native_product_decode_05_06, productColumn_sum_05_06, decode_sum_columns]

def productCoeff_05_07 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, (3/2), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def productColumn_05_07 : Fin 27 → ℝ := ![0, 0, 0, (-3/4), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (3/4), 0, 0, 0, 0, 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_05_07 :
    jordan value5 value7 = decode productColumn_05_07 := by
  simp only [value5_decode, value7_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_05_07, column5, column7, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_05_07 :
    productColumn_05_07 = ∑ k : Fin 27, productCoeff_05_07 k • columns k := by
  funext r
  change productColumn_05_07 r = ∑ k : Fin 27, productCoeff_05_07 k * columns k r
  fin_cases r <;> norm_num [productColumn_05_07, productCoeff_05_07, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_05_07 :
    jordan (nativeWords 5) (nativeWords 7) =
      ∑ k : Fin 27, productCoeff_05_07 k • nativeWords k := by
  change jordan value5 value7 = _
  rw [native_product_decode_05_07, productColumn_sum_05_07, decode_sum_columns]

def productCoeff_05_08 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
def productColumn_05_08 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, (-1/8), 0, 0, (1/8), 0, 0, 0, (-1/8), 0, 0, 0, 0, (1/8), 0, 0, 0, (1/8), 0, 0, (-1/8), 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_05_08 :
    jordan value5 value8 = decode productColumn_05_08 := by
  simp only [value5_decode, value8_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_05_08, column5, column8, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_05_08 :
    productColumn_05_08 = ∑ k : Fin 27, productCoeff_05_08 k • columns k := by
  funext r
  change productColumn_05_08 r = ∑ k : Fin 27, productCoeff_05_08 k * columns k r
  fin_cases r <;> norm_num [productColumn_05_08, productCoeff_05_08, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_05_08 :
    jordan (nativeWords 5) (nativeWords 8) =
      ∑ k : Fin 27, productCoeff_05_08 k • nativeWords k := by
  change jordan value5 value8 = _
  rw [native_product_decode_05_08, productColumn_sum_05_08, decode_sum_columns]

def productCoeff_05_09 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]
def productColumn_05_09 : Fin 27 → ℝ := ![0, 0, 0, -1, 0, 0, 0, 0, (1/4), 0, 0, 0, 0, (1/4), 0, 0, 0, 0, (1/4), 1, 0, 0, 0, 0, (-1/4), 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_05_09 :
    jordan value5 value9 = decode productColumn_05_09 := by
  simp only [value5_decode, value9_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_05_09, column5, column9, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_05_09 :
    productColumn_05_09 = ∑ k : Fin 27, productCoeff_05_09 k • columns k := by
  funext r
  change productColumn_05_09 r = ∑ k : Fin 27, productCoeff_05_09 k * columns k r
  fin_cases r <;> norm_num [productColumn_05_09, productCoeff_05_09, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_05_09 :
    jordan (nativeWords 5) (nativeWords 9) =
      ∑ k : Fin 27, productCoeff_05_09 k • nativeWords k := by
  change jordan value5 value9 = _
  rw [native_product_decode_05_09, productColumn_sum_05_09, decode_sum_columns]

def productCoeff_05_10 : Fin 27 → ℝ := ![0, (1/8), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def productColumn_05_10 : Fin 27 → ℝ := ![(-1/8), 0, (1/8), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_05_10 :
    jordan value5 value10 = decode productColumn_05_10 := by
  simp only [value5_decode, value10_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_05_10, column5, column10, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_05_10 :
    productColumn_05_10 = ∑ k : Fin 27, productCoeff_05_10 k • columns k := by
  funext r
  change productColumn_05_10 r = ∑ k : Fin 27, productCoeff_05_10 k * columns k r
  fin_cases r <;> norm_num [productColumn_05_10, productCoeff_05_10, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_05_10 :
    jordan (nativeWords 5) (nativeWords 10) =
      ∑ k : Fin 27, productCoeff_05_10 k • nativeWords k := by
  change jordan value5 value10 = _
  rw [native_product_decode_05_10, productColumn_sum_05_10, decode_sum_columns]

def productCoeff_05_11 : Fin 27 → ℝ := ![(-1/6), 0, 0, 0, 0, 0, 0, (1/12), 0, (1/12), 0, 0, 0, (-1/12), 0, (-1/6), 0, 0, 0, 0, 0, 0, 0, (-1/24), 0, 0, 0]
def productColumn_05_11 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (1/16), 0, 0, (1/16), 0, 0, 0, 0, 0, 0, 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_05_11 :
    jordan value5 value11 = decode productColumn_05_11 := by
  simp only [value5_decode, value11_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_05_11, column5, column11, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_05_11 :
    productColumn_05_11 = ∑ k : Fin 27, productCoeff_05_11 k • columns k := by
  funext r
  change productColumn_05_11 r = ∑ k : Fin 27, productCoeff_05_11 k * columns k r
  fin_cases r <;> norm_num [productColumn_05_11, productCoeff_05_11, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_05_11 :
    jordan (nativeWords 5) (nativeWords 11) =
      ∑ k : Fin 27, productCoeff_05_11 k • nativeWords k := by
  change jordan value5 value11 = _
  rw [native_product_decode_05_11, productColumn_sum_05_11, decode_sum_columns]

def productCoeff_05_12 : Fin 27 → ℝ := ![0, 0, (-1/4), 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def productColumn_05_12 : Fin 27 → ℝ := ![0, 0, 0, (1/2), 0, 0, 0, 0, 0, 0, 0, 0, (-1/4), 0, 0, 0, 0, 0, 0, (1/2), 0, 0, 0, 0, 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_05_12 :
    jordan value5 value12 = decode productColumn_05_12 := by
  simp only [value5_decode, value12_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_05_12, column5, column12, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_05_12 :
    productColumn_05_12 = ∑ k : Fin 27, productCoeff_05_12 k • columns k := by
  funext r
  change productColumn_05_12 r = ∑ k : Fin 27, productCoeff_05_12 k * columns k r
  fin_cases r <;> norm_num [productColumn_05_12, productCoeff_05_12, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_05_12 :
    jordan (nativeWords 5) (nativeWords 12) =
      ∑ k : Fin 27, productCoeff_05_12 k • nativeWords k := by
  change jordan value5 value12 = _
  rw [native_product_decode_05_12, productColumn_sum_05_12, decode_sum_columns]

end
end Glennie.Compact.NativeWordTableR01
