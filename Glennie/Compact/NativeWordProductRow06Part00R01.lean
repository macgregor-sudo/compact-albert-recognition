/- Native word row 6 product certificate, part 0. -/
module
public import Glennie.Compact.NativeWordProductCommonR01

@[expose] public section
namespace Glennie.Compact.NativeWordTableR01
noncomputable section
open Glennie AlbertGeometry.NativeOperatorTrace
open scoped BigOperators Matrix
set_option autoImplicit false

def productCoeff_06_06 : Fin 27 → ℝ := ![0, 0, 0, 0, (3/4), 0, 0, 0, 0, (1/4), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1/2), 0, 0, 0, 0, 0, 0]
def productColumn_06_06 : Fin 27 → ℝ := ![(1/4), (1/2), (1/4), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1/4), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_06_06 :
    jordan value6 value6 = decode productColumn_06_06 := by
  simp only [value6_decode, value6_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_06_06, column6, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_06_06 :
    productColumn_06_06 = ∑ k : Fin 27, productCoeff_06_06 k • columns k := by
  funext r
  change productColumn_06_06 r = ∑ k : Fin 27, productCoeff_06_06 k * columns k r
  fin_cases r <;> norm_num [productColumn_06_06, productCoeff_06_06, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_06_06 :
    jordan (nativeWords 6) (nativeWords 6) =
      ∑ k : Fin 27, productCoeff_06_06 k • nativeWords k := by
  change jordan value6 value6 = _
  rw [native_product_decode_06_06, productColumn_sum_06_06, decode_sum_columns]

def productCoeff_06_07 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, (3/2), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0]
def productColumn_06_07 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, (1/4), 0, 0, -1, 0, 0, 0, (1/4), 0, 0, 0, 0, (-1/4), 0, 0, 0, -1, 0, 0, (1/4), 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_06_07 :
    jordan value6 value7 = decode productColumn_06_07 := by
  simp only [value6_decode, value7_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_06_07, column6, column7, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_06_07 :
    productColumn_06_07 = ∑ k : Fin 27, productCoeff_06_07 k • columns k := by
  funext r
  change productColumn_06_07 r = ∑ k : Fin 27, productCoeff_06_07 k * columns k r
  fin_cases r <;> norm_num [productColumn_06_07, productCoeff_06_07, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_06_07 :
    jordan (nativeWords 6) (nativeWords 7) =
      ∑ k : Fin 27, productCoeff_06_07 k • nativeWords k := by
  change jordan value6 value7 = _
  rw [native_product_decode_06_07, productColumn_sum_06_07, decode_sum_columns]

def productCoeff_06_08 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, (3/4), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1/2), 0, 0, 0, 0]
def productColumn_06_08 : Fin 27 → ℝ := ![0, 0, 0, (1/8), 0, 0, 0, 0, (-1/8), 0, 0, 0, 0, (-1/8), 0, 0, 0, 0, (-1/8), (-1/8), 0, 0, 0, 0, (1/8), 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_06_08 :
    jordan value6 value8 = decode productColumn_06_08 := by
  simp only [value6_decode, value8_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_06_08, column6, column8, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_06_08 :
    productColumn_06_08 = ∑ k : Fin 27, productCoeff_06_08 k • columns k := by
  funext r
  change productColumn_06_08 r = ∑ k : Fin 27, productCoeff_06_08 k * columns k r
  fin_cases r <;> norm_num [productColumn_06_08, productCoeff_06_08, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_06_08 :
    jordan (nativeWords 6) (nativeWords 8) =
      ∑ k : Fin 27, productCoeff_06_08 k • nativeWords k := by
  change jordan value6 value8 = _
  rw [native_product_decode_06_08, productColumn_sum_06_08, decode_sum_columns]

def productCoeff_06_09 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, (3/2), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def productColumn_06_09 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, (-3/4), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-3/4), 0, 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_06_09 :
    jordan value6 value9 = decode productColumn_06_09 := by
  simp only [value6_decode, value9_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_06_09, column6, column9, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_06_09 :
    productColumn_06_09 = ∑ k : Fin 27, productCoeff_06_09 k • columns k := by
  funext r
  change productColumn_06_09 r = ∑ k : Fin 27, productCoeff_06_09 k * columns k r
  fin_cases r <;> norm_num [productColumn_06_09, productCoeff_06_09, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_06_09 :
    jordan (nativeWords 6) (nativeWords 9) =
      ∑ k : Fin 27, productCoeff_06_09 k • nativeWords k := by
  change jordan value6 value9 = _
  rw [native_product_decode_06_09, productColumn_sum_06_09, decode_sum_columns]

def productCoeff_06_10 : Fin 27 → ℝ := ![(1/6), 0, 0, 0, 0, 0, 0, (-1/12), 0, (-1/12), 0, 0, 0, (1/12), 0, (1/6), 0, 0, 0, 0, 0, 0, 0, (1/24), 0, 0, 0]
def productColumn_06_10 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1/16), 0, 0, (-1/16), 0, 0, 0, 0, 0, 0, 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_06_10 :
    jordan value6 value10 = decode productColumn_06_10 := by
  simp only [value6_decode, value10_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_06_10, column6, column10, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_06_10 :
    productColumn_06_10 = ∑ k : Fin 27, productCoeff_06_10 k • columns k := by
  funext r
  change productColumn_06_10 r = ∑ k : Fin 27, productCoeff_06_10 k * columns k r
  fin_cases r <;> norm_num [productColumn_06_10, productCoeff_06_10, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_06_10 :
    jordan (nativeWords 6) (nativeWords 10) =
      ∑ k : Fin 27, productCoeff_06_10 k • nativeWords k := by
  change jordan value6 value10 = _
  rw [native_product_decode_06_10, productColumn_sum_06_10, decode_sum_columns]

def productCoeff_06_11 : Fin 27 → ℝ := ![0, (1/8), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def productColumn_06_11 : Fin 27 → ℝ := ![(-1/8), 0, (1/8), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_06_11 :
    jordan value6 value11 = decode productColumn_06_11 := by
  simp only [value6_decode, value11_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_06_11, column6, column11, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_06_11 :
    productColumn_06_11 = ∑ k : Fin 27, productCoeff_06_11 k • columns k := by
  funext r
  change productColumn_06_11 r = ∑ k : Fin 27, productCoeff_06_11 k * columns k r
  fin_cases r <;> norm_num [productColumn_06_11, productCoeff_06_11, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_06_11 :
    jordan (nativeWords 6) (nativeWords 11) =
      ∑ k : Fin 27, productCoeff_06_11 k • nativeWords k := by
  change jordan value6 value11 = _
  rw [native_product_decode_06_11, productColumn_sum_06_11, decode_sum_columns]

def productCoeff_06_12 : Fin 27 → ℝ := ![0, 0, 0, (-1/12), 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, (1/6), 0, 0, 0, 0, 0, (-1/3), 0, 0, 0, (-1/6)]
def productColumn_06_12 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, (1/2), 0, 0, 0, (-1/8), 0, 0, 0, 0, (-1/8), 0, 0, 0, (-1/2), 0, 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_06_12 :
    jordan value6 value12 = decode productColumn_06_12 := by
  simp only [value6_decode, value12_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_06_12, column6, column12, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_06_12 :
    productColumn_06_12 = ∑ k : Fin 27, productCoeff_06_12 k • columns k := by
  funext r
  change productColumn_06_12 r = ∑ k : Fin 27, productCoeff_06_12 k * columns k r
  fin_cases r <;> norm_num [productColumn_06_12, productCoeff_06_12, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_06_12 :
    jordan (nativeWords 6) (nativeWords 12) =
      ∑ k : Fin 27, productCoeff_06_12 k • nativeWords k := by
  change jordan value6 value12 = _
  rw [native_product_decode_06_12, productColumn_sum_06_12, decode_sum_columns]

def productCoeff_06_13 : Fin 27 → ℝ := ![0, 0, (-5/24), 0, 0, 0, 0, 0, 0, 0, (1/2), 0, 0, 0, 0, 0, 0, (1/24), 0, 0, 0, (1/3), 0, 0, 0, (1/6), 0]
def productColumn_06_13 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1/8), (-1/16), 0, 0, 0, 0, (1/16), 0, 0, 0, 0, 0, 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_06_13 :
    jordan value6 value13 = decode productColumn_06_13 := by
  simp only [value6_decode, value13_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_06_13, column6, column13, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_06_13 :
    productColumn_06_13 = ∑ k : Fin 27, productCoeff_06_13 k • columns k := by
  funext r
  change productColumn_06_13 r = ∑ k : Fin 27, productCoeff_06_13 k * columns k r
  fin_cases r <;> norm_num [productColumn_06_13, productCoeff_06_13, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_06_13 :
    jordan (nativeWords 6) (nativeWords 13) =
      ∑ k : Fin 27, productCoeff_06_13 k • nativeWords k := by
  change jordan value6 value13 = _
  rw [native_product_decode_06_13, productColumn_sum_06_13, decode_sum_columns]

end
end Glennie.Compact.NativeWordTableR01
