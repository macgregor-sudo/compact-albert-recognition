/- Native word row 2 product certificate, part 1. -/
module
public import Glennie.Compact.NativeWordProductCommonR01

@[expose] public section
namespace Glennie.Compact.NativeWordTableR01
noncomputable section
open Glennie AlbertGeometry.NativeOperatorTrace
open scoped BigOperators Matrix
set_option autoImplicit false

def productCoeff_02_10 : Fin 27 → ℝ := ![(1/2), 0, 0, 0, (-3/4), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (1/4), 0, 0, 0, 0, 0, 0, 0, 0]
def productColumn_02_10 : Fin 27 → ℝ := ![(1/4), (1/2), (1/4), 0, (1/8), 0, 0, 0, 0, 0, 0, (1/4), 0, 0, 0, 0, 0, 0, 0, 0, (1/8), 0, 0, 0, 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_02_10 :
    jordan value2 value10 = decode productColumn_02_10 := by
  simp only [value2_decode, value10_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_02_10, column2, column10, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_02_10 :
    productColumn_02_10 = ∑ k : Fin 27, productCoeff_02_10 k • columns k := by
  funext r
  change productColumn_02_10 r = ∑ k : Fin 27, productCoeff_02_10 k * columns k r
  fin_cases r <;> norm_num [productColumn_02_10, productCoeff_02_10, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_02_10 :
    jordan (nativeWords 2) (nativeWords 10) =
      ∑ k : Fin 27, productCoeff_02_10 k • nativeWords k := by
  change jordan value2 value10 = _
  rw [native_product_decode_02_10, productColumn_sum_02_10, decode_sum_columns]

def productCoeff_02_11 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, 0, 0, (-1/4), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (1/2), 0, 0, 0, 0, -1, 0, 0]
def productColumn_02_11 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, (-1/8), 0, 0, 0, 0, 0, 0, 0, 0, (-1/8), 0, 0, (1/8), 0, 0, 0, 0, 0, 0, 0, 0, (-1/8)]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_02_11 :
    jordan value2 value11 = decode productColumn_02_11 := by
  simp only [value2_decode, value11_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_02_11, column2, column11, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_02_11 :
    productColumn_02_11 = ∑ k : Fin 27, productCoeff_02_11 k • columns k := by
  funext r
  change productColumn_02_11 r = ∑ k : Fin 27, productCoeff_02_11 k * columns k r
  fin_cases r <;> norm_num [productColumn_02_11, productCoeff_02_11, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_02_11 :
    jordan (nativeWords 2) (nativeWords 11) =
      ∑ k : Fin 27, productCoeff_02_11 k • nativeWords k := by
  change jordan value2 value11 = _
  rw [native_product_decode_02_11, productColumn_sum_02_11, decode_sum_columns]

def productCoeff_02_12 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, (3/2), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def productColumn_02_12 : Fin 27 → ℝ := ![0, 0, 0, (-3/4), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (3/4), 0, 0, 0, 0, 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_02_12 :
    jordan value2 value12 = decode productColumn_02_12 := by
  simp only [value2_decode, value12_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_02_12, column2, column12, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_02_12 :
    productColumn_02_12 = ∑ k : Fin 27, productCoeff_02_12 k • columns k := by
  funext r
  change productColumn_02_12 r = ∑ k : Fin 27, productCoeff_02_12 k * columns k r
  fin_cases r <;> norm_num [productColumn_02_12, productCoeff_02_12, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_02_12 :
    jordan (nativeWords 2) (nativeWords 12) =
      ∑ k : Fin 27, productCoeff_02_12 k • nativeWords k := by
  change jordan value2 value12 = _
  rw [native_product_decode_02_12, productColumn_sum_02_12, decode_sum_columns]

def productCoeff_02_13 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, -1, 0]
def productColumn_02_13 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, 0, 0, (1/8), (1/8), 0, 0, 0, (1/8), 0, 0, 0, 0, (-1/8), 0, 0, 0, (1/8), 0, (1/8), 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_02_13 :
    jordan value2 value13 = decode productColumn_02_13 := by
  simp only [value2_decode, value13_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_02_13, column2, column13, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_02_13 :
    productColumn_02_13 = ∑ k : Fin 27, productCoeff_02_13 k • columns k := by
  funext r
  change productColumn_02_13 r = ∑ k : Fin 27, productCoeff_02_13 k * columns k r
  fin_cases r <;> norm_num [productColumn_02_13, productCoeff_02_13, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_02_13 :
    jordan (nativeWords 2) (nativeWords 13) =
      ∑ k : Fin 27, productCoeff_02_13 k • nativeWords k := by
  change jordan value2 value13 = _
  rw [native_product_decode_02_13, productColumn_sum_02_13, decode_sum_columns]

def productCoeff_02_14 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, -1]
def productColumn_02_14 : Fin 27 → ℝ := ![0, 0, 0, -1, 0, 0, (1/4), 0, 0, 0, 0, 0, 0, (-1/4), 0, 0, 0, 0, (-1/4), 1, 0, 0, 0, 0, 0, (-1/4), 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_02_14 :
    jordan value2 value14 = decode productColumn_02_14 := by
  simp only [value2_decode, value14_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_02_14, column2, column14, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_02_14 :
    productColumn_02_14 = ∑ k : Fin 27, productCoeff_02_14 k • columns k := by
  funext r
  change productColumn_02_14 r = ∑ k : Fin 27, productCoeff_02_14 k * columns k r
  fin_cases r <;> norm_num [productColumn_02_14, productCoeff_02_14, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_02_14 :
    jordan (nativeWords 2) (nativeWords 14) =
      ∑ k : Fin 27, productCoeff_02_14 k • nativeWords k := by
  change jordan value2 value14 = _
  rw [native_product_decode_02_14, productColumn_sum_02_14, decode_sum_columns]

def productCoeff_02_15 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, (3/4), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
def productColumn_02_15 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, (-1/8), 0, 0, (-1/4), 0, 0, 0, (-1/8), 0, 0, 0, 0, (1/8), 0, 0, 0, (-1/4), 0, 0, (-1/8), 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_02_15 :
    jordan value2 value15 = decode productColumn_02_15 := by
  simp only [value2_decode, value15_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_02_15, column2, column15, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_02_15 :
    productColumn_02_15 = ∑ k : Fin 27, productCoeff_02_15 k • columns k := by
  funext r
  change productColumn_02_15 r = ∑ k : Fin 27, productCoeff_02_15 k * columns k r
  fin_cases r <;> norm_num [productColumn_02_15, productCoeff_02_15, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_02_15 :
    jordan (nativeWords 2) (nativeWords 15) =
      ∑ k : Fin 27, productCoeff_02_15 k • nativeWords k := by
  change jordan value2 value15 = _
  rw [native_product_decode_02_15, productColumn_sum_02_15, decode_sum_columns]

def productCoeff_02_16 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, 0, 0, (3/4), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def productColumn_02_16 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, (-3/8), 0, (-3/8), 0, 0, 0, 0, 0, 0, (-3/8), 0, 0, (3/8), 0, 0, 0, 0, 0, (-3/8), 0, 0, (-3/8)]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_02_16 :
    jordan value2 value16 = decode productColumn_02_16 := by
  simp only [value2_decode, value16_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_02_16, column2, column16, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_02_16 :
    productColumn_02_16 = ∑ k : Fin 27, productCoeff_02_16 k • columns k := by
  funext r
  change productColumn_02_16 r = ∑ k : Fin 27, productCoeff_02_16 k * columns k r
  fin_cases r <;> norm_num [productColumn_02_16, productCoeff_02_16, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_02_16 :
    jordan (nativeWords 2) (nativeWords 16) =
      ∑ k : Fin 27, productCoeff_02_16 k • nativeWords k := by
  change jordan value2 value16 = _
  rw [native_product_decode_02_16, productColumn_sum_02_16, decode_sum_columns]

def productCoeff_02_17 : Fin 27 → ℝ := ![-3, 0, 0, 0, 0, 0, 0, 3, 0, (3/2), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1/2), 0, 0, 0]
def productColumn_02_17 : Fin 27 → ℝ := ![4, 4, 4, 0, 2, (-1/4), 0, (1/4), 0, 0, (1/2), 2, 0, 0, (1/4), 0, (1/2), (1/4), 0, 0, 2, (-1/2), 0, (-1/4), 0, 0, (1/4)]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_02_17 :
    jordan value2 value17 = decode productColumn_02_17 := by
  simp only [value2_decode, value17_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_02_17, column2, column17, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_02_17 :
    productColumn_02_17 = ∑ k : Fin 27, productCoeff_02_17 k • columns k := by
  funext r
  change productColumn_02_17 r = ∑ k : Fin 27, productCoeff_02_17 k * columns k r
  fin_cases r <;> norm_num [productColumn_02_17, productCoeff_02_17, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_02_17 :
    jordan (nativeWords 2) (nativeWords 17) =
      ∑ k : Fin 27, productCoeff_02_17 k • nativeWords k := by
  change jordan value2 value17 = _
  rw [native_product_decode_02_17, productColumn_sum_02_17, decode_sum_columns]

end
end Glennie.Compact.NativeWordTableR01
