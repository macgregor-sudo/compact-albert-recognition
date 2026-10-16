/- Native word row 3 product certificate, part 1. -/
module
public import Glennie.Compact.NativeWordProductCommonR01

@[expose] public section
namespace Glennie.Compact.NativeWordTableR01
noncomputable section
open Glennie AlbertGeometry.NativeOperatorTrace
open scoped BigOperators Matrix
set_option autoImplicit false

def productCoeff_03_11 : Fin 27 → ℝ := ![(1/2), 0, 0, 0, (-3/4), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (1/4), 0, 0, 0, 0, 0, 0]
def productColumn_03_11 : Fin 27 → ℝ := ![(1/4), (1/2), (1/4), 0, 0, 0, 0, 0, 0, 0, (1/8), 0, 0, 0, 0, 0, (1/4), 0, 0, 0, 0, (-1/8), 0, 0, 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_03_11 :
    jordan value3 value11 = decode productColumn_03_11 := by
  simp only [value3_decode, value11_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_03_11, column3, column11, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_03_11 :
    productColumn_03_11 = ∑ k : Fin 27, productCoeff_03_11 k • columns k := by
  funext r
  change productColumn_03_11 r = ∑ k : Fin 27, productCoeff_03_11 k * columns k r
  fin_cases r <;> norm_num [productColumn_03_11, productCoeff_03_11, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_03_11 :
    jordan (nativeWords 3) (nativeWords 11) =
      ∑ k : Fin 27, productCoeff_03_11 k • nativeWords k := by
  change jordan value3 value11 = _
  rw [native_product_decode_03_11, productColumn_sum_03_11, decode_sum_columns]

def productCoeff_03_12 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, (3/2), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0]
def productColumn_03_12 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, 0, 0, (-1/4), -1, 0, 0, 0, (-1/4), 0, 0, 0, 0, (1/4), 0, 0, 0, -1, 0, (-1/4), 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_03_12 :
    jordan value3 value12 = decode productColumn_03_12 := by
  simp only [value3_decode, value12_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_03_12, column3, column12, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_03_12 :
    productColumn_03_12 = ∑ k : Fin 27, productCoeff_03_12 k • columns k := by
  funext r
  change productColumn_03_12 r = ∑ k : Fin 27, productCoeff_03_12 k * columns k r
  fin_cases r <;> norm_num [productColumn_03_12, productCoeff_03_12, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_03_12 :
    jordan (nativeWords 3) (nativeWords 12) =
      ∑ k : Fin 27, productCoeff_03_12 k • nativeWords k := by
  change jordan value3 value12 = _
  rw [native_product_decode_03_12, productColumn_sum_03_12, decode_sum_columns]

def productCoeff_03_13 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, (-9/4), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (1/2), 0, 0, 0, (1/2)]
def productColumn_03_13 : Fin 27 → ℝ := ![0, 0, 0, (1/8), 0, 0, (-1/8), 0, 0, 0, 0, 0, 0, (1/8), 0, 0, 0, 0, (1/8), (-1/8), 0, 0, 0, 0, 0, (1/8), 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_03_13 :
    jordan value3 value13 = decode productColumn_03_13 := by
  simp only [value3_decode, value13_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_03_13, column3, column13, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_03_13 :
    productColumn_03_13 = ∑ k : Fin 27, productCoeff_03_13 k • columns k := by
  funext r
  change productColumn_03_13 r = ∑ k : Fin 27, productCoeff_03_13 k * columns k r
  fin_cases r <;> norm_num [productColumn_03_13, productCoeff_03_13, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_03_13 :
    jordan (nativeWords 3) (nativeWords 13) =
      ∑ k : Fin 27, productCoeff_03_13 k • nativeWords k := by
  change jordan value3 value13 = _
  rw [native_product_decode_03_13, productColumn_sum_03_13, decode_sum_columns]

def productCoeff_03_14 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, (3/2), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def productColumn_03_14 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, (-3/4), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-3/4), 0, 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_03_14 :
    jordan value3 value14 = decode productColumn_03_14 := by
  simp only [value3_decode, value14_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_03_14, column3, column14, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_03_14 :
    productColumn_03_14 = ∑ k : Fin 27, productCoeff_03_14 k • columns k := by
  funext r
  change productColumn_03_14 r = ∑ k : Fin 27, productCoeff_03_14 k * columns k r
  fin_cases r <;> norm_num [productColumn_03_14, productCoeff_03_14, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_03_14 :
    jordan (nativeWords 3) (nativeWords 14) =
      ∑ k : Fin 27, productCoeff_03_14 k • nativeWords k := by
  change jordan value3 value14 = _
  rw [native_product_decode_03_14, productColumn_sum_03_14, decode_sum_columns]

def productCoeff_03_15 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, (3/4), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1/2)]
def productColumn_03_15 : Fin 27 → ℝ := ![0, 0, 0, (1/8), 0, 0, (1/8), 0, (1/8), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1/8), 0, 0, 0, 0, (-1/8), (-1/8), 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_03_15 :
    jordan value3 value15 = decode productColumn_03_15 := by
  simp only [value3_decode, value15_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_03_15, column3, column15, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_03_15 :
    productColumn_03_15 = ∑ k : Fin 27, productCoeff_03_15 k • columns k := by
  funext r
  change productColumn_03_15 r = ∑ k : Fin 27, productCoeff_03_15 k * columns k r
  fin_cases r <;> norm_num [productColumn_03_15, productCoeff_03_15, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_03_15 :
    jordan (nativeWords 3) (nativeWords 15) =
      ∑ k : Fin 27, productCoeff_03_15 k • nativeWords k := by
  change jordan value3 value15 = _
  rw [native_product_decode_03_15, productColumn_sum_03_15, decode_sum_columns]

def productCoeff_03_16 : Fin 27 → ℝ := ![(3/2), 0, 0, 0, 0, 0, 0, (-3/4), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (1/4), 0, 0, 0]
def productColumn_03_16 : Fin 27 → ℝ := ![1, 1, 1, 0, (-1/4), (1/8), 0, (-1/8), 0, 0, (1/2), (-1/4), 0, 0, (-1/8), 0, (1/2), (-1/8), 0, 0, (-1/4), (-1/2), 0, (1/8), 0, 0, (-1/8)]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_03_16 :
    jordan value3 value16 = decode productColumn_03_16 := by
  simp only [value3_decode, value16_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_03_16, column3, column16, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_03_16 :
    productColumn_03_16 = ∑ k : Fin 27, productCoeff_03_16 k • columns k := by
  funext r
  change productColumn_03_16 r = ∑ k : Fin 27, productCoeff_03_16 k * columns k r
  fin_cases r <;> norm_num [productColumn_03_16, productCoeff_03_16, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_03_16 :
    jordan (nativeWords 3) (nativeWords 16) =
      ∑ k : Fin 27, productCoeff_03_16 k • nativeWords k := by
  change jordan value3 value16 = _
  rw [native_product_decode_03_16, productColumn_sum_03_16, decode_sum_columns]

def productCoeff_03_17 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, 0, 0, (3/2), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def productColumn_03_17 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, (-3/4), 0, (-3/4), 0, 0, 0, 0, 0, 0, (-3/4), 0, 0, (3/4), 0, 0, 0, 0, 0, (-3/4), 0, 0, (-3/4)]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_03_17 :
    jordan value3 value17 = decode productColumn_03_17 := by
  simp only [value3_decode, value17_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_03_17, column3, column17, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_03_17 :
    productColumn_03_17 = ∑ k : Fin 27, productCoeff_03_17 k • columns k := by
  funext r
  change productColumn_03_17 r = ∑ k : Fin 27, productCoeff_03_17 k * columns k r
  fin_cases r <;> norm_num [productColumn_03_17, productCoeff_03_17, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_03_17 :
    jordan (nativeWords 3) (nativeWords 17) =
      ∑ k : Fin 27, productCoeff_03_17 k • nativeWords k := by
  change jordan value3 value17 = _
  rw [native_product_decode_03_17, productColumn_sum_03_17, decode_sum_columns]

def productCoeff_03_18 : Fin 27 → ℝ := ![0, 0, 0, (8/3), 0, 2, 0, 0, 0, 0, 0, -4, 0, 0, 0, 0, (-4/3), 0, 0, 0, 0, 0, (-1/3), 0, 0, 0, (-2/3)]
def productColumn_03_18 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, (1/2), 0, (-1/4), 1, 0, 0, 0, (1/4), 0, -2, 0, 0, (1/4), 0, 0, 0, -1, 0, (1/4), (-1/2), 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_03_18 :
    jordan value3 value18 = decode productColumn_03_18 := by
  simp only [value3_decode, value18_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_03_18, column3, column18, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_03_18 :
    productColumn_03_18 = ∑ k : Fin 27, productCoeff_03_18 k • columns k := by
  funext r
  change productColumn_03_18 r = ∑ k : Fin 27, productCoeff_03_18 k * columns k r
  fin_cases r <;> norm_num [productColumn_03_18, productCoeff_03_18, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_03_18 :
    jordan (nativeWords 3) (nativeWords 18) =
      ∑ k : Fin 27, productCoeff_03_18 k • nativeWords k := by
  change jordan value3 value18 = _
  rw [native_product_decode_03_18, productColumn_sum_03_18, decode_sum_columns]

end
end Glennie.Compact.NativeWordTableR01
