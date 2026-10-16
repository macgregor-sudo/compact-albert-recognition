/- Native word row 7 product certificate, part 1. -/
module
public import Glennie.Compact.NativeWordProductCommonR01

@[expose] public section
namespace Glennie.Compact.NativeWordTableR01
noncomputable section
open Glennie AlbertGeometry.NativeOperatorTrace
open scoped BigOperators Matrix
set_option autoImplicit false

def productCoeff_07_15 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (3/2), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def productColumn_07_15 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, (-3/8), 0, 0, 0, 0, 0, 0, 0, 0, (-3/8), 0, 0, (-3/8), 0, 0, 0, 0, 0, 0, 0, 0, (3/8)]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_07_15 :
    jordan value7 value15 = decode productColumn_07_15 := by
  simp only [value7_decode, value15_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_07_15, column7, column15, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_07_15 :
    productColumn_07_15 = ∑ k : Fin 27, productCoeff_07_15 k • columns k := by
  funext r
  change productColumn_07_15 r = ∑ k : Fin 27, productCoeff_07_15 k * columns k r
  fin_cases r <;> norm_num [productColumn_07_15, productCoeff_07_15, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_07_15 :
    jordan (nativeWords 7) (nativeWords 15) =
      ∑ k : Fin 27, productCoeff_07_15 k • nativeWords k := by
  change jordan value7 value15 = _
  rw [native_product_decode_07_15, productColumn_sum_07_15, decode_sum_columns]

def productCoeff_07_16 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (3/2), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def productColumn_07_16 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, (-3/8), 0, (3/8), (3/4), 0, 0, 0, (-3/8), 0, (-3/4), 0, 0, (-3/8), 0, 0, 0, (-3/4), 0, (-3/8), (3/8), 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_07_16 :
    jordan value7 value16 = decode productColumn_07_16 := by
  simp only [value7_decode, value16_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_07_16, column7, column16, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_07_16 :
    productColumn_07_16 = ∑ k : Fin 27, productCoeff_07_16 k • columns k := by
  funext r
  change productColumn_07_16 r = ∑ k : Fin 27, productCoeff_07_16 k * columns k r
  fin_cases r <;> norm_num [productColumn_07_16, productCoeff_07_16, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_07_16 :
    jordan (nativeWords 7) (nativeWords 16) =
      ∑ k : Fin 27, productCoeff_07_16 k • nativeWords k := by
  change jordan value7 value16 = _
  rw [native_product_decode_07_16, productColumn_sum_07_16, decode_sum_columns]

def productCoeff_07_17 : Fin 27 → ℝ := ![0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (3/2), 0, 0, 0, 0, 0, 0, 0, 0, 0]
def productColumn_07_17 : Fin 27 → ℝ := ![0, 0, 0, 6, 0, 0, (3/4), 0, (3/4), 0, 0, 0, 6, (-3/4), 0, 0, 0, 0, (3/4), 6, 0, 0, 0, 0, (3/4), (3/4), 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_07_17 :
    jordan value7 value17 = decode productColumn_07_17 := by
  simp only [value7_decode, value17_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_07_17, column7, column17, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_07_17 :
    productColumn_07_17 = ∑ k : Fin 27, productCoeff_07_17 k • columns k := by
  funext r
  change productColumn_07_17 r = ∑ k : Fin 27, productCoeff_07_17 k * columns k r
  fin_cases r <;> norm_num [productColumn_07_17, productCoeff_07_17, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_07_17 :
    jordan (nativeWords 7) (nativeWords 17) =
      ∑ k : Fin 27, productCoeff_07_17 k • nativeWords k := by
  change jordan value7 value17 = _
  rw [native_product_decode_07_17, productColumn_sum_07_17, decode_sum_columns]

def productCoeff_07_18 : Fin 27 → ℝ := ![3, 0, 0, 0, (-9/2), 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (9/2), 0, 0, 0, 0, 0, 0, 0, 0]
def productColumn_07_18 : Fin 27 → ℝ := ![(11/2), 1, (11/2), 0, (5/4), 0, 0, 0, 0, 0, 0, (7/2), 0, 0, 0, 0, 0, 0, 0, 0, (5/4), 0, 0, 0, 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_07_18 :
    jordan value7 value18 = decode productColumn_07_18 := by
  simp only [value7_decode, value18_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_07_18, column7, column18, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_07_18 :
    productColumn_07_18 = ∑ k : Fin 27, productCoeff_07_18 k • columns k := by
  funext r
  change productColumn_07_18 r = ∑ k : Fin 27, productCoeff_07_18 k * columns k r
  fin_cases r <;> norm_num [productColumn_07_18, productCoeff_07_18, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_07_18 :
    jordan (nativeWords 7) (nativeWords 18) =
      ∑ k : Fin 27, productCoeff_07_18 k • nativeWords k := by
  change jordan value7 value18 = _
  rw [native_product_decode_07_18, productColumn_sum_07_18, decode_sum_columns]

def productCoeff_07_19 : Fin 27 → ℝ := ![0, (-1/2), 0, 0, 0, 0, 0, 0, (-1/4), 0, 0, 0, 0, 0, (1/4), 0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0]
def productColumn_07_19 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, (-1/4), 0, (-3/8), 0, 0, (-1/8), 0, 0, 0, (-7/8), 0, 0, (7/8), 0, 0, 0, (-1/8), 0, (-3/8), 0, 0, (-1/4)]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_07_19 :
    jordan value7 value19 = decode productColumn_07_19 := by
  simp only [value7_decode, value19_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_07_19, column7, column19, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_07_19 :
    productColumn_07_19 = ∑ k : Fin 27, productCoeff_07_19 k • columns k := by
  funext r
  change productColumn_07_19 r = ∑ k : Fin 27, productCoeff_07_19 k * columns k r
  fin_cases r <;> norm_num [productColumn_07_19, productCoeff_07_19, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_07_19 :
    jordan (nativeWords 7) (nativeWords 19) =
      ∑ k : Fin 27, productCoeff_07_19 k • nativeWords k := by
  change jordan value7 value19 = _
  rw [native_product_decode_07_19, productColumn_sum_07_19, decode_sum_columns]

def productCoeff_07_20 : Fin 27 → ℝ := ![(8/3), 0, 0, 0, -4, 0, 0, (-4/3), 0, (-4/3), 0, 0, 0, (-2/3), 0, (-1/3), 0, 0, 2, 0, 2, 0, 0, (2/3), 0, 0, 0]
def productColumn_07_20 : Fin 27 → ℝ := ![4, 0, 4, 0, 1, (1/4), 0, (-1/2), 0, 0, 1, 2, 0, 0, (-1/4), 0, 2, (-1/4), 0, 0, 1, -1, 0, (1/2), 0, 0, (-1/4)]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_07_20 :
    jordan value7 value20 = decode productColumn_07_20 := by
  simp only [value7_decode, value20_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_07_20, column7, column20, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_07_20 :
    productColumn_07_20 = ∑ k : Fin 27, productCoeff_07_20 k • columns k := by
  funext r
  change productColumn_07_20 r = ∑ k : Fin 27, productCoeff_07_20 k * columns k r
  fin_cases r <;> norm_num [productColumn_07_20, productCoeff_07_20, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_07_20 :
    jordan (nativeWords 7) (nativeWords 20) =
      ∑ k : Fin 27, productCoeff_07_20 k • nativeWords k := by
  change jordan value7 value20 = _
  rw [native_product_decode_07_20, productColumn_sum_07_20, decode_sum_columns]

def productCoeff_07_21 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0]
def productColumn_07_21 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, (-3/8), 0, 0, (3/8), 0, 0, 0, (-3/8), 0, 0, 0, 0, (3/8), 0, 0, 0, (3/8), 0, 0, (-3/8), 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_07_21 :
    jordan value7 value21 = decode productColumn_07_21 := by
  simp only [value7_decode, value21_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_07_21, column7, column21, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_07_21 :
    productColumn_07_21 = ∑ k : Fin 27, productCoeff_07_21 k • columns k := by
  funext r
  change productColumn_07_21 r = ∑ k : Fin 27, productCoeff_07_21 k * columns k r
  fin_cases r <;> norm_num [productColumn_07_21, productCoeff_07_21, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_07_21 :
    jordan (nativeWords 7) (nativeWords 21) =
      ∑ k : Fin 27, productCoeff_07_21 k • nativeWords k := by
  change jordan value7 value21 = _
  rw [native_product_decode_07_21, productColumn_sum_07_21, decode_sum_columns]

def productCoeff_07_22 : Fin 27 → ℝ := ![0, 0, 0, (-1/4), 0, 0, 0, 0, 0, 0, 0, (3/2), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, (-1/2)]
def productColumn_07_22 : Fin 27 → ℝ := ![0, 0, 0, (-3/2), 0, 0, (1/8), 0, (5/8), (1/8), 0, 0, 0, (1/2), 0, (1/4), 0, 0, (1/2), (3/2), 0, 0, (-1/8), 0, (-5/8), (-1/8), 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_07_22 :
    jordan value7 value22 = decode productColumn_07_22 := by
  simp only [value7_decode, value22_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_07_22, column7, column22, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_07_22 :
    productColumn_07_22 = ∑ k : Fin 27, productCoeff_07_22 k • columns k := by
  funext r
  change productColumn_07_22 r = ∑ k : Fin 27, productCoeff_07_22 k * columns k r
  fin_cases r <;> norm_num [productColumn_07_22, productCoeff_07_22, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_07_22 :
    jordan (nativeWords 7) (nativeWords 22) =
      ∑ k : Fin 27, productCoeff_07_22 k • nativeWords k := by
  change jordan value7 value22 = _
  rw [native_product_decode_07_22, productColumn_sum_07_22, decode_sum_columns]

end
end Glennie.Compact.NativeWordTableR01
