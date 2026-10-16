/- Native word row 9 product certificate, part 2. -/
module
public import Glennie.Compact.NativeWordProductCommonR01

@[expose] public section
namespace Glennie.Compact.NativeWordTableR01
noncomputable section
open Glennie AlbertGeometry.NativeOperatorTrace
open scoped BigOperators Matrix
set_option autoImplicit false

def productCoeff_09_19 : Fin 27 → ℝ := ![0, (1/2), 0, 0, 0, 0, 0, 0, (-3/4), 0, 0, 0, (-1/4), 0, 0, 0, 0, 0, 0, (5/2), 0, 0, 0, 0, -1, 0, 0]
def productColumn_09_19 : Fin 27 → ℝ := ![0, 0, 0, 0, (1/8), (-3/8), 0, (-1/4), 0, 0, 0, 0, 0, 0, (-7/8), 0, 0, (7/8), 0, 0, (-1/8), 0, 0, (-1/4), 0, 0, (-3/8)]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_09_19 :
    jordan value9 value19 = decode productColumn_09_19 := by
  simp only [value9_decode, value19_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_09_19, column9, column19, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_09_19 :
    productColumn_09_19 = ∑ k : Fin 27, productCoeff_09_19 k • columns k := by
  funext r
  change productColumn_09_19 r = ∑ k : Fin 27, productCoeff_09_19 k * columns k r
  fin_cases r <;> norm_num [productColumn_09_19, productCoeff_09_19, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_09_19 :
    jordan (nativeWords 9) (nativeWords 19) =
      ∑ k : Fin 27, productCoeff_09_19 k • nativeWords k := by
  change jordan value9 value19 = _
  rw [native_product_decode_09_19, productColumn_sum_09_19, decode_sum_columns]

def productCoeff_09_20 : Fin 27 → ℝ := ![3, 0, 0, 0, (-9/2), 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (9/2), 0, 0, 0, 0, 0, 0]
def productColumn_09_20 : Fin 27 → ℝ := ![(11/2), 1, (11/2), 0, 0, 0, 0, 0, 0, 0, (5/4), 0, 0, 0, 0, 0, (7/2), 0, 0, 0, 0, (-5/4), 0, 0, 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_09_20 :
    jordan value9 value20 = decode productColumn_09_20 := by
  simp only [value9_decode, value20_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_09_20, column9, column20, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_09_20 :
    productColumn_09_20 = ∑ k : Fin 27, productCoeff_09_20 k • columns k := by
  funext r
  change productColumn_09_20 r = ∑ k : Fin 27, productCoeff_09_20 k * columns k r
  fin_cases r <;> norm_num [productColumn_09_20, productCoeff_09_20, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_09_20 :
    jordan (nativeWords 9) (nativeWords 20) =
      ∑ k : Fin 27, productCoeff_09_20 k • nativeWords k := by
  change jordan value9 value20 = _
  rw [native_product_decode_09_20, productColumn_sum_09_20, decode_sum_columns]

def productCoeff_09_21 : Fin 27 → ℝ := ![0, 0, (-1/8), 0, 0, 0, (3/8), 0, 0, 0, (3/4), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, (-1/2), 0]
def productColumn_09_21 : Fin 27 → ℝ := ![0, 0, 0, (1/16), 0, 0, (-5/16), 0, (1/16), (3/16), 0, 0, (-1/8), (-1/4), 0, 0, 0, 0, (1/4), (1/16), 0, 0, (3/16), 0, (1/16), (-5/16), 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_09_21 :
    jordan value9 value21 = decode productColumn_09_21 := by
  simp only [value9_decode, value21_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_09_21, column9, column21, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_09_21 :
    productColumn_09_21 = ∑ k : Fin 27, productCoeff_09_21 k • columns k := by
  funext r
  change productColumn_09_21 r = ∑ k : Fin 27, productCoeff_09_21 k * columns k r
  fin_cases r <;> norm_num [productColumn_09_21, productCoeff_09_21, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_09_21 :
    jordan (nativeWords 9) (nativeWords 21) =
      ∑ k : Fin 27, productCoeff_09_21 k • nativeWords k := by
  change jordan value9 value21 = _
  rw [native_product_decode_09_21, productColumn_sum_09_21, decode_sum_columns]

def productCoeff_09_22 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, (-9/2), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (9/2), 0, 0, 0, 0]
def productColumn_09_22 : Fin 27 → ℝ := ![0, 0, 0, (-9/4), 0, 0, 0, 0, (9/8), 0, 0, 0, 0, (9/8), 0, 0, 0, 0, (9/8), (9/4), 0, 0, 0, 0, (-9/8), 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_09_22 :
    jordan value9 value22 = decode productColumn_09_22 := by
  simp only [value9_decode, value22_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_09_22, column9, column22, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_09_22 :
    productColumn_09_22 = ∑ k : Fin 27, productCoeff_09_22 k • columns k := by
  funext r
  change productColumn_09_22 r = ∑ k : Fin 27, productCoeff_09_22 k * columns k r
  fin_cases r <;> norm_num [productColumn_09_22, productCoeff_09_22, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_09_22 :
    jordan (nativeWords 9) (nativeWords 22) =
      ∑ k : Fin 27, productCoeff_09_22 k • nativeWords k := by
  change jordan value9 value22 = _
  rw [native_product_decode_09_22, productColumn_sum_09_22, decode_sum_columns]

def productCoeff_09_23 : Fin 27 → ℝ := ![9, 0, 0, 0, 0, 0, 0, (-9/2), 0, -3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (9/2), 0, 0, 0]
def productColumn_09_23 : Fin 27 → ℝ := ![12, 12, 12, 0, (9/2), (9/4), 0, (-9/4), 0, 0, 6, (9/2), 0, 0, (-9/4), 0, 6, (-9/4), 0, 0, (9/2), -6, 0, (9/4), 0, 0, (-9/4)]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_09_23 :
    jordan value9 value23 = decode productColumn_09_23 := by
  simp only [value9_decode, value23_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_09_23, column9, column23, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_09_23 :
    productColumn_09_23 = ∑ k : Fin 27, productCoeff_09_23 k • columns k := by
  funext r
  change productColumn_09_23 r = ∑ k : Fin 27, productCoeff_09_23 k * columns k r
  fin_cases r <;> norm_num [productColumn_09_23, productCoeff_09_23, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_09_23 :
    jordan (nativeWords 9) (nativeWords 23) =
      ∑ k : Fin 27, productCoeff_09_23 k • nativeWords k := by
  change jordan value9 value23 = _
  rw [native_product_decode_09_23, productColumn_sum_09_23, decode_sum_columns]

end
end Glennie.Compact.NativeWordTableR01
