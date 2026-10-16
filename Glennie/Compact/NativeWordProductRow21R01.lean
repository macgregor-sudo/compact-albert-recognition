/- Concrete native Jordan product certificate for word row 21. -/
module
public import Glennie.Compact.NativeWordProductCommonR01

@[expose] public section
namespace Glennie.Compact.NativeWordTableR01
noncomputable section
open Glennie AlbertGeometry.NativeOperatorTrace
open scoped BigOperators Matrix
set_option autoImplicit false

def productCoeff_21_21 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, 0, (1/32), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def productColumn_21_21 : Fin 27 → ℝ := ![(1/16), (1/16), (1/16), 0, (1/32), 0, 0, 0, 0, 0, 0, (1/32), 0, 0, 0, 0, 0, 0, 0, 0, (1/32), 0, 0, 0, 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_21_21 :
    jordan value21 value21 = decode productColumn_21_21 := by
  simp only [value21_decode, value21_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_21_21, column21, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_21_21 :
    productColumn_21_21 = ∑ k : Fin 27, productCoeff_21_21 k • columns k := by
  funext r
  change productColumn_21_21 r = ∑ k : Fin 27, productCoeff_21_21 k * columns k r
  fin_cases r <;> norm_num [productColumn_21_21, productCoeff_21_21, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_21_21 :
    jordan (nativeWords 21) (nativeWords 21) =
      ∑ k : Fin 27, productCoeff_21_21 k • nativeWords k := by
  change jordan value21 value21 = _
  rw [native_product_decode_21_21, productColumn_sum_21_21, decode_sum_columns]

def productCoeff_21_22 : Fin 27 → ℝ := ![0, (3/16), 0, 0, 0, 0, 0, 0, (-1/8), 0, 0, 0, 0, 0, (-3/32), 0, 0, 0, 0, (3/8), 0, 0, 0, 0, (-3/8), 0, 0]
def productColumn_21_22 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, (-5/64), 0, (-1/32), 0, 0, (3/64), 0, 0, 0, (-1/8), 0, 0, (1/8), 0, 0, 0, (3/64), 0, (-1/32), 0, 0, (-5/64)]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_21_22 :
    jordan value21 value22 = decode productColumn_21_22 := by
  simp only [value21_decode, value22_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_21_22, column21, column22, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_21_22 :
    productColumn_21_22 = ∑ k : Fin 27, productCoeff_21_22 k • columns k := by
  funext r
  change productColumn_21_22 r = ∑ k : Fin 27, productCoeff_21_22 k * columns k r
  fin_cases r <;> norm_num [productColumn_21_22, productCoeff_21_22, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_21_22 :
    jordan (nativeWords 21) (nativeWords 22) =
      ∑ k : Fin 27, productCoeff_21_22 k • nativeWords k := by
  change jordan value21 value22 = _
  rw [native_product_decode_21_22, productColumn_sum_21_22, decode_sum_columns]

def productCoeff_21_23 : Fin 27 → ℝ := ![0, 0, (-3/16), 0, 0, 0, (9/16), 0, 0, 0, (9/8), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, (-3/4), 0]
def productColumn_21_23 : Fin 27 → ℝ := ![0, 0, 0, (3/32), 0, 0, (-27/32), 0, (3/32), (21/32), 0, 0, (-3/16), (-3/4), 0, 0, 0, 0, (3/4), (3/32), 0, 0, (21/32), 0, (3/32), (-27/32), 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_21_23 :
    jordan value21 value23 = decode productColumn_21_23 := by
  simp only [value21_decode, value23_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_21_23, column21, column23, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_21_23 :
    productColumn_21_23 = ∑ k : Fin 27, productCoeff_21_23 k • columns k := by
  funext r
  change productColumn_21_23 r = ∑ k : Fin 27, productCoeff_21_23 k * columns k r
  fin_cases r <;> norm_num [productColumn_21_23, productCoeff_21_23, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_21_23 :
    jordan (nativeWords 21) (nativeWords 23) =
      ∑ k : Fin 27, productCoeff_21_23 k • nativeWords k := by
  change jordan value21 value23 = _
  rw [native_product_decode_21_23, productColumn_sum_21_23, decode_sum_columns]

def productCoeff_21_24 : Fin 27 → ℝ := ![0, 0, 0, (-1/96), 0, (-1/64), 0, 0, 0, 0, 0, (1/16), 0, 0, 0, 0, (-1/96), 0, 0, 0, 0, 0, (-1/96), 0, 0, 0, (1/96)]
def productColumn_21_24 : Fin 27 → ℝ := ![0, 0, 0, (1/128), 0, 0, 0, 0, (-1/128), 0, 0, 0, 0, 0, 0, (1/64), 0, 0, 0, (-1/128), 0, 0, 0, 0, (1/128), 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_21_24 :
    jordan value21 value24 = decode productColumn_21_24 := by
  simp only [value21_decode, value24_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_21_24, column21, column24, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_21_24 :
    productColumn_21_24 = ∑ k : Fin 27, productCoeff_21_24 k • columns k := by
  funext r
  change productColumn_21_24 r = ∑ k : Fin 27, productCoeff_21_24 k * columns k r
  fin_cases r <;> norm_num [productColumn_21_24, productCoeff_21_24, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_21_24 :
    jordan (nativeWords 21) (nativeWords 24) =
      ∑ k : Fin 27, productCoeff_21_24 k • nativeWords k := by
  change jordan value21 value24 = _
  rw [native_product_decode_21_24, productColumn_sum_21_24, decode_sum_columns]

def productCoeff_21_25 : Fin 27 → ℝ := ![(-1/32), 0, 0, 0, (3/64), 0, 0, 0, 0, (-1/32), 0, 0, 0, (1/32), 0, (1/16), 0, 0, (-3/64), 0, (3/64), 0, 0, 0, 0, 0, 0]
def productColumn_21_25 : Fin 27 → ℝ := ![(-3/64), (-3/32), (-3/64), 0, (-3/128), (-1/128), 0, (1/128), 0, 0, (-1/128), (-3/64), 0, 0, (-1/64), 0, (1/64), (-1/64), 0, 0, (-3/128), (1/128), 0, (-1/128), 0, 0, (1/128)]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_21_25 :
    jordan value21 value25 = decode productColumn_21_25 := by
  simp only [value21_decode, value25_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_21_25, column21, column25, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_21_25 :
    productColumn_21_25 = ∑ k : Fin 27, productCoeff_21_25 k • columns k := by
  funext r
  change productColumn_21_25 r = ∑ k : Fin 27, productCoeff_21_25 k * columns k r
  fin_cases r <;> norm_num [productColumn_21_25, productCoeff_21_25, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_21_25 :
    jordan (nativeWords 21) (nativeWords 25) =
      ∑ k : Fin 27, productCoeff_21_25 k • nativeWords k := by
  change jordan value21 value25 = _
  rw [native_product_decode_21_25, productColumn_sum_21_25, decode_sum_columns]

def productCoeff_21_26 : Fin 27 → ℝ := ![0, (7/32), 0, 0, 0, 0, 0, 0, (-3/16), 0, 0, 0, (1/32), 0, (-5/32), 0, 0, 0, 0, (7/16), 0, 0, 0, 0, (-1/4), 0, 0]
def productColumn_21_26 : Fin 27 → ℝ := ![(1/32), 0, (-1/32), 0, (-1/64), (-3/64), 0, (-1/64), 0, 0, (5/64), 0, 0, 0, (-1/8), 0, 0, (1/8), 0, 0, (1/64), (5/64), 0, (-1/64), 0, 0, (-3/64)]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_21_26 :
    jordan value21 value26 = decode productColumn_21_26 := by
  simp only [value21_decode, value26_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_21_26, column21, column26, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_21_26 :
    productColumn_21_26 = ∑ k : Fin 27, productCoeff_21_26 k • columns k := by
  funext r
  change productColumn_21_26 r = ∑ k : Fin 27, productCoeff_21_26 k * columns k r
  fin_cases r <;> norm_num [productColumn_21_26, productCoeff_21_26, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_21_26 :
    jordan (nativeWords 21) (nativeWords 26) =
      ∑ k : Fin 27, productCoeff_21_26 k • nativeWords k := by
  change jordan value21 value26 = _
  rw [native_product_decode_21_26, productColumn_sum_21_26, decode_sum_columns]

end
end Glennie.Compact.NativeWordTableR01
