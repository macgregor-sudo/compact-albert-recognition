/- Native word row 5 product certificate, part 2. -/
module
public import Glennie.Compact.NativeWordProductCommonR01

@[expose] public section
namespace Glennie.Compact.NativeWordTableR01
noncomputable section
open Glennie AlbertGeometry.NativeOperatorTrace
open scoped BigOperators Matrix
set_option autoImplicit false

def productCoeff_05_21 : Fin 27 → ℝ := ![0, (1/8), 0, 0, 0, 0, 0, 0, (-1/8), 0, 0, 0, 0, 0, (-1/16), 0, 0, 0, 0, (1/4), 0, 0, 0, 0, (-1/4), 0, 0]
def productColumn_05_21 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, (-1/32), 0, 0, 0, 0, (1/32), 0, 0, 0, (-1/16), 0, 0, (1/16), 0, 0, 0, (1/32), 0, 0, 0, 0, (-1/32)]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_05_21 :
    jordan value5 value21 = decode productColumn_05_21 := by
  simp only [value5_decode, value21_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_05_21, column5, column21, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_05_21 :
    productColumn_05_21 = ∑ k : Fin 27, productCoeff_05_21 k • columns k := by
  funext r
  change productColumn_05_21 r = ∑ k : Fin 27, productCoeff_05_21 k * columns k r
  fin_cases r <;> norm_num [productColumn_05_21, productCoeff_05_21, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_05_21 :
    jordan (nativeWords 5) (nativeWords 21) =
      ∑ k : Fin 27, productCoeff_05_21 k • nativeWords k := by
  change jordan value5 value21 = _
  rw [native_product_decode_05_21, productColumn_sum_05_21, decode_sum_columns]

def productCoeff_05_22 : Fin 27 → ℝ := ![(1/6), 0, 0, 0, (5/4), 0, 0, (5/12), 0, (-1/12), 0, 0, 0, (1/12), 0, (-1/12), 0, 0, -1, 0, (1/8), 0, 0, (1/24), 0, 0, 0]
def productColumn_05_22 : Fin 27 → ℝ := ![(1/2), 1, (1/2), 0, 0, (1/16), 0, 0, 0, 0, (1/16), (-1/2), 0, 0, 0, 0, (1/8), 0, 0, 0, 0, (-1/16), 0, 0, 0, 0, (-1/16)]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_05_22 :
    jordan value5 value22 = decode productColumn_05_22 := by
  simp only [value5_decode, value22_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_05_22, column5, column22, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_05_22 :
    productColumn_05_22 = ∑ k : Fin 27, productCoeff_05_22 k • columns k := by
  funext r
  change productColumn_05_22 r = ∑ k : Fin 27, productCoeff_05_22 k * columns k r
  fin_cases r <;> norm_num [productColumn_05_22, productCoeff_05_22, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_05_22 :
    jordan (nativeWords 5) (nativeWords 22) =
      ∑ k : Fin 27, productCoeff_05_22 k • nativeWords k := by
  change jordan value5 value22 = _
  rw [native_product_decode_05_22, productColumn_sum_05_22, decode_sum_columns]

def productCoeff_05_23 : Fin 27 → ℝ := ![0, 0, 0, (1/4), 0, -3, 0, 0, 0, 0, 0, (-3/2), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (5/2), 0, 0, 0, (1/2)]
def productColumn_05_23 : Fin 27 → ℝ := ![0, 0, 0, (-3/2), 0, 0, (-1/8), 0, (1/2), (-1/8), 0, 0, 0, (5/8), 0, (-1/4), 0, 0, (5/8), (3/2), 0, 0, (1/8), 0, (-1/2), (1/8), 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_05_23 :
    jordan value5 value23 = decode productColumn_05_23 := by
  simp only [value5_decode, value23_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_05_23, column5, column23, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_05_23 :
    productColumn_05_23 = ∑ k : Fin 27, productCoeff_05_23 k • columns k := by
  funext r
  change productColumn_05_23 r = ∑ k : Fin 27, productCoeff_05_23 k * columns k r
  fin_cases r <;> norm_num [productColumn_05_23, productCoeff_05_23, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_05_23 :
    jordan (nativeWords 5) (nativeWords 23) =
      ∑ k : Fin 27, productCoeff_05_23 k • nativeWords k := by
  change jordan value5 value23 = _
  rw [native_product_decode_05_23, productColumn_sum_05_23, decode_sum_columns]

def productCoeff_05_24 : Fin 27 → ℝ := ![0, 0, (1/24), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1/48), 0, 0, 0, (-1/6), 0, 0, 0, (-1/12), 0]
def productColumn_05_24 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (1/32), 0, 0, 0, 0, (-1/32), 0, 0, 0, 0, 0, 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_05_24 :
    jordan value5 value24 = decode productColumn_05_24 := by
  simp only [value5_decode, value24_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_05_24, column5, column24, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_05_24 :
    productColumn_05_24 = ∑ k : Fin 27, productCoeff_05_24 k • columns k := by
  funext r
  change productColumn_05_24 r = ∑ k : Fin 27, productCoeff_05_24 k * columns k r
  fin_cases r <;> norm_num [productColumn_05_24, productCoeff_05_24, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_05_24 :
    jordan (nativeWords 5) (nativeWords 24) =
      ∑ k : Fin 27, productCoeff_05_24 k • nativeWords k := by
  change jordan value5 value24 = _
  rw [native_product_decode_05_24, productColumn_sum_05_24, decode_sum_columns]

def productCoeff_05_25 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, 0, 0, (3/16), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-3/8), 0, 0, 0, 0, 0, 0, 0]
def productColumn_05_25 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (3/32), 0, 0, (-3/32), 0, 0, 0, 0, 0, 0, 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_05_25 :
    jordan value5 value25 = decode productColumn_05_25 := by
  simp only [value5_decode, value25_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_05_25, column5, column25, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_05_25 :
    productColumn_05_25 = ∑ k : Fin 27, productCoeff_05_25 k • columns k := by
  funext r
  change productColumn_05_25 r = ∑ k : Fin 27, productCoeff_05_25 k * columns k r
  fin_cases r <;> norm_num [productColumn_05_25, productCoeff_05_25, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_05_25 :
    jordan (nativeWords 5) (nativeWords 25) =
      ∑ k : Fin 27, productCoeff_05_25 k • nativeWords k := by
  change jordan value5 value25 = _
  rw [native_product_decode_05_25, productColumn_sum_05_25, decode_sum_columns]

def productCoeff_05_26 : Fin 27 → ℝ := ![(-1/12), 0, 0, 0, 2, 0, 0, (5/12), 0, (1/24), 0, 0, 0, (1/12), 0, (1/6), 0, 0, -1, 0, (-1/4), 0, 0, (1/24), 0, 0, 0]
def productColumn_05_26 : Fin 27 → ℝ := ![(1/2), 1, (1/2), 0, 0, 0, 0, 0, 0, 0, 0, (-1/2), 0, 0, (-1/16), 0, (-1/8), (-1/16), 0, 0, 0, 0, 0, 0, 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_05_26 :
    jordan value5 value26 = decode productColumn_05_26 := by
  simp only [value5_decode, value26_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_05_26, column5, column26, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_05_26 :
    productColumn_05_26 = ∑ k : Fin 27, productCoeff_05_26 k • columns k := by
  funext r
  change productColumn_05_26 r = ∑ k : Fin 27, productCoeff_05_26 k * columns k r
  fin_cases r <;> norm_num [productColumn_05_26, productCoeff_05_26, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_05_26 :
    jordan (nativeWords 5) (nativeWords 26) =
      ∑ k : Fin 27, productCoeff_05_26 k • nativeWords k := by
  change jordan value5 value26 = _
  rw [native_product_decode_05_26, productColumn_sum_05_26, decode_sum_columns]

end
end Glennie.Compact.NativeWordTableR01
