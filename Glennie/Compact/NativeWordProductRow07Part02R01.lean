/- Native word row 7 product certificate, part 2. -/
module
public import Glennie.Compact.NativeWordProductCommonR01

@[expose] public section
namespace Glennie.Compact.NativeWordTableR01
noncomputable section
open Glennie AlbertGeometry.NativeOperatorTrace
open scoped BigOperators Matrix
set_option autoImplicit false

def productCoeff_07_23 : Fin 27 → ℝ := ![9, 0, 0, 0, 0, 0, 0, -3, 0, (-9/2), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (9/2), 0, 0, 0]
def productColumn_07_23 : Fin 27 → ℝ := ![12, 12, 12, 0, 6, (9/4), 0, (-9/4), 0, 0, (9/2), 6, 0, 0, (-9/4), 0, (9/2), (-9/4), 0, 0, 6, (-9/2), 0, (9/4), 0, 0, (-9/4)]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_07_23 :
    jordan value7 value23 = decode productColumn_07_23 := by
  simp only [value7_decode, value23_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_07_23, column7, column23, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_07_23 :
    productColumn_07_23 = ∑ k : Fin 27, productCoeff_07_23 k • columns k := by
  funext r
  change productColumn_07_23 r = ∑ k : Fin 27, productCoeff_07_23 k * columns k r
  fin_cases r <;> norm_num [productColumn_07_23, productCoeff_07_23, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_07_23 :
    jordan (nativeWords 7) (nativeWords 23) =
      ∑ k : Fin 27, productCoeff_07_23 k • nativeWords k := by
  change jordan value7 value23 = _
  rw [native_product_decode_07_23, productColumn_sum_07_23, decode_sum_columns]

def productCoeff_07_24 : Fin 27 → ℝ := ![0, (-1/4), 0, 0, 0, 0, 0, 0, (-1/8), 0, 0, 0, 0, 0, (1/8), 0, 0, 0, 0, (1/4), 0, 0, 0, 0, 2, 0, 0]
def productColumn_07_24 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, (1/4), 0, 0, 0, 0, (-1/16), 0, 0, 0, (-1/16), 0, 0, (1/16), 0, 0, 0, (-1/16), 0, 0, 0, 0, (1/4)]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_07_24 :
    jordan value7 value24 = decode productColumn_07_24 := by
  simp only [value7_decode, value24_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_07_24, column7, column24, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_07_24 :
    productColumn_07_24 = ∑ k : Fin 27, productCoeff_07_24 k • columns k := by
  funext r
  change productColumn_07_24 r = ∑ k : Fin 27, productCoeff_07_24 k * columns k r
  fin_cases r <;> norm_num [productColumn_07_24, productCoeff_07_24, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_07_24 :
    jordan (nativeWords 7) (nativeWords 24) =
      ∑ k : Fin 27, productCoeff_07_24 k • nativeWords k := by
  change jordan value7 value24 = _
  rw [native_product_decode_07_24, productColumn_sum_07_24, decode_sum_columns]

def productCoeff_07_25 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-3/2), 0, 0, 0, (3/2), 0]
def productColumn_07_25 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, (3/8), 0, (-3/16), (-9/16), 0, 0, 0, (3/16), 0, 0, 0, 0, (-3/16), 0, 0, 0, (-9/16), 0, (-3/16), (3/8), 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_07_25 :
    jordan value7 value25 = decode productColumn_07_25 := by
  simp only [value7_decode, value25_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_07_25, column7, column25, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_07_25 :
    productColumn_07_25 = ∑ k : Fin 27, productCoeff_07_25 k • columns k := by
  funext r
  change productColumn_07_25 r = ∑ k : Fin 27, productCoeff_07_25 k * columns k r
  fin_cases r <;> norm_num [productColumn_07_25, productCoeff_07_25, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_07_25 :
    jordan (nativeWords 7) (nativeWords 25) =
      ∑ k : Fin 27, productCoeff_07_25 k • nativeWords k := by
  change jordan value7 value25 = _
  rw [native_product_decode_07_25, productColumn_sum_07_25, decode_sum_columns]

def productCoeff_07_26 : Fin 27 → ℝ := ![0, 0, 0, (1/4), 0, 0, 0, 0, 0, 0, 0, (-3/2), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1/2), 0, 0, 0, 2]
def productColumn_07_26 : Fin 27 → ℝ := ![0, 0, 0, (-3/2), 0, 0, (-1/2), 0, (-5/8), (-1/8), 0, 0, 0, (-1/8), 0, (-1/4), 0, 0, (-1/8), (3/2), 0, 0, (1/8), 0, (5/8), (1/2), 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_07_26 :
    jordan value7 value26 = decode productColumn_07_26 := by
  simp only [value7_decode, value26_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_07_26, column7, column26, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_07_26 :
    productColumn_07_26 = ∑ k : Fin 27, productCoeff_07_26 k • columns k := by
  funext r
  change productColumn_07_26 r = ∑ k : Fin 27, productCoeff_07_26 k * columns k r
  fin_cases r <;> norm_num [productColumn_07_26, productCoeff_07_26, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_07_26 :
    jordan (nativeWords 7) (nativeWords 26) =
      ∑ k : Fin 27, productCoeff_07_26 k • nativeWords k := by
  change jordan value7 value26 = _
  rw [native_product_decode_07_26, productColumn_sum_07_26, decode_sum_columns]

end
end Glennie.Compact.NativeWordTableR01
