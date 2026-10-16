/- Native word row 8 product certificate, part 0. -/
module
public import Glennie.Compact.NativeWordProductCommonR01

@[expose] public section
namespace Glennie.Compact.NativeWordTableR01
noncomputable section
open Glennie AlbertGeometry.NativeOperatorTrace
open scoped BigOperators Matrix
set_option autoImplicit false

def productCoeff_08_08 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, 0, (3/4), 0, (3/4), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1/2), 0, 0, 0]
def productColumn_08_08 : Fin 27 → ℝ := ![1, 1, 1, 0, (-1/4), (-1/4), 0, (1/4), 0, 0, (-1/4), (-1/4), 0, 0, (1/4), 0, (-1/4), (1/4), 0, 0, (-1/4), (1/4), 0, (-1/4), 0, 0, (1/4)]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_08_08 :
    jordan value8 value8 = decode productColumn_08_08 := by
  simp only [value8_decode, value8_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_08_08, column8, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_08_08 :
    productColumn_08_08 = ∑ k : Fin 27, productCoeff_08_08 k • columns k := by
  funext r
  change productColumn_08_08 r = ∑ k : Fin 27, productCoeff_08_08 k * columns k r
  fin_cases r <;> norm_num [productColumn_08_08, productCoeff_08_08, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_08_08 :
    jordan (nativeWords 8) (nativeWords 8) =
      ∑ k : Fin 27, productCoeff_08_08 k • nativeWords k := by
  change jordan value8 value8 = _
  rw [native_product_decode_08_08, productColumn_sum_08_08, decode_sum_columns]

def productCoeff_08_09 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, 0, 0, (3/2), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def productColumn_08_09 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, (-3/4), 0, (-3/4), 0, 0, 0, 0, 0, 0, (-3/4), 0, 0, (3/4), 0, 0, 0, 0, 0, (-3/4), 0, 0, (-3/4)]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_08_09 :
    jordan value8 value9 = decode productColumn_08_09 := by
  simp only [value8_decode, value9_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_08_09, column8, column9, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_08_09 :
    productColumn_08_09 = ∑ k : Fin 27, productCoeff_08_09 k • columns k := by
  funext r
  change productColumn_08_09 r = ∑ k : Fin 27, productCoeff_08_09 k * columns k r
  fin_cases r <;> norm_num [productColumn_08_09, productCoeff_08_09, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_08_09 :
    jordan (nativeWords 8) (nativeWords 9) =
      ∑ k : Fin 27, productCoeff_08_09 k • nativeWords k := by
  change jordan value8 value9 = _
  rw [native_product_decode_08_09, productColumn_sum_08_09, decode_sum_columns]

def productCoeff_08_10 : Fin 27 → ℝ := ![0, 0, 0, (1/24), 0, 0, 0, 0, 0, 0, 0, (-1/4), 0, 0, 0, 0, (1/6), 0, 0, 0, 0, 0, (-1/12), 0, 0, 0, (1/12)]
def productColumn_08_10 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, (-1/16), 0, 0, (1/16), 0, 0, 0, (-1/16), 0, (-1/8), 0, 0, (-1/16), 0, 0, 0, (-1/16), 0, 0, (1/16), 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_08_10 :
    jordan value8 value10 = decode productColumn_08_10 := by
  simp only [value8_decode, value10_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_08_10, column8, column10, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_08_10 :
    productColumn_08_10 = ∑ k : Fin 27, productCoeff_08_10 k • columns k := by
  funext r
  change productColumn_08_10 r = ∑ k : Fin 27, productCoeff_08_10 k * columns k r
  fin_cases r <;> norm_num [productColumn_08_10, productCoeff_08_10, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_08_10 :
    jordan (nativeWords 8) (nativeWords 10) =
      ∑ k : Fin 27, productCoeff_08_10 k • nativeWords k := by
  change jordan value8 value10 = _
  rw [native_product_decode_08_10, productColumn_sum_08_10, decode_sum_columns]

def productCoeff_08_11 : Fin 27 → ℝ := ![0, 0, (7/24), 0, 0, 0, (-1/8), 0, 0, 0, (-1/4), 0, 0, 0, 0, 0, 0, (-1/12), 0, 0, 0, (-1/6), 0, 0, 0, (1/6), 0]
def productColumn_08_11 : Fin 27 → ℝ := ![0, 0, 0, (1/16), 0, 0, 0, 0, (-1/16), 0, 0, 0, (1/8), (1/16), 0, 0, 0, 0, (-1/16), (1/16), 0, 0, 0, 0, (-1/16), 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_08_11 :
    jordan value8 value11 = decode productColumn_08_11 := by
  simp only [value8_decode, value11_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_08_11, column8, column11, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_08_11 :
    productColumn_08_11 = ∑ k : Fin 27, productCoeff_08_11 k • columns k := by
  funext r
  change productColumn_08_11 r = ∑ k : Fin 27, productCoeff_08_11 k * columns k r
  fin_cases r <;> norm_num [productColumn_08_11, productCoeff_08_11, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_08_11 :
    jordan (nativeWords 8) (nativeWords 11) =
      ∑ k : Fin 27, productCoeff_08_11 k • nativeWords k := by
  change jordan value8 value11 = _
  rw [native_product_decode_08_11, productColumn_sum_08_11, decode_sum_columns]

def productCoeff_08_12 : Fin 27 → ℝ := ![1, 0, 0, 0, (-3/2), 0, 0, 0, 0, (-1/2), 0, 0, 0, 2, 0, (-1/2), 0, 0, 0, 0, (3/4), 0, 0, 0, 0, 0, 0]
def productColumn_08_12 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, (5/8), 0, (1/2), 0, 0, (-1/8), 0, 0, 0, (1/8), 0, (1/4), (1/8), 0, 0, 0, (1/8), 0, (-1/2), 0, 0, (-5/8)]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_08_12 :
    jordan value8 value12 = decode productColumn_08_12 := by
  simp only [value8_decode, value12_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_08_12, column8, column12, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_08_12 :
    productColumn_08_12 = ∑ k : Fin 27, productCoeff_08_12 k • columns k := by
  funext r
  change productColumn_08_12 r = ∑ k : Fin 27, productCoeff_08_12 k * columns k r
  fin_cases r <;> norm_num [productColumn_08_12, productCoeff_08_12, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_08_12 :
    jordan (nativeWords 8) (nativeWords 12) =
      ∑ k : Fin 27, productCoeff_08_12 k • nativeWords k := by
  change jordan value8 value12 = _
  rw [native_product_decode_08_12, productColumn_sum_08_12, decode_sum_columns]

def productCoeff_08_13 : Fin 27 → ℝ := ![0, (-1/4), 0, 0, 0, 0, 0, 0, (-1/4), 0, 0, 0, (1/8), 0, (1/8), 0, 0, 0, 0, (1/4), 0, 0, 0, 0, -1, 0, 0]
def productColumn_08_13 : Fin 27 → ℝ := ![(-1/4), 0, (1/4), 0, (-1/16), (-1/16), 0, (1/16), 0, 0, (-1/16), 0, 0, 0, 0, 0, 0, 0, 0, 0, (1/16), (-1/16), 0, (1/16), 0, 0, (-1/16)]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_08_13 :
    jordan value8 value13 = decode productColumn_08_13 := by
  simp only [value8_decode, value13_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_08_13, column8, column13, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_08_13 :
    productColumn_08_13 = ∑ k : Fin 27, productCoeff_08_13 k • columns k := by
  funext r
  change productColumn_08_13 r = ∑ k : Fin 27, productCoeff_08_13 k * columns k r
  fin_cases r <;> norm_num [productColumn_08_13, productCoeff_08_13, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_08_13 :
    jordan (nativeWords 8) (nativeWords 13) =
      ∑ k : Fin 27, productCoeff_08_13 k • nativeWords k := by
  change jordan value8 value13 = _
  rw [native_product_decode_08_13, productColumn_sum_08_13, decode_sum_columns]

def productCoeff_08_14 : Fin 27 → ℝ := ![-1, 0, 0, 0, (3/2), 0, 0, (1/2), 0, 0, 0, 0, 0, (5/2), 0, (1/2), 0, 0, (-3/4), 0, 0, 0, 0, 0, 0, 0, 0]
def productColumn_08_14 : Fin 27 → ℝ := ![0, 0, 0, 0, (1/8), (1/2), 0, (5/8), 0, 0, 0, (-1/4), 0, 0, (-1/8), 0, 0, (-1/8), 0, 0, (1/8), 0, 0, (-5/8), 0, 0, (-1/2)]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_08_14 :
    jordan value8 value14 = decode productColumn_08_14 := by
  simp only [value8_decode, value14_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_08_14, column8, column14, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_08_14 :
    productColumn_08_14 = ∑ k : Fin 27, productCoeff_08_14 k • columns k := by
  funext r
  change productColumn_08_14 r = ∑ k : Fin 27, productCoeff_08_14 k * columns k r
  fin_cases r <;> norm_num [productColumn_08_14, productCoeff_08_14, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_08_14 :
    jordan (nativeWords 8) (nativeWords 14) =
      ∑ k : Fin 27, productCoeff_08_14 k • nativeWords k := by
  change jordan value8 value14 = _
  rw [native_product_decode_08_14, productColumn_sum_08_14, decode_sum_columns]

def productCoeff_08_15 : Fin 27 → ℝ := ![0, (1/8), 0, 0, 0, 0, 0, 0, (-1/8), 0, 0, 0, (-1/4), 0, (1/8), 0, 0, 0, 0, (1/4), 0, 0, 0, 0, (1/2), 0, 0]
def productColumn_08_15 : Fin 27 → ℝ := ![(1/8), 0, (-1/8), 0, (1/8), (1/16), 0, 0, 0, 0, (-1/16), 0, 0, 0, (-1/16), 0, 0, (1/16), 0, 0, (-1/8), (-1/16), 0, 0, 0, 0, (1/16)]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_08_15 :
    jordan value8 value15 = decode productColumn_08_15 := by
  simp only [value8_decode, value15_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_08_15, column8, column15, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_08_15 :
    productColumn_08_15 = ∑ k : Fin 27, productCoeff_08_15 k • columns k := by
  funext r
  change productColumn_08_15 r = ∑ k : Fin 27, productCoeff_08_15 k * columns k r
  fin_cases r <;> norm_num [productColumn_08_15, productCoeff_08_15, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_08_15 :
    jordan (nativeWords 8) (nativeWords 15) =
      ∑ k : Fin 27, productCoeff_08_15 k • nativeWords k := by
  change jordan value8 value15 = _
  rw [native_product_decode_08_15, productColumn_sum_08_15, decode_sum_columns]

end
end Glennie.Compact.NativeWordTableR01
