/- Native word row 8 product certificate, part 1. -/
module
public import Glennie.Compact.NativeWordProductCommonR01

@[expose] public section
namespace Glennie.Compact.NativeWordTableR01
noncomputable section
open Glennie AlbertGeometry.NativeOperatorTrace
open scoped BigOperators Matrix
set_option autoImplicit false

def productCoeff_08_16 : Fin 27 → ℝ := ![0, 0, (3/8), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def productColumn_08_16 : Fin 27 → ℝ := ![0, 0, 0, (3/8), 0, 0, 0, 0, 0, 0, 0, 0, (3/8), 0, 0, 0, 0, 0, 0, (3/8), 0, 0, 0, 0, 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_08_16 :
    jordan value8 value16 = decode productColumn_08_16 := by
  simp only [value8_decode, value16_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_08_16, column8, column16, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_08_16 :
    productColumn_08_16 = ∑ k : Fin 27, productCoeff_08_16 k • columns k := by
  funext r
  change productColumn_08_16 r = ∑ k : Fin 27, productCoeff_08_16 k * columns k r
  fin_cases r <;> norm_num [productColumn_08_16, productCoeff_08_16, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_08_16 :
    jordan (nativeWords 8) (nativeWords 16) =
      ∑ k : Fin 27, productCoeff_08_16 k • nativeWords k := by
  change jordan value8 value16 = _
  rw [native_product_decode_08_16, productColumn_sum_08_16, decode_sum_columns]

def productCoeff_08_17 : Fin 27 → ℝ := ![0, 0, 0, (-3/4), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def productColumn_08_17 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, (-3/4), 0, (3/4), (3/4), 0, 0, 0, (-3/4), 0, (-3/4), 0, 0, (-3/4), 0, 0, 0, (-3/4), 0, (-3/4), (3/4), 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_08_17 :
    jordan value8 value17 = decode productColumn_08_17 := by
  simp only [value8_decode, value17_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_08_17, column8, column17, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_08_17 :
    productColumn_08_17 = ∑ k : Fin 27, productCoeff_08_17 k • columns k := by
  funext r
  change productColumn_08_17 r = ∑ k : Fin 27, productCoeff_08_17 k * columns k r
  fin_cases r <;> norm_num [productColumn_08_17, productCoeff_08_17, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_08_17 :
    jordan (nativeWords 8) (nativeWords 17) =
      ∑ k : Fin 27, productCoeff_08_17 k • nativeWords k := by
  change jordan value8 value17 = _
  rw [native_product_decode_08_17, productColumn_sum_08_17, decode_sum_columns]

def productCoeff_08_18 : Fin 27 → ℝ := ![0, (1/2), 0, 0, 0, 0, 0, 0, (-3/4), 0, 0, 0, 0, 0, (-1/4), 0, 0, 0, 0, (5/2), 0, 0, 0, 0, -1, 0, 0]
def productColumn_08_18 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, (-3/8), 0, (-1/4), 0, 0, (1/8), 0, 0, 0, (-7/8), 0, 0, (7/8), 0, 0, 0, (1/8), 0, (-1/4), 0, 0, (-3/8)]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_08_18 :
    jordan value8 value18 = decode productColumn_08_18 := by
  simp only [value8_decode, value18_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_08_18, column8, column18, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_08_18 :
    productColumn_08_18 = ∑ k : Fin 27, productCoeff_08_18 k • columns k := by
  funext r
  change productColumn_08_18 r = ∑ k : Fin 27, productCoeff_08_18 k * columns k r
  fin_cases r <;> norm_num [productColumn_08_18, productCoeff_08_18, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_08_18 :
    jordan (nativeWords 8) (nativeWords 18) =
      ∑ k : Fin 27, productCoeff_08_18 k • nativeWords k := by
  change jordan value8 value18 = _
  rw [native_product_decode_08_18, productColumn_sum_08_18, decode_sum_columns]

def productCoeff_08_19 : Fin 27 → ℝ := ![(1/6), 0, 0, 0, (-1/4), 0, 0, (5/12), 0, (5/12), 0, 0, 0, (1/12), 0, (1/6), 0, 0, (1/8), 0, (1/8), 0, 0, (-1/3), 0, 0, 0]
def productColumn_08_19 : Fin 27 → ℝ := ![(3/4), (1/2), (3/4), 0, (-3/16), (-3/16), 0, (3/16), 0, 0, (-3/16), (-1/8), 0, 0, (1/8), 0, (-1/8), (1/8), 0, 0, (-3/16), (3/16), 0, (-3/16), 0, 0, (3/16)]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_08_19 :
    jordan value8 value19 = decode productColumn_08_19 := by
  simp only [value8_decode, value19_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_08_19, column8, column19, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_08_19 :
    productColumn_08_19 = ∑ k : Fin 27, productCoeff_08_19 k • columns k := by
  funext r
  change productColumn_08_19 r = ∑ k : Fin 27, productCoeff_08_19 k * columns k r
  fin_cases r <;> norm_num [productColumn_08_19, productCoeff_08_19, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_08_19 :
    jordan (nativeWords 8) (nativeWords 19) =
      ∑ k : Fin 27, productCoeff_08_19 k • nativeWords k := by
  change jordan value8 value19 = _
  rw [native_product_decode_08_19, productColumn_sum_08_19, decode_sum_columns]

def productCoeff_08_20 : Fin 27 → ℝ := ![0, (-1/2), 0, 0, 0, 0, 0, 0, (-1/4), 0, 0, 0, (1/4), 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0]
def productColumn_08_20 : Fin 27 → ℝ := ![0, 0, 0, 0, (-1/8), (-1/4), 0, (-3/8), 0, 0, 0, 0, 0, 0, (-7/8), 0, 0, (7/8), 0, 0, (1/8), 0, 0, (-3/8), 0, 0, (-1/4)]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_08_20 :
    jordan value8 value20 = decode productColumn_08_20 := by
  simp only [value8_decode, value20_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_08_20, column8, column20, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_08_20 :
    productColumn_08_20 = ∑ k : Fin 27, productCoeff_08_20 k • columns k := by
  funext r
  change productColumn_08_20 r = ∑ k : Fin 27, productCoeff_08_20 k * columns k r
  fin_cases r <;> norm_num [productColumn_08_20, productCoeff_08_20, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_08_20 :
    jordan (nativeWords 8) (nativeWords 20) =
      ∑ k : Fin 27, productCoeff_08_20 k • nativeWords k := by
  change jordan value8 value20 = _
  rw [native_product_decode_08_20, productColumn_sum_08_20, decode_sum_columns]

def productCoeff_08_21 : Fin 27 → ℝ := ![0, 0, 0, (1/16), 0, (-9/16), 0, 0, 0, 0, 0, (-3/8), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (1/4), 0, 0, 0, (1/8)]
def productColumn_08_21 : Fin 27 → ℝ := ![0, 0, 0, (-3/32), 0, 0, (-1/32), 0, (1/32), (-1/32), 0, 0, 0, (1/16), 0, (-1/16), 0, 0, (1/16), (3/32), 0, 0, (1/32), 0, (-1/32), (1/32), 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_08_21 :
    jordan value8 value21 = decode productColumn_08_21 := by
  simp only [value8_decode, value21_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_08_21, column8, column21, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_08_21 :
    productColumn_08_21 = ∑ k : Fin 27, productCoeff_08_21 k • columns k := by
  funext r
  change productColumn_08_21 r = ∑ k : Fin 27, productCoeff_08_21 k * columns k r
  fin_cases r <;> norm_num [productColumn_08_21, productCoeff_08_21, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_08_21 :
    jordan (nativeWords 8) (nativeWords 21) =
      ∑ k : Fin 27, productCoeff_08_21 k • nativeWords k := by
  change jordan value8 value21 = _
  rw [native_product_decode_08_21, productColumn_sum_08_21, decode_sum_columns]

def productCoeff_08_22 : Fin 27 → ℝ := ![0, 0, (1/8), 0, 0, 0, (-3/8), 0, 0, 0, (-3/4), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (5/2), 0, 0, 0, (1/2), 0]
def productColumn_08_22 : Fin 27 → ℝ := ![0, 0, 0, (-1/16), 0, 0, (-1/4), 0, (-1/16), (3/8), 0, 0, (1/8), (-5/16), 0, 0, 0, 0, (5/16), (-1/16), 0, 0, (3/8), 0, (-1/16), (-1/4), 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_08_22 :
    jordan value8 value22 = decode productColumn_08_22 := by
  simp only [value8_decode, value22_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_08_22, column8, column22, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_08_22 :
    productColumn_08_22 = ∑ k : Fin 27, productCoeff_08_22 k • columns k := by
  funext r
  change productColumn_08_22 r = ∑ k : Fin 27, productCoeff_08_22 k * columns k r
  fin_cases r <;> norm_num [productColumn_08_22, productCoeff_08_22, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_08_22 :
    jordan (nativeWords 8) (nativeWords 22) =
      ∑ k : Fin 27, productCoeff_08_22 k • nativeWords k := by
  change jordan value8 value22 = _
  rw [native_product_decode_08_22, productColumn_sum_08_22, decode_sum_columns]

def productCoeff_08_23 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, 0, 0, (3/2), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def productColumn_08_23 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, (-3/4), 0, (-3/4), 0, 0, 0, 0, 0, 0, (-3/4), 0, 0, (3/4), 0, 0, 0, 0, 0, (-3/4), 0, 0, (-3/4)]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_08_23 :
    jordan value8 value23 = decode productColumn_08_23 := by
  simp only [value8_decode, value23_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_08_23, column8, column23, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_08_23 :
    productColumn_08_23 = ∑ k : Fin 27, productCoeff_08_23 k • columns k := by
  funext r
  change productColumn_08_23 r = ∑ k : Fin 27, productCoeff_08_23 k * columns k r
  fin_cases r <;> norm_num [productColumn_08_23, productCoeff_08_23, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_08_23 :
    jordan (nativeWords 8) (nativeWords 23) =
      ∑ k : Fin 27, productCoeff_08_23 k • nativeWords k := by
  change jordan value8 value23 = _
  rw [native_product_decode_08_23, productColumn_sum_08_23, decode_sum_columns]

end
end Glennie.Compact.NativeWordTableR01
