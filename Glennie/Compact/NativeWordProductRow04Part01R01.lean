/- Native word row 4 product certificate, part 1. -/
module
public import Glennie.Compact.NativeWordProductCommonR01

@[expose] public section
namespace Glennie.Compact.NativeWordTableR01
noncomputable section
open Glennie AlbertGeometry.NativeOperatorTrace
open scoped BigOperators Matrix
set_option autoImplicit false

def productCoeff_04_12 : Fin 27 → ℝ := ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (1/2), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def productColumn_04_12 : Fin 27 → ℝ := ![-2, 0, 2, 0, (-1/4), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (1/4), 0, 0, 0, 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_04_12 :
    jordan value4 value12 = decode productColumn_04_12 := by
  simp only [value4_decode, value12_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_04_12, column4, column12, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_04_12 :
    productColumn_04_12 = ∑ k : Fin 27, productCoeff_04_12 k • columns k := by
  funext r
  change productColumn_04_12 r = ∑ k : Fin 27, productCoeff_04_12 k * columns k r
  fin_cases r <;> norm_num [productColumn_04_12, productCoeff_04_12, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_04_12 :
    jordan (nativeWords 4) (nativeWords 12) =
      ∑ k : Fin 27, productCoeff_04_12 k • nativeWords k := by
  change jordan value4 value12 = _
  rw [native_product_decode_04_12, productColumn_sum_04_12, decode_sum_columns]

def productCoeff_04_13 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (1/2), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def productColumn_04_13 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, (1/8), 0, (1/8), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1/8), 0, 0, (-1/8)]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_04_13 :
    jordan value4 value13 = decode productColumn_04_13 := by
  simp only [value4_decode, value13_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_04_13, column4, column13, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_04_13 :
    productColumn_04_13 = ∑ k : Fin 27, productCoeff_04_13 k • columns k := by
  funext r
  change productColumn_04_13 r = ∑ k : Fin 27, productCoeff_04_13 k * columns k r
  fin_cases r <;> norm_num [productColumn_04_13, productCoeff_04_13, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_04_13 :
    jordan (nativeWords 4) (nativeWords 13) =
      ∑ k : Fin 27, productCoeff_04_13 k • nativeWords k := by
  change jordan value4 value13 = _
  rw [native_product_decode_04_13, productColumn_sum_04_13, decode_sum_columns]

def productCoeff_04_14 : Fin 27 → ℝ := ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (1/2), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def productColumn_04_14 : Fin 27 → ℝ := ![-2, 0, 2, 0, 0, 0, 0, 0, 0, 0, (-1/4), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1/4), 0, 0, 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_04_14 :
    jordan value4 value14 = decode productColumn_04_14 := by
  simp only [value4_decode, value14_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_04_14, column4, column14, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_04_14 :
    productColumn_04_14 = ∑ k : Fin 27, productCoeff_04_14 k • columns k := by
  funext r
  change productColumn_04_14 r = ∑ k : Fin 27, productCoeff_04_14 k * columns k r
  fin_cases r <;> norm_num [productColumn_04_14, productCoeff_04_14, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_04_14 :
    jordan (nativeWords 4) (nativeWords 14) =
      ∑ k : Fin 27, productCoeff_04_14 k • nativeWords k := by
  change jordan value4 value14 = _
  rw [native_product_decode_04_14, productColumn_sum_04_14, decode_sum_columns]

def productCoeff_04_15 : Fin 27 → ℝ := ![(1/3), 0, 0, 0, 0, 0, 0, (-1/6), 0, (-1/6), 0, 0, 0, (1/6), 0, (5/6), 0, 0, 0, 0, 0, 0, 0, (1/12), 0, 0, 0]
def productColumn_04_15 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, (-1/8), 0, 0, 0, 0, 0, 0, 0, 0, (-1/4), 0, 0, (-1/4), 0, 0, 0, 0, 0, 0, 0, 0, (1/8)]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_04_15 :
    jordan value4 value15 = decode productColumn_04_15 := by
  simp only [value4_decode, value15_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_04_15, column4, column15, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_04_15 :
    productColumn_04_15 = ∑ k : Fin 27, productCoeff_04_15 k • columns k := by
  funext r
  change productColumn_04_15 r = ∑ k : Fin 27, productCoeff_04_15 k * columns k r
  fin_cases r <;> norm_num [productColumn_04_15, productCoeff_04_15, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_04_15 :
    jordan (nativeWords 4) (nativeWords 15) =
      ∑ k : Fin 27, productCoeff_04_15 k • nativeWords k := by
  change jordan value4 value15 = _
  rw [native_product_decode_04_15, productColumn_sum_04_15, decode_sum_columns]

def productCoeff_04_16 : Fin 27 → ℝ := ![0, 0, 0, (1/6), 0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, (2/3), 0, 0, 0, 0, 0, (-1/3), 0, 0, 0, (-1/6)]
def productColumn_04_16 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, (-1/8), 0, (1/8), (1/4), 0, 0, 0, (-1/4), 0, (-1/2), 0, 0, (-1/4), 0, 0, 0, (-1/4), 0, (-1/8), (1/8), 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_04_16 :
    jordan value4 value16 = decode productColumn_04_16 := by
  simp only [value4_decode, value16_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_04_16, column4, column16, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_04_16 :
    productColumn_04_16 = ∑ k : Fin 27, productCoeff_04_16 k • columns k := by
  funext r
  change productColumn_04_16 r = ∑ k : Fin 27, productCoeff_04_16 k * columns k r
  fin_cases r <;> norm_num [productColumn_04_16, productCoeff_04_16, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_04_16 :
    jordan (nativeWords 4) (nativeWords 16) =
      ∑ k : Fin 27, productCoeff_04_16 k • nativeWords k := by
  change jordan value4 value16 = _
  rw [native_product_decode_04_16, productColumn_sum_04_16, decode_sum_columns]

def productCoeff_04_17 : Fin 27 → ℝ := ![0, 0, (2/3), 0, 0, 0, 0, 0, 0, 0, -4, 0, 0, 0, 0, 0, 0, (2/3), 0, 0, 0, (4/3), 0, 0, 0, (2/3), 0]
def productColumn_04_17 : Fin 27 → ℝ := ![0, 0, 0, 1, 0, 0, (1/4), 0, (1/4), 0, 0, 0, 2, (-1/2), 0, 0, 0, 0, (1/2), 1, 0, 0, 0, 0, (1/4), (1/4), 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_04_17 :
    jordan value4 value17 = decode productColumn_04_17 := by
  simp only [value4_decode, value17_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_04_17, column4, column17, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_04_17 :
    productColumn_04_17 = ∑ k : Fin 27, productCoeff_04_17 k • columns k := by
  funext r
  change productColumn_04_17 r = ∑ k : Fin 27, productCoeff_04_17 k * columns k r
  fin_cases r <;> norm_num [productColumn_04_17, productCoeff_04_17, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_04_17 :
    jordan (nativeWords 4) (nativeWords 17) =
      ∑ k : Fin 27, productCoeff_04_17 k • nativeWords k := by
  change jordan value4 value17 = _
  rw [native_product_decode_04_17, productColumn_sum_04_17, decode_sum_columns]

def productCoeff_04_18 : Fin 27 → ℝ := ![1, 0, 0, 0, -1, 0, 0, (-1/2), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (3/2), 0, 0, 0, 0, 0, 0, 0, 0]
def productColumn_04_18 : Fin 27 → ℝ := ![2, 0, 2, 0, (1/4), 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, (1/4), 0, 0, 0, 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_04_18 :
    jordan value4 value18 = decode productColumn_04_18 := by
  simp only [value4_decode, value18_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_04_18, column4, column18, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_04_18 :
    productColumn_04_18 = ∑ k : Fin 27, productCoeff_04_18 k • columns k := by
  funext r
  change productColumn_04_18 r = ∑ k : Fin 27, productCoeff_04_18 k * columns k r
  fin_cases r <;> norm_num [productColumn_04_18, productCoeff_04_18, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_04_18 :
    jordan (nativeWords 4) (nativeWords 18) =
      ∑ k : Fin 27, productCoeff_04_18 k • nativeWords k := by
  change jordan value4 value18 = _
  rw [native_product_decode_04_18, productColumn_sum_04_18, decode_sum_columns]

def productCoeff_04_19 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, 0, 0, (-1/2), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (3/2), 0, 0, 0, 0, 0, 0, 0]
def productColumn_04_19 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, (-1/8), 0, (-1/8), 0, 0, 0, 0, 0, 0, (-1/2), 0, 0, (1/2), 0, 0, 0, 0, 0, (-1/8), 0, 0, (-1/8)]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_04_19 :
    jordan value4 value19 = decode productColumn_04_19 := by
  simp only [value4_decode, value19_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_04_19, column4, column19, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_04_19 :
    productColumn_04_19 = ∑ k : Fin 27, productCoeff_04_19 k • columns k := by
  funext r
  change productColumn_04_19 r = ∑ k : Fin 27, productCoeff_04_19 k * columns k r
  fin_cases r <;> norm_num [productColumn_04_19, productCoeff_04_19, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_04_19 :
    jordan (nativeWords 4) (nativeWords 19) =
      ∑ k : Fin 27, productCoeff_04_19 k • nativeWords k := by
  change jordan value4 value19 = _
  rw [native_product_decode_04_19, productColumn_sum_04_19, decode_sum_columns]

end
end Glennie.Compact.NativeWordTableR01
