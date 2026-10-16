/- Native word row 5 product certificate, part 1. -/
module
public import Glennie.Compact.NativeWordProductCommonR01

@[expose] public section
namespace Glennie.Compact.NativeWordTableR01
noncomputable section
open Glennie AlbertGeometry.NativeOperatorTrace
open scoped BigOperators Matrix
set_option autoImplicit false

def productCoeff_05_13 : Fin 27 → ℝ := ![0, 0, 0, (-1/12), 0, (-1/2), 0, 0, 0, 0, 0, (1/2), 0, 0, 0, 0, (-1/12), 0, 0, 0, 0, 0, (1/6), 0, 0, 0, (1/12)]
def productColumn_05_13 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (1/16), 0, (1/8), 0, 0, (1/16), 0, 0, 0, 0, 0, 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_05_13 :
    jordan value5 value13 = decode productColumn_05_13 := by
  simp only [value5_decode, value13_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_05_13, column5, column13, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_05_13 :
    productColumn_05_13 = ∑ k : Fin 27, productCoeff_05_13 k • columns k := by
  funext r
  change productColumn_05_13 r = ∑ k : Fin 27, productCoeff_05_13 k * columns k r
  fin_cases r <;> norm_num [productColumn_05_13, productCoeff_05_13, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_05_13 :
    jordan (nativeWords 5) (nativeWords 13) =
      ∑ k : Fin 27, productCoeff_05_13 k • nativeWords k := by
  change jordan value5 value13 = _
  rw [native_product_decode_05_13, productColumn_sum_05_13, decode_sum_columns]

def productCoeff_05_14 : Fin 27 → ℝ := ![0, 0, (1/6), 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, (-1/12), 0, 0, 0, (-2/3), 0, 0, 0, (-1/3), 0]
def productColumn_05_14 : Fin 27 → ℝ := ![0, 0, 0, (1/2), 0, 0, 0, 0, 0, 0, 0, 0, 0, (1/8), 0, 0, 0, 0, (-1/8), (1/2), 0, 0, 0, 0, 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_05_14 :
    jordan value5 value14 = decode productColumn_05_14 := by
  simp only [value5_decode, value14_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_05_14, column5, column14, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_05_14 :
    productColumn_05_14 = ∑ k : Fin 27, productCoeff_05_14 k • columns k := by
  funext r
  change productColumn_05_14 r = ∑ k : Fin 27, productCoeff_05_14 k * columns k r
  fin_cases r <;> norm_num [productColumn_05_14, productCoeff_05_14, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_05_14 :
    jordan (nativeWords 5) (nativeWords 14) =
      ∑ k : Fin 27, productCoeff_05_14 k • nativeWords k := by
  change jordan value5 value14 = _
  rw [native_product_decode_05_14, productColumn_sum_05_14, decode_sum_columns]

def productCoeff_05_15 : Fin 27 → ℝ := ![0, 0, 0, (-1/12), 0, 0, 0, 0, 0, 0, 0, (-1/4), 0, 0, 0, 0, (1/6), 0, 0, 0, 0, 0, (-1/12), 0, 0, 0, (1/12)]
def productColumn_05_15 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, (-1/16), 0, 0, (-1/16), 0, 0, 0, (-1/16), 0, 0, 0, 0, (-1/16), 0, 0, 0, (1/16), 0, 0, (1/16), 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_05_15 :
    jordan value5 value15 = decode productColumn_05_15 := by
  simp only [value5_decode, value15_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_05_15, column5, column15, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_05_15 :
    productColumn_05_15 = ∑ k : Fin 27, productCoeff_05_15 k • columns k := by
  funext r
  change productColumn_05_15 r = ∑ k : Fin 27, productCoeff_05_15 k * columns k r
  fin_cases r <;> norm_num [productColumn_05_15, productCoeff_05_15, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_05_15 :
    jordan (nativeWords 5) (nativeWords 15) =
      ∑ k : Fin 27, productCoeff_05_15 k • nativeWords k := by
  change jordan value5 value15 = _
  rw [native_product_decode_05_15, productColumn_sum_05_15, decode_sum_columns]

def productCoeff_05_16 : Fin 27 → ℝ := ![(1/2), 0, 0, 0, (-3/4), 0, 0, 0, 0, (-1/4), 0, 0, 0, (-1/2), 0, (-1/4), 0, 0, 0, 0, (3/8), 0, 0, 0, 0, 0, 0]
def productColumn_05_16 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, (-1/16), 0, (-1/8), 0, 0, (-1/16), 0, 0, 0, (1/16), 0, (1/8), (1/16), 0, 0, 0, (1/16), 0, (1/8), 0, 0, (1/16)]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_05_16 :
    jordan value5 value16 = decode productColumn_05_16 := by
  simp only [value5_decode, value16_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_05_16, column5, column16, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_05_16 :
    productColumn_05_16 = ∑ k : Fin 27, productCoeff_05_16 k • columns k := by
  funext r
  change productColumn_05_16 r = ∑ k : Fin 27, productCoeff_05_16 k * columns k r
  fin_cases r <;> norm_num [productColumn_05_16, productCoeff_05_16, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_05_16 :
    jordan (nativeWords 5) (nativeWords 16) =
      ∑ k : Fin 27, productCoeff_05_16 k • nativeWords k := by
  change jordan value5 value16 = _
  rw [native_product_decode_05_16, productColumn_sum_05_16, decode_sum_columns]

def productCoeff_05_17 : Fin 27 → ℝ := ![0, (7/2), 0, 0, 0, 0, 0, 0, (1/4), 0, 0, 0, -1, 0, (-1/4), 0, 0, 0, 0, (-1/2), 0, 0, 0, 0, -1, 0, 0]
def productColumn_05_17 : Fin 27 → ℝ := ![-1, 0, 1, 0, (1/2), (-1/8), 0, 0, 0, 0, (1/8), 0, 0, 0, (1/8), 0, 0, (-1/8), 0, 0, (-1/2), (1/8), 0, 0, 0, 0, (-1/8)]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_05_17 :
    jordan value5 value17 = decode productColumn_05_17 := by
  simp only [value5_decode, value17_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_05_17, column5, column17, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_05_17 :
    productColumn_05_17 = ∑ k : Fin 27, productCoeff_05_17 k • columns k := by
  funext r
  change productColumn_05_17 r = ∑ k : Fin 27, productCoeff_05_17 k * columns k r
  fin_cases r <;> norm_num [productColumn_05_17, productCoeff_05_17, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_05_17 :
    jordan (nativeWords 5) (nativeWords 17) =
      ∑ k : Fin 27, productCoeff_05_17 k • nativeWords k := by
  change jordan value5 value17 = _
  rw [native_product_decode_05_17, productColumn_sum_05_17, decode_sum_columns]

def productCoeff_05_18 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, (1/2), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def productColumn_05_18 : Fin 27 → ℝ := ![0, 0, 0, (-1/4), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (1/4), 0, 0, 0, 0, 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_05_18 :
    jordan value5 value18 = decode productColumn_05_18 := by
  simp only [value5_decode, value18_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_05_18, column5, column18, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_05_18 :
    productColumn_05_18 = ∑ k : Fin 27, productCoeff_05_18 k • columns k := by
  funext r
  change productColumn_05_18 r = ∑ k : Fin 27, productCoeff_05_18 k * columns k r
  fin_cases r <;> norm_num [productColumn_05_18, productCoeff_05_18, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_05_18 :
    jordan (nativeWords 5) (nativeWords 18) =
      ∑ k : Fin 27, productCoeff_05_18 k • nativeWords k := by
  change jordan value5 value18 = _
  rw [native_product_decode_05_18, productColumn_sum_05_18, decode_sum_columns]

def productCoeff_05_19 : Fin 27 → ℝ := ![0, 0, (1/12), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1/24), 0, 0, 0, (2/3), 0, 0, 0, (-1/6), 0]
def productColumn_05_19 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, (-1/8), 0, 0, (1/8), 0, 0, 0, (-1/16), 0, 0, 0, 0, (1/16), 0, 0, 0, (1/8), 0, 0, (-1/8), 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_05_19 :
    jordan value5 value19 = decode productColumn_05_19 := by
  simp only [value5_decode, value19_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_05_19, column5, column19, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_05_19 :
    productColumn_05_19 = ∑ k : Fin 27, productCoeff_05_19 k • columns k := by
  funext r
  change productColumn_05_19 r = ∑ k : Fin 27, productCoeff_05_19 k * columns k r
  fin_cases r <;> norm_num [productColumn_05_19, productCoeff_05_19, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_05_19 :
    jordan (nativeWords 5) (nativeWords 19) =
      ∑ k : Fin 27, productCoeff_05_19 k • nativeWords k := by
  change jordan value5 value19 = _
  rw [native_product_decode_05_19, productColumn_sum_05_19, decode_sum_columns]

def productCoeff_05_20 : Fin 27 → ℝ := ![0, 0, 0, (-1/12), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (1/6), 0, 0, 0, 0, 0, (2/3), 0, 0, 0, (-1/6)]
def productColumn_05_20 : Fin 27 → ℝ := ![0, 0, 0, (-1/2), 0, 0, 0, 0, (1/4), 0, 0, 0, 0, (1/8), 0, 0, 0, 0, (1/8), (1/2), 0, 0, 0, 0, (-1/4), 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_05_20 :
    jordan value5 value20 = decode productColumn_05_20 := by
  simp only [value5_decode, value20_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_05_20, column5, column20, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_05_20 :
    productColumn_05_20 = ∑ k : Fin 27, productCoeff_05_20 k • columns k := by
  funext r
  change productColumn_05_20 r = ∑ k : Fin 27, productCoeff_05_20 k * columns k r
  fin_cases r <;> norm_num [productColumn_05_20, productCoeff_05_20, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_05_20 :
    jordan (nativeWords 5) (nativeWords 20) =
      ∑ k : Fin 27, productCoeff_05_20 k • nativeWords k := by
  change jordan value5 value20 = _
  rw [native_product_decode_05_20, productColumn_sum_05_20, decode_sum_columns]

end
end Glennie.Compact.NativeWordTableR01
