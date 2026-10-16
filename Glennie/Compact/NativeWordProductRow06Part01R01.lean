/- Native word row 6 product certificate, part 1. -/
module
public import Glennie.Compact.NativeWordProductCommonR01

@[expose] public section
namespace Glennie.Compact.NativeWordTableR01
noncomputable section
open Glennie AlbertGeometry.NativeOperatorTrace
open scoped BigOperators Matrix
set_option autoImplicit false

def productCoeff_06_14 : Fin 27 → ℝ := ![0, 0, 0, (-1/4), 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def productColumn_06_14 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, (1/2), 0, 0, 0, 0, 0, (1/4), 0, 0, 0, 0, 0, 0, (-1/2), 0, 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_06_14 :
    jordan value6 value14 = decode productColumn_06_14 := by
  simp only [value6_decode, value14_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_06_14, column6, column14, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_06_14 :
    productColumn_06_14 = ∑ k : Fin 27, productCoeff_06_14 k • columns k := by
  funext r
  change productColumn_06_14 r = ∑ k : Fin 27, productCoeff_06_14 k * columns k r
  fin_cases r <;> norm_num [productColumn_06_14, productCoeff_06_14, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_06_14 :
    jordan (nativeWords 6) (nativeWords 14) =
      ∑ k : Fin 27, productCoeff_06_14 k • nativeWords k := by
  change jordan value6 value14 = _
  rw [native_product_decode_06_14, productColumn_sum_06_14, decode_sum_columns]

def productCoeff_06_15 : Fin 27 → ℝ := ![0, 0, (1/24), 0, 0, 0, (1/8), 0, 0, 0, (-1/4), 0, 0, 0, 0, 0, 0, (1/24), 0, 0, 0, (-1/6), 0, 0, 0, (-1/3), 0]
def productColumn_06_15 : Fin 27 → ℝ := ![0, 0, 0, (1/16), 0, 0, 0, 0, (1/16), 0, 0, 0, (1/8), 0, 0, 0, 0, 0, 0, (1/16), 0, 0, 0, 0, (1/16), 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_06_15 :
    jordan value6 value15 = decode productColumn_06_15 := by
  simp only [value6_decode, value15_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_06_15, column6, column15, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_06_15 :
    productColumn_06_15 = ∑ k : Fin 27, productCoeff_06_15 k • columns k := by
  funext r
  change productColumn_06_15 r = ∑ k : Fin 27, productCoeff_06_15 k * columns k r
  fin_cases r <;> norm_num [productColumn_06_15, productCoeff_06_15, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_06_15 :
    jordan (nativeWords 6) (nativeWords 15) =
      ∑ k : Fin 27, productCoeff_06_15 k • nativeWords k := by
  change jordan value6 value15 = _
  rw [native_product_decode_06_15, productColumn_sum_06_15, decode_sum_columns]

def productCoeff_06_16 : Fin 27 → ℝ := ![0, (1/2), 0, 0, 0, 0, 0, 0, (3/8), 0, 0, 0, (1/8), 0, (-1/4), 0, 0, 0, 0, (-1/2), 0, 0, 0, 0, (1/2), 0, 0]
def productColumn_06_16 : Fin 27 → ℝ := ![(-1/4), 0, (1/4), 0, (-1/16), 0, 0, (-1/16), 0, 0, (1/8), 0, 0, 0, (1/16), 0, 0, (-1/16), 0, 0, (1/16), (1/8), 0, (-1/16), 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_06_16 :
    jordan value6 value16 = decode productColumn_06_16 := by
  simp only [value6_decode, value16_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_06_16, column6, column16, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_06_16 :
    productColumn_06_16 = ∑ k : Fin 27, productCoeff_06_16 k • columns k := by
  funext r
  change productColumn_06_16 r = ∑ k : Fin 27, productCoeff_06_16 k * columns k r
  fin_cases r <;> norm_num [productColumn_06_16, productCoeff_06_16, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_06_16 :
    jordan (nativeWords 6) (nativeWords 16) =
      ∑ k : Fin 27, productCoeff_06_16 k • nativeWords k := by
  change jordan value6 value16 = _
  rw [native_product_decode_06_16, productColumn_sum_06_16, decode_sum_columns]

def productCoeff_06_17 : Fin 27 → ℝ := ![1, 0, 0, 0, (-3/2), 0, 0, (-1/2), 0, 0, 0, 0, 0, (1/2), 0, (5/2), 0, 0, (3/4), 0, 0, 0, 0, 0, 0, 0, 0]
def productColumn_06_17 : Fin 27 → ℝ := ![0, 0, 0, 0, (-1/8), (-1/2), 0, (1/8), 0, 0, 0, (1/4), 0, 0, (-5/8), 0, 0, (-5/8), 0, 0, (-1/8), 0, 0, (-1/8), 0, 0, (1/2)]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_06_17 :
    jordan value6 value17 = decode productColumn_06_17 := by
  simp only [value6_decode, value17_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_06_17, column6, column17, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_06_17 :
    productColumn_06_17 = ∑ k : Fin 27, productCoeff_06_17 k • columns k := by
  funext r
  change productColumn_06_17 r = ∑ k : Fin 27, productCoeff_06_17 k * columns k r
  fin_cases r <;> norm_num [productColumn_06_17, productCoeff_06_17, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_06_17 :
    jordan (nativeWords 6) (nativeWords 17) =
      ∑ k : Fin 27, productCoeff_06_17 k • nativeWords k := by
  change jordan value6 value17 = _
  rw [native_product_decode_06_17, productColumn_sum_06_17, decode_sum_columns]

def productCoeff_06_18 : Fin 27 → ℝ := ![0, 0, (-1/6), 0, 0, 0, (1/2), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (1/12), 0, 0, 0, (-4/3), 0, 0, 0, (1/3), 0]
def productColumn_06_18 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, (1/4), 0, 0, (-1/2), 0, 0, 0, (1/8), 0, 0, 0, 0, (-1/8), 0, 0, 0, (-1/2), 0, 0, (1/4), 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_06_18 :
    jordan value6 value18 = decode productColumn_06_18 := by
  simp only [value6_decode, value18_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_06_18, column6, column18, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_06_18 :
    productColumn_06_18 = ∑ k : Fin 27, productCoeff_06_18 k • columns k := by
  funext r
  change productColumn_06_18 r = ∑ k : Fin 27, productCoeff_06_18 k * columns k r
  fin_cases r <;> norm_num [productColumn_06_18, productCoeff_06_18, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_06_18 :
    jordan (nativeWords 6) (nativeWords 18) =
      ∑ k : Fin 27, productCoeff_06_18 k • nativeWords k := by
  change jordan value6 value18 = _
  rw [native_product_decode_06_18, productColumn_sum_06_18, decode_sum_columns]

def productCoeff_06_19 : Fin 27 → ℝ := ![0, 0, 0, (1/24), 0, (1/4), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1/12), 0, 0, 0, 0, 0, (-1/3), 0, 0, 0, (1/12)]
def productColumn_06_19 : Fin 27 → ℝ := ![0, 0, 0, (1/8), 0, 0, 0, 0, (-1/8), 0, 0, 0, 0, (-1/16), 0, 0, 0, 0, (-1/16), (-1/8), 0, 0, 0, 0, (1/8), 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_06_19 :
    jordan value6 value19 = decode productColumn_06_19 := by
  simp only [value6_decode, value19_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_06_19, column6, column19, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_06_19 :
    productColumn_06_19 = ∑ k : Fin 27, productCoeff_06_19 k • columns k := by
  funext r
  change productColumn_06_19 r = ∑ k : Fin 27, productCoeff_06_19 k * columns k r
  fin_cases r <;> norm_num [productColumn_06_19, productCoeff_06_19, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_06_19 :
    jordan (nativeWords 6) (nativeWords 19) =
      ∑ k : Fin 27, productCoeff_06_19 k • nativeWords k := by
  change jordan value6 value19 = _
  rw [native_product_decode_06_19, productColumn_sum_06_19, decode_sum_columns]

def productCoeff_06_20 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, (1/2), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def productColumn_06_20 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, (-1/4), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1/4), 0, 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_06_20 :
    jordan value6 value20 = decode productColumn_06_20 := by
  simp only [value6_decode, value20_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_06_20, column6, column20, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_06_20 :
    productColumn_06_20 = ∑ k : Fin 27, productCoeff_06_20 k • columns k := by
  funext r
  change productColumn_06_20 r = ∑ k : Fin 27, productCoeff_06_20 k * columns k r
  fin_cases r <;> norm_num [productColumn_06_20, productCoeff_06_20, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_06_20 :
    jordan (nativeWords 6) (nativeWords 20) =
      ∑ k : Fin 27, productCoeff_06_20 k • nativeWords k := by
  change jordan value6 value20 = _
  rw [native_product_decode_06_20, productColumn_sum_06_20, decode_sum_columns]

def productCoeff_06_21 : Fin 27 → ℝ := ![(-1/12), 0, 0, 0, (-1/16), 0, 0, (1/24), 0, (-1/48), 0, 0, 0, (1/12), 0, (1/24), 0, 0, (-1/16), 0, (1/8), 0, 0, (-1/48), 0, 0, 0]
def productColumn_06_21 : Fin 27 → ℝ := ![(-1/16), (-1/8), (-1/16), 0, (-1/32), 0, 0, (1/32), 0, 0, 0, (-1/16), 0, 0, 0, 0, (1/16), 0, 0, 0, (-1/32), 0, 0, (-1/32), 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_06_21 :
    jordan value6 value21 = decode productColumn_06_21 := by
  simp only [value6_decode, value21_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_06_21, column6, column21, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_06_21 :
    productColumn_06_21 = ∑ k : Fin 27, productCoeff_06_21 k • columns k := by
  funext r
  change productColumn_06_21 r = ∑ k : Fin 27, productCoeff_06_21 k * columns k r
  fin_cases r <;> norm_num [productColumn_06_21, productCoeff_06_21, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_06_21 :
    jordan (nativeWords 6) (nativeWords 21) =
      ∑ k : Fin 27, productCoeff_06_21 k • nativeWords k := by
  change jordan value6 value21 = _
  rw [native_product_decode_06_21, productColumn_sum_06_21, decode_sum_columns]

end
end Glennie.Compact.NativeWordTableR01
