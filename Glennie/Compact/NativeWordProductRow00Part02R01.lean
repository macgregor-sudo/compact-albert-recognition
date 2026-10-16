/- Native word row 0 product certificate, part 2. -/
module
public import Glennie.Compact.NativeWordProductCommonR01

@[expose] public section
namespace Glennie.Compact.NativeWordTableR01
noncomputable section
open Glennie AlbertGeometry.NativeOperatorTrace
open scoped BigOperators Matrix
set_option autoImplicit false

def productCoeff_00_16 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def productColumn_00_16 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, (-1/4), 0, (1/4), (1/2), 0, 0, 0, (-1/4), 0, (-1/2), 0, 0, (-1/4), 0, 0, 0, (-1/2), 0, (-1/4), (1/4), 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_00_16 :
    jordan value0 value16 = decode productColumn_00_16 := by
  simp only [value0_decode, value16_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_00_16, column0, column16, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_00_16 :
    productColumn_00_16 = ∑ k : Fin 27, productCoeff_00_16 k • columns k := by
  funext r
  change productColumn_00_16 r = ∑ k : Fin 27, productCoeff_00_16 k * columns k r
  fin_cases r <;> norm_num [productColumn_00_16, productCoeff_00_16, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_00_16 :
    jordan (nativeWords 0) (nativeWords 16) =
      ∑ k : Fin 27, productCoeff_00_16 k • nativeWords k := by
  change jordan value0 value16 = _
  rw [native_product_decode_00_16, productColumn_sum_00_16, decode_sum_columns]

def productCoeff_00_17 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def productColumn_00_17 : Fin 27 → ℝ := ![0, 0, 0, 2, 0, 0, (1/2), 0, (1/2), 0, 0, 0, 2, (-1/2), 0, 0, 0, 0, (1/2), 2, 0, 0, 0, 0, (1/2), (1/2), 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_00_17 :
    jordan value0 value17 = decode productColumn_00_17 := by
  simp only [value0_decode, value17_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_00_17, column0, column17, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_00_17 :
    productColumn_00_17 = ∑ k : Fin 27, productCoeff_00_17 k • columns k := by
  funext r
  change productColumn_00_17 r = ∑ k : Fin 27, productCoeff_00_17 k * columns k r
  fin_cases r <;> norm_num [productColumn_00_17, productCoeff_00_17, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_00_17 :
    jordan (nativeWords 0) (nativeWords 17) =
      ∑ k : Fin 27, productCoeff_00_17 k • nativeWords k := by
  change jordan value0 value17 = _
  rw [native_product_decode_00_17, productColumn_sum_00_17, decode_sum_columns]

def productCoeff_00_18 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]
def productColumn_00_18 : Fin 27 → ℝ := ![2, 0, 2, 0, (1/2), 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, (1/2), 0, 0, 0, 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_00_18 :
    jordan value0 value18 = decode productColumn_00_18 := by
  simp only [value0_decode, value18_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_00_18, column0, column18, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_00_18 :
    productColumn_00_18 = ∑ k : Fin 27, productCoeff_00_18 k • columns k := by
  funext r
  change productColumn_00_18 r = ∑ k : Fin 27, productCoeff_00_18 k * columns k r
  fin_cases r <;> norm_num [productColumn_00_18, productCoeff_00_18, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_00_18 :
    jordan (nativeWords 0) (nativeWords 18) =
      ∑ k : Fin 27, productCoeff_00_18 k • nativeWords k := by
  change jordan value0 value18 = _
  rw [native_product_decode_00_18, productColumn_sum_00_18, decode_sum_columns]

def productCoeff_00_19 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
def productColumn_00_19 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, (-1/4), 0, (-1/4), 0, 0, 0, 0, 0, 0, (-1/2), 0, 0, (1/2), 0, 0, 0, 0, 0, (-1/4), 0, 0, (-1/4)]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_00_19 :
    jordan value0 value19 = decode productColumn_00_19 := by
  simp only [value0_decode, value19_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_00_19, column0, column19, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_00_19 :
    productColumn_00_19 = ∑ k : Fin 27, productCoeff_00_19 k • columns k := by
  funext r
  change productColumn_00_19 r = ∑ k : Fin 27, productCoeff_00_19 k * columns k r
  fin_cases r <;> norm_num [productColumn_00_19, productCoeff_00_19, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_00_19 :
    jordan (nativeWords 0) (nativeWords 19) =
      ∑ k : Fin 27, productCoeff_00_19 k • nativeWords k := by
  change jordan value0 value19 = _
  rw [native_product_decode_00_19, productColumn_sum_00_19, decode_sum_columns]

def productCoeff_00_20 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]
def productColumn_00_20 : Fin 27 → ℝ := ![2, 0, 2, 0, 0, 0, 0, 0, 0, 0, (1/2), 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, (-1/2), 0, 0, 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_00_20 :
    jordan value0 value20 = decode productColumn_00_20 := by
  simp only [value0_decode, value20_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_00_20, column0, column20, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_00_20 :
    productColumn_00_20 = ∑ k : Fin 27, productCoeff_00_20 k • columns k := by
  funext r
  change productColumn_00_20 r = ∑ k : Fin 27, productCoeff_00_20 k * columns k r
  fin_cases r <;> norm_num [productColumn_00_20, productCoeff_00_20, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_00_20 :
    jordan (nativeWords 0) (nativeWords 20) =
      ∑ k : Fin 27, productCoeff_00_20 k • nativeWords k := by
  change jordan value0 value20 = _
  rw [native_product_decode_00_20, productColumn_sum_00_20, decode_sum_columns]

def productCoeff_00_21 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
def productColumn_00_21 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, (-1/8), 0, 0, (1/8), 0, 0, 0, (-1/8), 0, 0, 0, 0, (1/8), 0, 0, 0, (1/8), 0, 0, (-1/8), 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_00_21 :
    jordan value0 value21 = decode productColumn_00_21 := by
  simp only [value0_decode, value21_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_00_21, column0, column21, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_00_21 :
    productColumn_00_21 = ∑ k : Fin 27, productCoeff_00_21 k • columns k := by
  funext r
  change productColumn_00_21 r = ∑ k : Fin 27, productCoeff_00_21 k * columns k r
  fin_cases r <;> norm_num [productColumn_00_21, productCoeff_00_21, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_00_21 :
    jordan (nativeWords 0) (nativeWords 21) =
      ∑ k : Fin 27, productCoeff_00_21 k • nativeWords k := by
  change jordan value0 value21 = _
  rw [native_product_decode_00_21, productColumn_sum_00_21, decode_sum_columns]

def productCoeff_00_22 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]
def productColumn_00_22 : Fin 27 → ℝ := ![0, 0, 0, -1, 0, 0, 0, 0, (1/4), 0, 0, 0, 0, (1/4), 0, 0, 0, 0, (1/4), 1, 0, 0, 0, 0, (-1/4), 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_00_22 :
    jordan value0 value22 = decode productColumn_00_22 := by
  simp only [value0_decode, value22_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_00_22, column0, column22, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_00_22 :
    productColumn_00_22 = ∑ k : Fin 27, productCoeff_00_22 k • columns k := by
  funext r
  change productColumn_00_22 r = ∑ k : Fin 27, productCoeff_00_22 k * columns k r
  fin_cases r <;> norm_num [productColumn_00_22, productCoeff_00_22, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_00_22 :
    jordan (nativeWords 0) (nativeWords 22) =
      ∑ k : Fin 27, productCoeff_00_22 k • nativeWords k := by
  change jordan value0 value22 = _
  rw [native_product_decode_00_22, productColumn_sum_00_22, decode_sum_columns]

def productCoeff_00_23 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0]
def productColumn_00_23 : Fin 27 → ℝ := ![4, 4, 4, 0, 2, (1/2), 0, (-1/2), 0, 0, 2, 2, 0, 0, (-1/2), 0, 2, (-1/2), 0, 0, 2, -2, 0, (1/2), 0, 0, (-1/2)]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_00_23 :
    jordan value0 value23 = decode productColumn_00_23 := by
  simp only [value0_decode, value23_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_00_23, column0, column23, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_00_23 :
    productColumn_00_23 = ∑ k : Fin 27, productCoeff_00_23 k • columns k := by
  funext r
  change productColumn_00_23 r = ∑ k : Fin 27, productCoeff_00_23 k * columns k r
  fin_cases r <;> norm_num [productColumn_00_23, productCoeff_00_23, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_00_23 :
    jordan (nativeWords 0) (nativeWords 23) =
      ∑ k : Fin 27, productCoeff_00_23 k • nativeWords k := by
  change jordan value0 value23 = _
  rw [native_product_decode_00_23, productColumn_sum_00_23, decode_sum_columns]

end
end Glennie.Compact.NativeWordTableR01
