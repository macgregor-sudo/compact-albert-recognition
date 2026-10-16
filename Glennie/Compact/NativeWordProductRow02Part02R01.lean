/- Native word row 2 product certificate, part 2. -/
module
public import Glennie.Compact.NativeWordProductCommonR01

@[expose] public section
namespace Glennie.Compact.NativeWordTableR01
noncomputable section
open Glennie AlbertGeometry.NativeOperatorTrace
open scoped BigOperators Matrix
set_option autoImplicit false

def productCoeff_02_18 : Fin 27 → ℝ := ![0, 0, (5/2), 0, 0, 0, 0, 0, 0, 0, -3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def productColumn_02_18 : Fin 27 → ℝ := ![0, 0, 0, (7/4), 0, 0, 0, 0, 0, 0, 0, 0, (5/2), 0, 0, 0, 0, 0, 0, (7/4), 0, 0, 0, 0, 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_02_18 :
    jordan value2 value18 = decode productColumn_02_18 := by
  simp only [value2_decode, value18_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_02_18, column2, column18, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_02_18 :
    productColumn_02_18 = ∑ k : Fin 27, productCoeff_02_18 k • columns k := by
  funext r
  change productColumn_02_18 r = ∑ k : Fin 27, productCoeff_02_18 k * columns k r
  fin_cases r <;> norm_num [productColumn_02_18, productCoeff_02_18, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_02_18 :
    jordan (nativeWords 2) (nativeWords 18) =
      ∑ k : Fin 27, productCoeff_02_18 k • nativeWords k := by
  change jordan value2 value18 = _
  rw [native_product_decode_02_18, productColumn_sum_02_18, decode_sum_columns]

def productCoeff_02_19 : Fin 27 → ℝ := ![0, 0, 0, (-1/12), 0, -1, 0, 0, 0, 0, 0, (1/2), 0, 0, 0, 0, (2/3), 0, 0, 0, 0, 0, (1/6), 0, 0, 0, (1/3)]
def productColumn_02_19 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, (-1/4), 0, (1/8), (3/8), 0, 0, 0, (-1/8), 0, (-1/4), 0, 0, (-1/8), 0, 0, 0, (-3/8), 0, (-1/8), (1/4), 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_02_19 :
    jordan value2 value19 = decode productColumn_02_19 := by
  simp only [value2_decode, value19_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_02_19, column2, column19, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_02_19 :
    productColumn_02_19 = ∑ k : Fin 27, productCoeff_02_19 k • columns k := by
  funext r
  change productColumn_02_19 r = ∑ k : Fin 27, productCoeff_02_19 k * columns k r
  fin_cases r <;> norm_num [productColumn_02_19, productCoeff_02_19, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_02_19 :
    jordan (nativeWords 2) (nativeWords 19) =
      ∑ k : Fin 27, productCoeff_02_19 k • nativeWords k := by
  change jordan value2 value19 = _
  rw [native_product_decode_02_19, productColumn_sum_02_19, decode_sum_columns]

def productCoeff_02_20 : Fin 27 → ℝ := ![0, 0, (2/3), 0, 0, 0, (1/2), 0, 0, 0, -4, 0, 0, 0, 0, 0, 0, (2/3), 0, 0, 0, (-2/3), 0, 0, 0, (-4/3), 0]
def productColumn_02_20 : Fin 27 → ℝ := ![0, 0, 0, 1, 0, 0, (1/4), 0, (1/2), 0, 0, 0, 2, (-1/4), 0, 0, 0, 0, (1/4), 1, 0, 0, 0, 0, (1/2), (1/4), 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_02_20 :
    jordan value2 value20 = decode productColumn_02_20 := by
  simp only [value2_decode, value20_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_02_20, column2, column20, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_02_20 :
    productColumn_02_20 = ∑ k : Fin 27, productCoeff_02_20 k • columns k := by
  funext r
  change productColumn_02_20 r = ∑ k : Fin 27, productCoeff_02_20 k * columns k r
  fin_cases r <;> norm_num [productColumn_02_20, productCoeff_02_20, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_02_20 :
    jordan (nativeWords 2) (nativeWords 20) =
      ∑ k : Fin 27, productCoeff_02_20 k • nativeWords k := by
  change jordan value2 value20 = _
  rw [native_product_decode_02_20, productColumn_sum_02_20, decode_sum_columns]

def productCoeff_02_21 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def productColumn_02_21 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_02_21 :
    jordan value2 value21 = decode productColumn_02_21 := by
  simp only [value2_decode, value21_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_02_21, column2, column21, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_02_21 :
    productColumn_02_21 = ∑ k : Fin 27, productCoeff_02_21 k • columns k := by
  funext r
  change productColumn_02_21 r = ∑ k : Fin 27, productCoeff_02_21 k * columns k r
  fin_cases r <;> norm_num [productColumn_02_21, productCoeff_02_21, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_02_21 :
    jordan (nativeWords 2) (nativeWords 21) =
      ∑ k : Fin 27, productCoeff_02_21 k • nativeWords k := by
  change jordan value2 value21 = _
  rw [native_product_decode_02_21, productColumn_sum_02_21, decode_sum_columns]

def productCoeff_02_22 : Fin 27 → ℝ := ![0, (7/2), 0, 0, 0, 0, 0, 0, (1/2), 0, 0, 0, -1, 0, (-1/4), 0, 0, 0, 0, (-1/2), 0, 0, 0, 0, 2, 0, 0]
def productColumn_02_22 : Fin 27 → ℝ := ![-1, 0, 1, 0, (1/2), (1/8), 0, (-1/8), 0, 0, (1/8), 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1/2), (1/8), 0, (-1/8), 0, 0, (1/8)]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_02_22 :
    jordan value2 value22 = decode productColumn_02_22 := by
  simp only [value2_decode, value22_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_02_22, column2, column22, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_02_22 :
    productColumn_02_22 = ∑ k : Fin 27, productCoeff_02_22 k • columns k := by
  funext r
  change productColumn_02_22 r = ∑ k : Fin 27, productCoeff_02_22 k * columns k r
  fin_cases r <;> norm_num [productColumn_02_22, productCoeff_02_22, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_02_22 :
    jordan (nativeWords 2) (nativeWords 22) =
      ∑ k : Fin 27, productCoeff_02_22 k • nativeWords k := by
  change jordan value2 value22 = _
  rw [native_product_decode_02_22, productColumn_sum_02_22, decode_sum_columns]

def productCoeff_02_23 : Fin 27 → ℝ := ![0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (3/2), 0, 0, 0, 0, 0, 0, 0, 0, 0]
def productColumn_02_23 : Fin 27 → ℝ := ![0, 0, 0, 6, 0, 0, (3/4), 0, (3/4), 0, 0, 0, 6, (-3/4), 0, 0, 0, 0, (3/4), 6, 0, 0, 0, 0, (3/4), (3/4), 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_02_23 :
    jordan value2 value23 = decode productColumn_02_23 := by
  simp only [value2_decode, value23_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_02_23, column2, column23, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_02_23 :
    productColumn_02_23 = ∑ k : Fin 27, productCoeff_02_23 k • columns k := by
  funext r
  change productColumn_02_23 r = ∑ k : Fin 27, productCoeff_02_23 k * columns k r
  fin_cases r <;> norm_num [productColumn_02_23, productCoeff_02_23, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_02_23 :
    jordan (nativeWords 2) (nativeWords 23) =
      ∑ k : Fin 27, productCoeff_02_23 k • nativeWords k := by
  change jordan value2 value23 = _
  rw [native_product_decode_02_23, productColumn_sum_02_23, decode_sum_columns]

def productCoeff_02_24 : Fin 27 → ℝ := ![0, 0, 0, (1/24), 0, (-1/2), 0, 0, 0, 0, 0, (-1/4), 0, 0, 0, 0, (-1/12), 0, 0, 0, 0, 0, (1/6), 0, 0, 0, (1/12)]
def productColumn_02_24 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, (-1/16), 0, 0, 0, (1/16), 0, 0, 0, 0, (1/16), 0, 0, 0, (1/16), 0, 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_02_24 :
    jordan value2 value24 = decode productColumn_02_24 := by
  simp only [value2_decode, value24_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_02_24, column2, column24, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_02_24 :
    productColumn_02_24 = ∑ k : Fin 27, productCoeff_02_24 k • columns k := by
  funext r
  change productColumn_02_24 r = ∑ k : Fin 27, productCoeff_02_24 k * columns k r
  fin_cases r <;> norm_num [productColumn_02_24, productCoeff_02_24, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_02_24 :
    jordan (nativeWords 2) (nativeWords 24) =
      ∑ k : Fin 27, productCoeff_02_24 k • nativeWords k := by
  change jordan value2 value24 = _
  rw [native_product_decode_02_24, productColumn_sum_02_24, decode_sum_columns]

def productCoeff_02_25 : Fin 27 → ℝ := ![(-1/2), 0, 0, 0, (3/4), 0, 0, 0, 0, (1/4), 0, 0, 0, (-1/4), 0, (1/4), 0, 0, 0, 0, (-3/8), 0, 0, 0, 0, 0, 0]
def productColumn_02_25 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, (-1/8), 0, (-1/16), 0, 0, (1/16), 0, 0, 0, (-1/16), 0, (-1/8), (-1/16), 0, 0, 0, (-1/16), 0, (1/16), 0, 0, (1/8)]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_02_25 :
    jordan value2 value25 = decode productColumn_02_25 := by
  simp only [value2_decode, value25_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_02_25, column2, column25, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_02_25 :
    productColumn_02_25 = ∑ k : Fin 27, productCoeff_02_25 k • columns k := by
  funext r
  change productColumn_02_25 r = ∑ k : Fin 27, productCoeff_02_25 k * columns k r
  fin_cases r <;> norm_num [productColumn_02_25, productCoeff_02_25, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_02_25 :
    jordan (nativeWords 2) (nativeWords 25) =
      ∑ k : Fin 27, productCoeff_02_25 k • nativeWords k := by
  change jordan value2 value25 = _
  rw [native_product_decode_02_25, productColumn_sum_02_25, decode_sum_columns]

end
end Glennie.Compact.NativeWordTableR01
