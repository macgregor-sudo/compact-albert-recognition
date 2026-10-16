/- Native word row 1 product certificate, part 2. -/
module
public import Glennie.Compact.NativeWordProductCommonR01

@[expose] public section
namespace Glennie.Compact.NativeWordTableR01
noncomputable section
open Glennie AlbertGeometry.NativeOperatorTrace
open scoped BigOperators Matrix
set_option autoImplicit false

def productCoeff_01_17 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
def productColumn_01_17 : Fin 27 → ℝ := ![0, 0, 0, -1, 0, 0, (-1/4), 0, (-1/4), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, (1/4), (1/4), 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_01_17 :
    jordan value1 value17 = decode productColumn_01_17 := by
  simp only [value1_decode, value17_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_01_17, column1, column17, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_01_17 :
    productColumn_01_17 = ∑ k : Fin 27, productCoeff_01_17 k • columns k := by
  funext r
  change productColumn_01_17 r = ∑ k : Fin 27, productCoeff_01_17 k * columns k r
  fin_cases r <;> norm_num [productColumn_01_17, productCoeff_01_17, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_01_17 :
    jordan (nativeWords 1) (nativeWords 17) =
      ∑ k : Fin 27, productCoeff_01_17 k • nativeWords k := by
  change jordan value1 value17 = _
  rw [native_product_decode_01_17, productColumn_sum_01_17, decode_sum_columns]

def productCoeff_01_18 : Fin 27 → ℝ := ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (1/2), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def productColumn_01_18 : Fin 27 → ℝ := ![-2, 0, 2, 0, (-1/4), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (1/4), 0, 0, 0, 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_01_18 :
    jordan value1 value18 = decode productColumn_01_18 := by
  simp only [value1_decode, value18_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_01_18, column1, column18, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_01_18 :
    productColumn_01_18 = ∑ k : Fin 27, productCoeff_01_18 k • columns k := by
  funext r
  change productColumn_01_18 r = ∑ k : Fin 27, productCoeff_01_18 k * columns k r
  fin_cases r <;> norm_num [productColumn_01_18, productCoeff_01_18, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_01_18 :
    jordan (nativeWords 1) (nativeWords 18) =
      ∑ k : Fin 27, productCoeff_01_18 k • nativeWords k := by
  change jordan value1 value18 = _
  rw [native_product_decode_01_18, productColumn_sum_01_18, decode_sum_columns]

def productCoeff_01_19 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (1/2), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def productColumn_01_19 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, (1/8), 0, (1/8), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1/8), 0, 0, (-1/8)]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_01_19 :
    jordan value1 value19 = decode productColumn_01_19 := by
  simp only [value1_decode, value19_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_01_19, column1, column19, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_01_19 :
    productColumn_01_19 = ∑ k : Fin 27, productCoeff_01_19 k • columns k := by
  funext r
  change productColumn_01_19 r = ∑ k : Fin 27, productCoeff_01_19 k * columns k r
  fin_cases r <;> norm_num [productColumn_01_19, productCoeff_01_19, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_01_19 :
    jordan (nativeWords 1) (nativeWords 19) =
      ∑ k : Fin 27, productCoeff_01_19 k • nativeWords k := by
  change jordan value1 value19 = _
  rw [native_product_decode_01_19, productColumn_sum_01_19, decode_sum_columns]

def productCoeff_01_20 : Fin 27 → ℝ := ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (1/2), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def productColumn_01_20 : Fin 27 → ℝ := ![-2, 0, 2, 0, 0, 0, 0, 0, 0, 0, (-1/4), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1/4), 0, 0, 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_01_20 :
    jordan value1 value20 = decode productColumn_01_20 := by
  simp only [value1_decode, value20_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_01_20, column1, column20, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_01_20 :
    productColumn_01_20 = ∑ k : Fin 27, productCoeff_01_20 k • columns k := by
  funext r
  change productColumn_01_20 r = ∑ k : Fin 27, productCoeff_01_20 k * columns k r
  fin_cases r <;> norm_num [productColumn_01_20, productCoeff_01_20, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_01_20 :
    jordan (nativeWords 1) (nativeWords 20) =
      ∑ k : Fin 27, productCoeff_01_20 k • nativeWords k := by
  change jordan value1 value20 = _
  rw [native_product_decode_01_20, productColumn_sum_01_20, decode_sum_columns]

def productCoeff_01_21 : Fin 27 → ℝ := ![0, 0, 0, (1/24), 0, (1/2), 0, 0, 0, 0, 0, (-1/4), 0, 0, 0, 0, (-1/12), 0, 0, 0, 0, 0, (-1/12), 0, 0, 0, (-1/6)]
def productColumn_01_21 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, (1/16), 0, 0, (-1/16), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (1/16), 0, 0, (-1/16), 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_01_21 :
    jordan value1 value21 = decode productColumn_01_21 := by
  simp only [value1_decode, value21_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_01_21, column1, column21, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_01_21 :
    productColumn_01_21 = ∑ k : Fin 27, productCoeff_01_21 k • columns k := by
  funext r
  change productColumn_01_21 r = ∑ k : Fin 27, productCoeff_01_21 k * columns k r
  fin_cases r <;> norm_num [productColumn_01_21, productCoeff_01_21, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_01_21 :
    jordan (nativeWords 1) (nativeWords 21) =
      ∑ k : Fin 27, productCoeff_01_21 k • nativeWords k := by
  change jordan value1 value21 = _
  rw [native_product_decode_01_21, productColumn_sum_01_21, decode_sum_columns]

def productCoeff_01_22 : Fin 27 → ℝ := ![0, 0, (1/6), 0, 0, 0, (-1/4), 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, (-1/12), 0, 0, 0, (1/3), 0, 0, 0, (2/3), 0]
def productColumn_01_22 : Fin 27 → ℝ := ![0, 0, 0, (1/2), 0, 0, 0, 0, (-1/8), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (1/2), 0, 0, 0, 0, (-1/8), 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_01_22 :
    jordan value1 value22 = decode productColumn_01_22 := by
  simp only [value1_decode, value22_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_01_22, column1, column22, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_01_22 :
    productColumn_01_22 = ∑ k : Fin 27, productCoeff_01_22 k • columns k := by
  funext r
  change productColumn_01_22 r = ∑ k : Fin 27, productCoeff_01_22 k * columns k r
  fin_cases r <;> norm_num [productColumn_01_22, productCoeff_01_22, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_01_22 :
    jordan (nativeWords 1) (nativeWords 22) =
      ∑ k : Fin 27, productCoeff_01_22 k • nativeWords k := by
  change jordan value1 value22 = _
  rw [native_product_decode_01_22, productColumn_sum_01_22, decode_sum_columns]

def productCoeff_01_23 : Fin 27 → ℝ := ![0, -4, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, -4, 0, 0]
def productColumn_01_23 : Fin 27 → ℝ := ![-4, 0, 4, 0, -1, (-1/4), 0, (1/4), 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, (1/4), 0, 0, (-1/4)]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_01_23 :
    jordan value1 value23 = decode productColumn_01_23 := by
  simp only [value1_decode, value23_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_01_23, column1, column23, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_01_23 :
    productColumn_01_23 = ∑ k : Fin 27, productCoeff_01_23 k • columns k := by
  funext r
  change productColumn_01_23 r = ∑ k : Fin 27, productCoeff_01_23 k * columns k r
  fin_cases r <;> norm_num [productColumn_01_23, productCoeff_01_23, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_01_23 :
    jordan (nativeWords 1) (nativeWords 23) =
      ∑ k : Fin 27, productCoeff_01_23 k • nativeWords k := by
  change jordan value1 value23 = _
  rw [native_product_decode_01_23, productColumn_sum_01_23, decode_sum_columns]

def productCoeff_01_24 : Fin 27 → ℝ := ![(-1/6), 0, 0, 0, 0, 0, 0, (1/12), 0, (1/12), 0, 0, 0, (-1/12), 0, (1/12), 0, 0, 0, 0, 0, 0, 0, (-1/24), 0, 0, 0]
def productColumn_01_24 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, (-1/16), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (1/16)]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_01_24 :
    jordan value1 value24 = decode productColumn_01_24 := by
  simp only [value1_decode, value24_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_01_24, column1, column24, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_01_24 :
    productColumn_01_24 = ∑ k : Fin 27, productCoeff_01_24 k • columns k := by
  funext r
  change productColumn_01_24 r = ∑ k : Fin 27, productCoeff_01_24 k * columns k r
  fin_cases r <;> norm_num [productColumn_01_24, productCoeff_01_24, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_01_24 :
    jordan (nativeWords 1) (nativeWords 24) =
      ∑ k : Fin 27, productCoeff_01_24 k • nativeWords k := by
  change jordan value1 value24 = _
  rw [native_product_decode_01_24, productColumn_sum_01_24, decode_sum_columns]

end
end Glennie.Compact.NativeWordTableR01
