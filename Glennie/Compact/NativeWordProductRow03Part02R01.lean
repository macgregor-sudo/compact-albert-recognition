/- Native word row 3 product certificate, part 2. -/
module
public import Glennie.Compact.NativeWordProductCommonR01

@[expose] public section
namespace Glennie.Compact.NativeWordTableR01
noncomputable section
open Glennie AlbertGeometry.NativeOperatorTrace
open scoped BigOperators Matrix
set_option autoImplicit false

def productCoeff_03_19 : Fin 27 → ℝ := ![0, 0, (11/12), 0, 0, 0, (-1/4), 0, 0, 0, (1/2), 0, 0, 0, 0, 0, 0, (-1/3), 0, 0, 0, (1/3), 0, 0, 0, (2/3), 0]
def productColumn_03_19 : Fin 27 → ℝ := ![0, 0, 0, (3/8), 0, 0, (-1/8), 0, (-1/4), 0, 0, 0, (1/4), (1/8), 0, 0, 0, 0, (-1/8), (3/8), 0, 0, 0, 0, (-1/4), (-1/8), 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_03_19 :
    jordan value3 value19 = decode productColumn_03_19 := by
  simp only [value3_decode, value19_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_03_19, column3, column19, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_03_19 :
    productColumn_03_19 = ∑ k : Fin 27, productCoeff_03_19 k • columns k := by
  funext r
  change productColumn_03_19 r = ∑ k : Fin 27, productCoeff_03_19 k * columns k r
  fin_cases r <;> norm_num [productColumn_03_19, productCoeff_03_19, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_03_19 :
    jordan (nativeWords 3) (nativeWords 19) =
      ∑ k : Fin 27, productCoeff_03_19 k • nativeWords k := by
  change jordan value3 value19 = _
  rw [native_product_decode_03_19, productColumn_sum_03_19, decode_sum_columns]

def productCoeff_03_20 : Fin 27 → ℝ := ![0, 0, 0, (5/2), 0, 0, 0, 0, 0, 0, 0, -3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def productColumn_03_20 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, (7/4), 0, 0, 0, 0, 0, (-5/2), 0, 0, 0, 0, 0, 0, (-7/4), 0, 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_03_20 :
    jordan value3 value20 = decode productColumn_03_20 := by
  simp only [value3_decode, value20_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_03_20, column3, column20, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_03_20 :
    productColumn_03_20 = ∑ k : Fin 27, productCoeff_03_20 k • columns k := by
  funext r
  change productColumn_03_20 r = ∑ k : Fin 27, productCoeff_03_20 k * columns k r
  fin_cases r <;> norm_num [productColumn_03_20, productCoeff_03_20, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_03_20 :
    jordan (nativeWords 3) (nativeWords 20) =
      ∑ k : Fin 27, productCoeff_03_20 k • nativeWords k := by
  change jordan value3 value20 = _
  rw [native_product_decode_03_20, productColumn_sum_03_20, decode_sum_columns]

def productCoeff_03_21 : Fin 27 → ℝ := ![0, (-5/8), 0, 0, 0, 0, 0, 0, (-1/4), 0, 0, 0, (1/8), 0, (1/8), 0, 0, 0, 0, (1/4), 0, 0, 0, 0, -1, 0, 0]
def productColumn_03_21 : Fin 27 → ℝ := ![(1/8), 0, (-1/8), 0, (-1/16), (-1/16), 0, (1/16), 0, 0, (-1/16), 0, 0, 0, 0, 0, 0, 0, 0, 0, (1/16), (-1/16), 0, (1/16), 0, 0, (-1/16)]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_03_21 :
    jordan value3 value21 = decode productColumn_03_21 := by
  simp only [value3_decode, value21_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_03_21, column3, column21, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_03_21 :
    productColumn_03_21 = ∑ k : Fin 27, productCoeff_03_21 k • columns k := by
  funext r
  change productColumn_03_21 r = ∑ k : Fin 27, productCoeff_03_21 k * columns k r
  fin_cases r <;> norm_num [productColumn_03_21, productCoeff_03_21, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_03_21 :
    jordan (nativeWords 3) (nativeWords 21) =
      ∑ k : Fin 27, productCoeff_03_21 k • nativeWords k := by
  change jordan value3 value21 = _
  rw [native_product_decode_03_21, productColumn_sum_03_21, decode_sum_columns]

def productCoeff_03_22 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-3/2), 0, (-3/2), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def productColumn_03_22 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, 0, (-3/8), 0, 0, 0, 0, 0, 0, (3/8), 0, 0, (3/8), 0, 0, 0, 0, 0, (3/8), 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_03_22 :
    jordan value3 value22 = decode productColumn_03_22 := by
  simp only [value3_decode, value22_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_03_22, column3, column22, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_03_22 :
    productColumn_03_22 = ∑ k : Fin 27, productCoeff_03_22 k • columns k := by
  funext r
  change productColumn_03_22 r = ∑ k : Fin 27, productCoeff_03_22 k * columns k r
  fin_cases r <;> norm_num [productColumn_03_22, productCoeff_03_22, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_03_22 :
    jordan (nativeWords 3) (nativeWords 22) =
      ∑ k : Fin 27, productCoeff_03_22 k • nativeWords k := by
  change jordan value3 value22 = _
  rw [native_product_decode_03_22, productColumn_sum_03_22, decode_sum_columns]

def productCoeff_03_23 : Fin 27 → ℝ := ![0, 0, 0, (15/2), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def productColumn_03_23 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, (3/4), 0, (-3/4), 6, 0, 0, 0, (3/4), 0, -6, 0, 0, (3/4), 0, 0, 0, -6, 0, (3/4), (-3/4), 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_03_23 :
    jordan value3 value23 = decode productColumn_03_23 := by
  simp only [value3_decode, value23_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_03_23, column3, column23, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_03_23 :
    productColumn_03_23 = ∑ k : Fin 27, productCoeff_03_23 k • columns k := by
  funext r
  change productColumn_03_23 r = ∑ k : Fin 27, productCoeff_03_23 k * columns k r
  fin_cases r <;> norm_num [productColumn_03_23, productCoeff_03_23, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_03_23 :
    jordan (nativeWords 3) (nativeWords 23) =
      ∑ k : Fin 27, productCoeff_03_23 k • nativeWords k := by
  change jordan value3 value23 = _
  rw [native_product_decode_03_23, productColumn_sum_03_23, decode_sum_columns]

def productCoeff_03_24 : Fin 27 → ℝ := ![0, 0, (-5/24), 0, 0, 0, (-1/8), 0, 0, 0, (1/2), 0, 0, 0, 0, 0, 0, (1/24), 0, 0, 0, (-1/6), 0, 0, 0, (1/6), 0]
def productColumn_03_24 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, (1/16), 0, 0, 0, 0, 0, (-1/8), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (1/16), 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_03_24 :
    jordan value3 value24 = decode productColumn_03_24 := by
  simp only [value3_decode, value24_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_03_24, column3, column24, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_03_24 :
    productColumn_03_24 = ∑ k : Fin 27, productCoeff_03_24 k • columns k := by
  funext r
  change productColumn_03_24 r = ∑ k : Fin 27, productCoeff_03_24 k * columns k r
  fin_cases r <;> norm_num [productColumn_03_24, productCoeff_03_24, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_03_24 :
    jordan (nativeWords 3) (nativeWords 24) =
      ∑ k : Fin 27, productCoeff_03_24 k • nativeWords k := by
  change jordan value3 value24 = _
  rw [native_product_decode_03_24, productColumn_sum_03_24, decode_sum_columns]

def productCoeff_03_25 : Fin 27 → ℝ := ![0, (1/2), 0, 0, 0, 0, 0, 0, (-1/8), 0, 0, 0, (1/8), 0, (-1/4), 0, 0, 0, 0, (1/4), 0, 0, 0, 0, (1/2), 0, 0]
def productColumn_03_25 : Fin 27 → ℝ := ![(-1/4), 0, (1/4), 0, (-1/16), (1/16), 0, 0, 0, 0, (1/8), 0, 0, 0, (-1/16), 0, 0, (1/16), 0, 0, (1/16), (1/8), 0, 0, 0, 0, (1/16)]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_03_25 :
    jordan value3 value25 = decode productColumn_03_25 := by
  simp only [value3_decode, value25_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_03_25, column3, column25, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_03_25 :
    productColumn_03_25 = ∑ k : Fin 27, productCoeff_03_25 k • columns k := by
  funext r
  change productColumn_03_25 r = ∑ k : Fin 27, productCoeff_03_25 k * columns k r
  fin_cases r <;> norm_num [productColumn_03_25, productCoeff_03_25, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_03_25 :
    jordan (nativeWords 3) (nativeWords 25) =
      ∑ k : Fin 27, productCoeff_03_25 k • nativeWords k := by
  change jordan value3 value25 = _
  rw [native_product_decode_03_25, productColumn_sum_03_25, decode_sum_columns]

def productCoeff_03_26 : Fin 27 → ℝ := ![-1, 0, 0, 0, (3/2), 0, 0, (1/2), 0, 0, 0, 0, 0, -2, 0, (-5/2), 0, 0, (-3/4), 0, 0, 0, 0, 0, 0, 0, 0]
def productColumn_03_26 : Fin 27 → ℝ := ![0, 0, 0, 0, (1/8), (1/8), 0, (-1/2), 0, 0, 0, (-1/4), 0, 0, (5/8), 0, 0, (5/8), 0, 0, (1/8), 0, 0, (1/2), 0, 0, (-1/8)]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_03_26 :
    jordan value3 value26 = decode productColumn_03_26 := by
  simp only [value3_decode, value26_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_03_26, column3, column26, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_03_26 :
    productColumn_03_26 = ∑ k : Fin 27, productCoeff_03_26 k • columns k := by
  funext r
  change productColumn_03_26 r = ∑ k : Fin 27, productCoeff_03_26 k * columns k r
  fin_cases r <;> norm_num [productColumn_03_26, productCoeff_03_26, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_03_26 :
    jordan (nativeWords 3) (nativeWords 26) =
      ∑ k : Fin 27, productCoeff_03_26 k • nativeWords k := by
  change jordan value3 value26 = _
  rw [native_product_decode_03_26, productColumn_sum_03_26, decode_sum_columns]

end
end Glennie.Compact.NativeWordTableR01
