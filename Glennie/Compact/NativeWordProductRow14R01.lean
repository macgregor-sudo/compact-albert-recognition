/- Concrete native Jordan product certificate for word row 14. -/
module
public import Glennie.Compact.NativeWordProductCommonR01

@[expose] public section
namespace Glennie.Compact.NativeWordTableR01
noncomputable section
open Glennie AlbertGeometry.NativeOperatorTrace
open scoped BigOperators Matrix
set_option autoImplicit false

def productCoeff_14_14 : Fin 27 → ℝ := ![-3, 0, 0, 0, (27/4), 0, 0, 0, 0, (7/4), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-3/2), 0, 0, 0, 0, 0, 0]
def productColumn_14_14 : Fin 27 → ℝ := ![(17/4), (1/2), (17/4), 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, (1/4), 0, 0, 0, 0, -1, 0, 0, 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_14_14 :
    jordan value14 value14 = decode productColumn_14_14 := by
  simp only [value14_decode, value14_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_14_14, column14, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_14_14 :
    productColumn_14_14 = ∑ k : Fin 27, productCoeff_14_14 k • columns k := by
  funext r
  change productColumn_14_14 r = ∑ k : Fin 27, productCoeff_14_14 k * columns k r
  fin_cases r <;> norm_num [productColumn_14_14, productCoeff_14_14, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_14_14 :
    jordan (nativeWords 14) (nativeWords 14) =
      ∑ k : Fin 27, productCoeff_14_14 k • nativeWords k := by
  change jordan value14 value14 = _
  rw [native_product_decode_14_14, productColumn_sum_14_14, decode_sum_columns]

def productCoeff_14_15 : Fin 27 → ℝ := ![0, (1/4), 0, 0, 0, 0, 0, 0, (1/4), 0, 0, 0, (-1/8), 0, 0, 0, 0, 0, 0, (-1/4), 0, 0, 0, 0, (5/2), 0, 0]
def productColumn_14_15 : Fin 27 → ℝ := ![0, 0, 0, 0, (1/16), (1/4), 0, (-1/16), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1/16), 0, 0, (-1/16), 0, 0, (1/4)]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_14_15 :
    jordan value14 value15 = decode productColumn_14_15 := by
  simp only [value14_decode, value15_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_14_15, column14, column15, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_14_15 :
    productColumn_14_15 = ∑ k : Fin 27, productCoeff_14_15 k • columns k := by
  funext r
  change productColumn_14_15 r = ∑ k : Fin 27, productCoeff_14_15 k * columns k r
  fin_cases r <;> norm_num [productColumn_14_15, productCoeff_14_15, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_14_15 :
    jordan (nativeWords 14) (nativeWords 15) =
      ∑ k : Fin 27, productCoeff_14_15 k • nativeWords k := by
  change jordan value14 value15 = _
  rw [native_product_decode_14_15, productColumn_sum_14_15, decode_sum_columns]

def productCoeff_14_16 : Fin 27 → ℝ := ![0, 0, (-1/8), 0, 0, 0, (-3/8), 0, 0, 0, (3/4), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (1/2), 0, 0, 0, (5/2), 0]
def productColumn_14_16 : Fin 27 → ℝ := ![0, 0, 0, (1/16), 0, 0, (1/4), 0, (-5/16), (-3/8), 0, 0, (-1/8), (-1/16), 0, 0, 0, 0, (1/16), (1/16), 0, 0, (-3/8), 0, (-5/16), (1/4), 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_14_16 :
    jordan value14 value16 = decode productColumn_14_16 := by
  simp only [value14_decode, value16_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_14_16, column14, column16, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_14_16 :
    productColumn_14_16 = ∑ k : Fin 27, productCoeff_14_16 k • columns k := by
  funext r
  change productColumn_14_16 r = ∑ k : Fin 27, productCoeff_14_16 k * columns k r
  fin_cases r <;> norm_num [productColumn_14_16, productCoeff_14_16, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_14_16 :
    jordan (nativeWords 14) (nativeWords 16) =
      ∑ k : Fin 27, productCoeff_14_16 k • nativeWords k := by
  change jordan value14 value16 = _
  rw [native_product_decode_14_16, productColumn_sum_14_16, decode_sum_columns]

def productCoeff_14_17 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, (27/4), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-3/2), 0, 0, 0, 0]
def productColumn_14_17 : Fin 27 → ℝ := ![0, 0, 0, (-15/8), 0, 0, 0, 0, (-3/8), 0, 0, 0, 0, (-3/8), 0, 0, 0, 0, (-3/8), (15/8), 0, 0, 0, 0, (3/8), 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_14_17 :
    jordan value14 value17 = decode productColumn_14_17 := by
  simp only [value14_decode, value17_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_14_17, column14, column17, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_14_17 :
    productColumn_14_17 = ∑ k : Fin 27, productCoeff_14_17 k • columns k := by
  funext r
  change productColumn_14_17 r = ∑ k : Fin 27, productCoeff_14_17 k * columns k r
  fin_cases r <;> norm_num [productColumn_14_17, productCoeff_14_17, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_14_17 :
    jordan (nativeWords 14) (nativeWords 17) =
      ∑ k : Fin 27, productCoeff_14_17 k • nativeWords k := by
  change jordan value14 value17 = _
  rw [native_product_decode_14_17, productColumn_sum_14_17, decode_sum_columns]

def productCoeff_14_18 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, 0, 0, (-1/4), 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, (1/2), 0, 0, 0, 0, 2, 0, 0]
def productColumn_14_18 : Fin 27 → ℝ := ![-4, 0, 4, 0, (-1/2), (1/4), 0, 0, 0, 0, (-1/2), 0, 0, 0, (-1/8), 0, 0, (1/8), 0, 0, (1/2), (-1/2), 0, 0, 0, 0, (1/4)]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_14_18 :
    jordan value14 value18 = decode productColumn_14_18 := by
  simp only [value14_decode, value18_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_14_18, column14, column18, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_14_18 :
    productColumn_14_18 = ∑ k : Fin 27, productCoeff_14_18 k • columns k := by
  funext r
  change productColumn_14_18 r = ∑ k : Fin 27, productCoeff_14_18 k * columns k r
  fin_cases r <;> norm_num [productColumn_14_18, productCoeff_14_18, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_14_18 :
    jordan (nativeWords 14) (nativeWords 18) =
      ∑ k : Fin 27, productCoeff_14_18 k • nativeWords k := by
  change jordan value14 value18 = _
  rw [native_product_decode_14_18, productColumn_sum_14_18, decode_sum_columns]

def productCoeff_14_19 : Fin 27 → ℝ := ![(-11/12), 0, 0, 0, 1, 0, 0, (11/24), 0, (1/12), 0, 0, 0, (17/12), 0, (1/3), 0, 0, (-1/2), 0, 0, 0, 0, (-1/24), 0, 0, 0]
def productColumn_14_19 : Fin 27 → ℝ := ![0, 0, 0, 0, (1/8), (1/4), 0, (3/8), 0, 0, 0, (-1/8), 0, 0, (-1/16), 0, 0, (-1/16), 0, 0, (1/8), 0, 0, (-3/8), 0, 0, (-1/4)]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_14_19 :
    jordan value14 value19 = decode productColumn_14_19 := by
  simp only [value14_decode, value19_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_14_19, column14, column19, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_14_19 :
    productColumn_14_19 = ∑ k : Fin 27, productCoeff_14_19 k • columns k := by
  funext r
  change productColumn_14_19 r = ∑ k : Fin 27, productCoeff_14_19 k * columns k r
  fin_cases r <;> norm_num [productColumn_14_19, productCoeff_14_19, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_14_19 :
    jordan (nativeWords 14) (nativeWords 19) =
      ∑ k : Fin 27, productCoeff_14_19 k • nativeWords k := by
  change jordan value14 value19 = _
  rw [native_product_decode_14_19, productColumn_sum_14_19, decode_sum_columns]

def productCoeff_14_20 : Fin 27 → ℝ := ![0, (-3/4), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (5/2), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def productColumn_14_20 : Fin 27 → ℝ := ![(-17/4), 0, (17/4), 0, 0, 0, 0, 0, 0, 0, (-5/4), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-5/4), 0, 0, 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_14_20 :
    jordan value14 value20 = decode productColumn_14_20 := by
  simp only [value14_decode, value20_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_14_20, column14, column20, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_14_20 :
    productColumn_14_20 = ∑ k : Fin 27, productCoeff_14_20 k • columns k := by
  funext r
  change productColumn_14_20 r = ∑ k : Fin 27, productCoeff_14_20 k * columns k r
  fin_cases r <;> norm_num [productColumn_14_20, productCoeff_14_20, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_14_20 :
    jordan (nativeWords 14) (nativeWords 20) =
      ∑ k : Fin 27, productCoeff_14_20 k • nativeWords k := by
  change jordan value14 value20 = _
  rw [native_product_decode_14_20, productColumn_sum_14_20, decode_sum_columns]

def productCoeff_14_21 : Fin 27 → ℝ := ![0, 0, 0, (1/8), 0, (15/16), 0, 0, 0, 0, 0, (-3/4), 0, 0, 0, 0, (-1/8), 0, 0, 0, 0, 0, (-1/8), 0, 0, 0, (-3/8)]
def productColumn_14_21 : Fin 27 → ℝ := ![0, 0, 0, (1/32), 0, 0, (1/8), 0, (1/32), (-1/8), 0, 0, 0, 0, 0, (-1/16), 0, 0, 0, (-1/32), 0, 0, (1/8), 0, (-1/32), (-1/8), 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_14_21 :
    jordan value14 value21 = decode productColumn_14_21 := by
  simp only [value14_decode, value21_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_14_21, column14, column21, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_14_21 :
    productColumn_14_21 = ∑ k : Fin 27, productCoeff_14_21 k • columns k := by
  funext r
  change productColumn_14_21 r = ∑ k : Fin 27, productCoeff_14_21 k * columns k r
  fin_cases r <;> norm_num [productColumn_14_21, productCoeff_14_21, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_14_21 :
    jordan (nativeWords 14) (nativeWords 21) =
      ∑ k : Fin 27, productCoeff_14_21 k • nativeWords k := by
  change jordan value14 value21 = _
  rw [native_product_decode_14_21, productColumn_sum_14_21, decode_sum_columns]

def productCoeff_14_22 : Fin 27 → ℝ := ![0, 0, (1/2), 0, 0, 0, (-3/8), 0, 0, 0, (15/4), 0, 0, 0, 0, 0, 0, (-1/4), 0, 0, 0, (-1/2), 0, 0, 0, (1/2), 0]
def productColumn_14_22 : Fin 27 → ℝ := ![0, 0, 0, (15/16), 0, 0, 0, 0, (-3/16), 0, 0, 0, 0, (3/16), 0, 0, 0, 0, (-3/16), (15/16), 0, 0, 0, 0, (-3/16), 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_14_22 :
    jordan value14 value22 = decode productColumn_14_22 := by
  simp only [value14_decode, value22_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_14_22, column14, column22, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_14_22 :
    productColumn_14_22 = ∑ k : Fin 27, productCoeff_14_22 k • columns k := by
  funext r
  change productColumn_14_22 r = ∑ k : Fin 27, productCoeff_14_22 k * columns k r
  fin_cases r <;> norm_num [productColumn_14_22, productCoeff_14_22, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_14_22 :
    jordan (nativeWords 14) (nativeWords 22) =
      ∑ k : Fin 27, productCoeff_14_22 k • nativeWords k := by
  change jordan value14 value22 = _
  rw [native_product_decode_14_22, productColumn_sum_14_22, decode_sum_columns]

def productCoeff_14_23 : Fin 27 → ℝ := ![0, (-33/2), 0, 0, 0, 0, 0, 0, (-9/4), 0, 0, 0, (15/4), 0, 9, 0, 0, 0, 0, 3, 0, 0, 0, 0, -3, 0, 0]
def productColumn_14_23 : Fin 27 → ℝ := ![-9, 0, 9, 0, (-15/8), 0, 0, (3/8), 0, 0, (-9/2), 0, 0, 0, (-3/8), 0, 0, (3/8), 0, 0, (15/8), (-9/2), 0, (3/8), 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_14_23 :
    jordan value14 value23 = decode productColumn_14_23 := by
  simp only [value14_decode, value23_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_14_23, column14, column23, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_14_23 :
    productColumn_14_23 = ∑ k : Fin 27, productCoeff_14_23 k • columns k := by
  funext r
  change productColumn_14_23 r = ∑ k : Fin 27, productCoeff_14_23 k * columns k r
  fin_cases r <;> norm_num [productColumn_14_23, productCoeff_14_23, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_14_23 :
    jordan (nativeWords 14) (nativeWords 23) =
      ∑ k : Fin 27, productCoeff_14_23 k • nativeWords k := by
  change jordan value14 value23 = _
  rw [native_product_decode_14_23, productColumn_sum_14_23, decode_sum_columns]

def productCoeff_14_24 : Fin 27 → ℝ := ![(-5/24), 0, 0, 0, (-1/4), 0, 0, (5/48), 0, (1/6), 0, 0, 0, (-1/6), 0, (1/6), 0, 0, (1/8), 0, 0, 0, 0, (-1/12), 0, 0, 0]
def productColumn_14_24 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, (-1/8), 0, 0, 0, 0, 0, (1/16), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (1/8)]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_14_24 :
    jordan value14 value24 = decode productColumn_14_24 := by
  simp only [value14_decode, value24_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_14_24, column14, column24, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_14_24 :
    productColumn_14_24 = ∑ k : Fin 27, productCoeff_14_24 k • columns k := by
  funext r
  change productColumn_14_24 r = ∑ k : Fin 27, productCoeff_14_24 k * columns k r
  fin_cases r <;> norm_num [productColumn_14_24, productCoeff_14_24, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_14_24 :
    jordan (nativeWords 14) (nativeWords 24) =
      ∑ k : Fin 27, productCoeff_14_24 k • nativeWords k := by
  change jordan value14 value24 = _
  rw [native_product_decode_14_24, productColumn_sum_14_24, decode_sum_columns]

def productCoeff_14_25 : Fin 27 → ℝ := ![0, 0, 0, (-5/16), 0, (-3/4), 0, 0, 0, 0, 0, (3/2), 0, 0, 0, 0, (3/8), 0, 0, 0, 0, 0, (1/4), 0, 0, 0, (1/8)]
def productColumn_14_25 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, (-1/8), 0, (1/8), (1/4), 0, 0, 0, (-1/32), 0, (1/8), 0, 0, (-1/32), 0, 0, 0, (-1/4), 0, (-1/8), (1/8), 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_14_25 :
    jordan value14 value25 = decode productColumn_14_25 := by
  simp only [value14_decode, value25_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_14_25, column14, column25, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_14_25 :
    productColumn_14_25 = ∑ k : Fin 27, productCoeff_14_25 k • columns k := by
  funext r
  change productColumn_14_25 r = ∑ k : Fin 27, productCoeff_14_25 k * columns k r
  fin_cases r <;> norm_num [productColumn_14_25, productCoeff_14_25, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_14_25 :
    jordan (nativeWords 14) (nativeWords 25) =
      ∑ k : Fin 27, productCoeff_14_25 k • nativeWords k := by
  change jordan value14 value25 = _
  rw [native_product_decode_14_25, productColumn_sum_14_25, decode_sum_columns]

def productCoeff_14_26 : Fin 27 → ℝ := ![0, 0, (-3/8), 0, 0, 0, 0, 0, 0, 0, (9/2), 0, 0, 0, 0, 0, 0, (1/8), 0, 0, 0, -3, 0, 0, 0, (-3/2), 0]
def productColumn_14_26 : Fin 27 → ℝ := ![0, 0, 0, 1, 0, 0, (1/4), 0, (1/4), 0, 0, 0, (-1/8), (5/16), 0, 0, 0, 0, (-5/16), 1, 0, 0, 0, 0, (1/4), (1/4), 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_14_26 :
    jordan value14 value26 = decode productColumn_14_26 := by
  simp only [value14_decode, value26_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_14_26, column14, column26, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_14_26 :
    productColumn_14_26 = ∑ k : Fin 27, productCoeff_14_26 k • columns k := by
  funext r
  change productColumn_14_26 r = ∑ k : Fin 27, productCoeff_14_26 k * columns k r
  fin_cases r <;> norm_num [productColumn_14_26, productCoeff_14_26, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_14_26 :
    jordan (nativeWords 14) (nativeWords 26) =
      ∑ k : Fin 27, productCoeff_14_26 k • nativeWords k := by
  change jordan value14 value26 = _
  rw [native_product_decode_14_26, productColumn_sum_14_26, decode_sum_columns]

end
end Glennie.Compact.NativeWordTableR01
