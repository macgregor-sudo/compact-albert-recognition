/- Concrete native Jordan product certificate for word row 12. -/
module
public import Glennie.Compact.NativeWordProductCommonR01

@[expose] public section
namespace Glennie.Compact.NativeWordTableR01
noncomputable section
open Glennie AlbertGeometry.NativeOperatorTrace
open scoped BigOperators Matrix
set_option autoImplicit false

def productCoeff_12_12 : Fin 27 → ℝ := ![-3, 0, 0, 0, (27/4), 0, 0, (7/4), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-3/2), 0, 0, 0, 0, 0, 0, 0, 0]
def productColumn_12_12 : Fin 27 → ℝ := ![(17/4), (1/2), (17/4), 0, 1, 0, 0, 0, 0, 0, 0, (1/4), 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_12_12 :
    jordan value12 value12 = decode productColumn_12_12 := by
  simp only [value12_decode, value12_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_12_12, column12, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_12_12 :
    productColumn_12_12 = ∑ k : Fin 27, productCoeff_12_12 k • columns k := by
  funext r
  change productColumn_12_12 r = ∑ k : Fin 27, productCoeff_12_12 k * columns k r
  fin_cases r <;> norm_num [productColumn_12_12, productCoeff_12_12, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_12_12 :
    jordan (nativeWords 12) (nativeWords 12) =
      ∑ k : Fin 27, productCoeff_12_12 k • nativeWords k := by
  change jordan value12 value12 = _
  rw [native_product_decode_12_12, productColumn_sum_12_12, decode_sum_columns]

def productCoeff_12_13 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, 0, 0, (7/8), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-3/4), 0, 0, 0, 0, 0, 0, 0]
def productColumn_12_13 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, (-1/4), 0, (-1/4), 0, 0, 0, 0, 0, 0, (-1/16), 0, 0, (1/16), 0, 0, 0, 0, 0, (-1/4), 0, 0, (-1/4)]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_12_13 :
    jordan value12 value13 = decode productColumn_12_13 := by
  simp only [value12_decode, value13_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_12_13, column12, column13, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_12_13 :
    productColumn_12_13 = ∑ k : Fin 27, productCoeff_12_13 k • columns k := by
  funext r
  change productColumn_12_13 r = ∑ k : Fin 27, productCoeff_12_13 k * columns k r
  fin_cases r <;> norm_num [productColumn_12_13, productCoeff_12_13, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_12_13 :
    jordan (nativeWords 12) (nativeWords 13) =
      ∑ k : Fin 27, productCoeff_12_13 k • nativeWords k := by
  change jordan value12 value13 = _
  rw [native_product_decode_12_13, productColumn_sum_12_13, decode_sum_columns]

def productCoeff_12_14 : Fin 27 → ℝ := ![(-13/3), 0, 0, 0, 8, 0, 0, (7/6), 0, (7/6), 0, 0, 0, (-1/6), 0, (-1/3), 0, 0, -1, 0, -1, 0, 0, (-1/12), 0, 0, 0]
def productColumn_12_14 : Fin 27 → ℝ := ![4, 0, 4, 0, (1/2), 0, 0, 0, 0, 0, (1/2), 0, 0, 0, (1/8), 0, 0, (1/8), 0, 0, (1/2), (-1/2), 0, 0, 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_12_14 :
    jordan value12 value14 = decode productColumn_12_14 := by
  simp only [value12_decode, value14_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_12_14, column12, column14, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_12_14 :
    productColumn_12_14 = ∑ k : Fin 27, productCoeff_12_14 k • columns k := by
  funext r
  change productColumn_12_14 r = ∑ k : Fin 27, productCoeff_12_14 k * columns k r
  fin_cases r <;> norm_num [productColumn_12_14, productCoeff_12_14, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_12_14 :
    jordan (nativeWords 12) (nativeWords 14) =
      ∑ k : Fin 27, productCoeff_12_14 k • nativeWords k := by
  change jordan value12 value14 = _
  rw [native_product_decode_12_14, productColumn_sum_12_14, decode_sum_columns]

def productCoeff_12_15 : Fin 27 → ℝ := ![0, (1/4), 0, 0, 0, 0, 0, 0, (1/8), 0, 0, 0, 0, 0, (-1/8), 0, 0, 0, 0, (-1/4), 0, 0, 0, 0, (5/2), 0, 0]
def productColumn_12_15 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, (5/16), 0, 0, 0, 0, (1/16), 0, 0, 0, (1/16), 0, 0, (-1/16), 0, 0, 0, (1/16), 0, 0, 0, 0, (5/16)]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_12_15 :
    jordan value12 value15 = decode productColumn_12_15 := by
  simp only [value12_decode, value15_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_12_15, column12, column15, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_12_15 :
    productColumn_12_15 = ∑ k : Fin 27, productCoeff_12_15 k • columns k := by
  funext r
  change productColumn_12_15 r = ∑ k : Fin 27, productCoeff_12_15 k * columns k r
  fin_cases r <;> norm_num [productColumn_12_15, productCoeff_12_15, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_12_15 :
    jordan (nativeWords 12) (nativeWords 15) =
      ∑ k : Fin 27, productCoeff_12_15 k • nativeWords k := by
  change jordan value12 value15 = _
  rw [native_product_decode_12_15, productColumn_sum_12_15, decode_sum_columns]

def productCoeff_12_16 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (3/2), 0, 0, 0, 3, 0]
def productColumn_12_16 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, (3/16), 0, (-3/8), (-9/16), 0, 0, 0, (-3/16), 0, 0, 0, 0, (3/16), 0, 0, 0, (-9/16), 0, (-3/8), (3/16), 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_12_16 :
    jordan value12 value16 = decode productColumn_12_16 := by
  simp only [value12_decode, value16_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_12_16, column12, column16, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_12_16 :
    productColumn_12_16 = ∑ k : Fin 27, productCoeff_12_16 k • columns k := by
  funext r
  change productColumn_12_16 r = ∑ k : Fin 27, productCoeff_12_16 k * columns k r
  fin_cases r <;> norm_num [productColumn_12_16, productCoeff_12_16, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_12_16 :
    jordan (nativeWords 12) (nativeWords 16) =
      ∑ k : Fin 27, productCoeff_12_16 k • nativeWords k := by
  change jordan value12 value16 = _
  rw [native_product_decode_12_16, productColumn_sum_12_16, decode_sum_columns]

def productCoeff_12_17 : Fin 27 → ℝ := ![0, 0, 0, (-1/4), 0, -3, 0, 0, 0, 0, 0, (3/2), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (1/2), 0, 0, 0, (5/2)]
def productColumn_12_17 : Fin 27 → ℝ := ![0, 0, 0, (-3/2), 0, 0, (-5/8), 0, (-1/2), (1/8), 0, 0, 0, (1/8), 0, (1/4), 0, 0, (1/8), (3/2), 0, 0, (-1/8), 0, (1/2), (5/8), 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_12_17 :
    jordan value12 value17 = decode productColumn_12_17 := by
  simp only [value12_decode, value17_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_12_17, column12, column17, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_12_17 :
    productColumn_12_17 = ∑ k : Fin 27, productCoeff_12_17 k • columns k := by
  funext r
  change productColumn_12_17 r = ∑ k : Fin 27, productCoeff_12_17 k * columns k r
  fin_cases r <;> norm_num [productColumn_12_17, productCoeff_12_17, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_12_17 :
    jordan (nativeWords 12) (nativeWords 17) =
      ∑ k : Fin 27, productCoeff_12_17 k • nativeWords k := by
  change jordan value12 value17 = _
  rw [native_product_decode_12_17, productColumn_sum_12_17, decode_sum_columns]

def productCoeff_12_18 : Fin 27 → ℝ := ![0, (-3/4), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (5/2), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def productColumn_12_18 : Fin 27 → ℝ := ![(-17/4), 0, (17/4), 0, (-5/4), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (5/4), 0, 0, 0, 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_12_18 :
    jordan value12 value18 = decode productColumn_12_18 := by
  simp only [value12_decode, value18_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_12_18, column12, column18, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_12_18 :
    productColumn_12_18 = ∑ k : Fin 27, productCoeff_12_18 k • columns k := by
  funext r
  change productColumn_12_18 r = ∑ k : Fin 27, productCoeff_12_18 k * columns k r
  fin_cases r <;> norm_num [productColumn_12_18, productCoeff_12_18, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_12_18 :
    jordan (nativeWords 12) (nativeWords 18) =
      ∑ k : Fin 27, productCoeff_12_18 k • nativeWords k := by
  change jordan value12 value18 = _
  rw [native_product_decode_12_18, productColumn_sum_12_18, decode_sum_columns]

def productCoeff_12_19 : Fin 27 → ℝ := ![(11/12), 0, 0, 0, -1, 0, 0, (-1/12), 0, (-11/24), 0, 0, 0, (13/12), 0, (-1/3), 0, 0, 0, 0, (1/2), 0, 0, (1/24), 0, 0, 0]
def productColumn_12_19 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, (3/8), 0, (1/4), 0, 0, (-1/8), 0, 0, 0, (1/16), 0, (1/8), (1/16), 0, 0, 0, (1/8), 0, (-1/4), 0, 0, (-3/8)]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_12_19 :
    jordan value12 value19 = decode productColumn_12_19 := by
  simp only [value12_decode, value19_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_12_19, column12, column19, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_12_19 :
    productColumn_12_19 = ∑ k : Fin 27, productCoeff_12_19 k • columns k := by
  funext r
  change productColumn_12_19 r = ∑ k : Fin 27, productCoeff_12_19 k * columns k r
  fin_cases r <;> norm_num [productColumn_12_19, productCoeff_12_19, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_12_19 :
    jordan (nativeWords 12) (nativeWords 19) =
      ∑ k : Fin 27, productCoeff_12_19 k • nativeWords k := by
  change jordan value12 value19 = _
  rw [native_product_decode_12_19, productColumn_sum_12_19, decode_sum_columns]

def productCoeff_12_20 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, 0, 0, (5/4), 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, (-3/2), 0, 0, 0, 0, 2, 0, 0]
def productColumn_12_20 : Fin 27 → ℝ := ![-4, 0, 4, 0, (-1/2), 0, 0, (-1/4), 0, 0, (-1/2), 0, 0, 0, (1/8), 0, 0, (-1/8), 0, 0, (1/2), (-1/2), 0, (-1/4), 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_12_20 :
    jordan value12 value20 = decode productColumn_12_20 := by
  simp only [value12_decode, value20_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_12_20, column12, column20, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_12_20 :
    productColumn_12_20 = ∑ k : Fin 27, productCoeff_12_20 k • columns k := by
  funext r
  change productColumn_12_20 r = ∑ k : Fin 27, productCoeff_12_20 k * columns k r
  fin_cases r <;> norm_num [productColumn_12_20, productCoeff_12_20, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_12_20 :
    jordan (nativeWords 12) (nativeWords 20) =
      ∑ k : Fin 27, productCoeff_12_20 k • nativeWords k := by
  change jordan value12 value20 = _
  rw [native_product_decode_12_20, productColumn_sum_12_20, decode_sum_columns]

def productCoeff_12_21 : Fin 27 → ℝ := ![0, 0, 0, (1/16), 0, (3/4), 0, 0, 0, 0, 0, (-3/8), 0, 0, 0, 0, (-1/8), 0, 0, 0, 0, 0, (-1/8), 0, 0, 0, (-1/4)]
def productColumn_12_21 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, (3/32), 0, 0, (-3/32), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (3/32), 0, 0, (-3/32), 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_12_21 :
    jordan value12 value21 = decode productColumn_12_21 := by
  simp only [value12_decode, value21_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_12_21, column12, column21, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_12_21 :
    productColumn_12_21 = ∑ k : Fin 27, productCoeff_12_21 k • columns k := by
  funext r
  change productColumn_12_21 r = ∑ k : Fin 27, productCoeff_12_21 k * columns k r
  fin_cases r <;> norm_num [productColumn_12_21, productCoeff_12_21, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_12_21 :
    jordan (nativeWords 12) (nativeWords 21) =
      ∑ k : Fin 27, productCoeff_12_21 k • nativeWords k := by
  change jordan value12 value21 = _
  rw [native_product_decode_12_21, productColumn_sum_12_21, decode_sum_columns]

def productCoeff_12_22 : Fin 27 → ℝ := ![0, 0, (-1/4), 0, 0, 0, (-3/4), 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, (-1/8), 0, 0, 0, (1/2), 0, 0, 0, (3/2), 0]
def productColumn_12_22 : Fin 27 → ℝ := ![0, 0, 0, 1, 0, 0, (1/16), 0, (-1/4), (1/16), 0, 0, (-1/2), 0, 0, 0, 0, 0, 0, 1, 0, 0, (1/16), 0, (-1/4), (1/16), 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_12_22 :
    jordan value12 value22 = decode productColumn_12_22 := by
  simp only [value12_decode, value22_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_12_22, column12, column22, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_12_22 :
    productColumn_12_22 = ∑ k : Fin 27, productCoeff_12_22 k • columns k := by
  funext r
  change productColumn_12_22 r = ∑ k : Fin 27, productCoeff_12_22 k * columns k r
  fin_cases r <;> norm_num [productColumn_12_22, productCoeff_12_22, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_12_22 :
    jordan (nativeWords 12) (nativeWords 22) =
      ∑ k : Fin 27, productCoeff_12_22 k • nativeWords k := by
  change jordan value12 value22 = _
  rw [native_product_decode_12_22, productColumn_sum_12_22, decode_sum_columns]

def productCoeff_12_23 : Fin 27 → ℝ := ![0, (-33/2), 0, 0, 0, 0, 0, 0, (3/4), 0, 0, 0, 9, 0, (15/4), 0, 0, 0, 0, (-3/2), 0, 0, 0, 0, -3, 0, 0]
def productColumn_12_23 : Fin 27 → ℝ := ![-9, 0, 9, 0, (-9/2), (-3/8), 0, 0, 0, 0, (-15/8), 0, 0, 0, (3/8), 0, 0, (-3/8), 0, 0, (9/2), (-15/8), 0, 0, 0, 0, (-3/8)]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_12_23 :
    jordan value12 value23 = decode productColumn_12_23 := by
  simp only [value12_decode, value23_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_12_23, column12, column23, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_12_23 :
    productColumn_12_23 = ∑ k : Fin 27, productCoeff_12_23 k • columns k := by
  funext r
  change productColumn_12_23 r = ∑ k : Fin 27, productCoeff_12_23 k * columns k r
  fin_cases r <;> norm_num [productColumn_12_23, productCoeff_12_23, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_12_23 :
    jordan (nativeWords 12) (nativeWords 23) =
      ∑ k : Fin 27, productCoeff_12_23 k • nativeWords k := by
  change jordan value12 value23 = _
  rw [native_product_decode_12_23, productColumn_sum_12_23, decode_sum_columns]

def productCoeff_12_24 : Fin 27 → ℝ := ![(-1/4), 0, 0, 0, 0, 0, 0, (1/8), 0, (1/8), 0, 0, 0, (-1/8), 0, (1/4), 0, 0, 0, 0, 0, 0, 0, (-1/16), 0, 0, 0]
def productColumn_12_24 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, (-1/8), 0, 0, 0, 0, 0, 0, 0, 0, (-1/32), 0, 0, (-1/32), 0, 0, 0, 0, 0, 0, 0, 0, (1/8)]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_12_24 :
    jordan value12 value24 = decode productColumn_12_24 := by
  simp only [value12_decode, value24_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_12_24, column12, column24, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_12_24 :
    productColumn_12_24 = ∑ k : Fin 27, productCoeff_12_24 k • columns k := by
  funext r
  change productColumn_12_24 r = ∑ k : Fin 27, productCoeff_12_24 k * columns k r
  fin_cases r <;> norm_num [productColumn_12_24, productCoeff_12_24, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_12_24 :
    jordan (nativeWords 12) (nativeWords 24) =
      ∑ k : Fin 27, productCoeff_12_24 k • nativeWords k := by
  change jordan value12 value24 = _
  rw [native_product_decode_12_24, productColumn_sum_12_24, decode_sum_columns]

def productCoeff_12_25 : Fin 27 → ℝ := ![0, 0, 0, (-1/8), 0, (-3/4), 0, 0, 0, 0, 0, (3/4), 0, 0, 0, 0, (3/8), 0, 0, 0, 0, 0, (1/4), 0, 0, 0, (1/8)]
def productColumn_12_25 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, (-1/8), 0, (1/8), (1/4), 0, 0, 0, (-1/32), 0, (-1/16), 0, 0, (-1/32), 0, 0, 0, (-1/4), 0, (-1/8), (1/8), 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_12_25 :
    jordan value12 value25 = decode productColumn_12_25 := by
  simp only [value12_decode, value25_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_12_25, column12, column25, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_12_25 :
    productColumn_12_25 = ∑ k : Fin 27, productCoeff_12_25 k • columns k := by
  funext r
  change productColumn_12_25 r = ∑ k : Fin 27, productCoeff_12_25 k * columns k r
  fin_cases r <;> norm_num [productColumn_12_25, productCoeff_12_25, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_12_25 :
    jordan (nativeWords 12) (nativeWords 25) =
      ∑ k : Fin 27, productCoeff_12_25 k • nativeWords k := by
  change jordan value12 value25 = _
  rw [native_product_decode_12_25, productColumn_sum_12_25, decode_sum_columns]

def productCoeff_12_26 : Fin 27 → ℝ := ![0, 0, (-5/4), 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, (3/8), 0, 0, 0, -1, 0, 0, 0, (-1/2), 0]
def productColumn_12_26 : Fin 27 → ℝ := ![0, 0, 0, 1, 0, 0, (1/4), 0, (1/4), 0, 0, 0, (-1/2), (-1/16), 0, 0, 0, 0, (1/16), 1, 0, 0, 0, 0, (1/4), (1/4), 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_12_26 :
    jordan value12 value26 = decode productColumn_12_26 := by
  simp only [value12_decode, value26_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_12_26, column12, column26, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_12_26 :
    productColumn_12_26 = ∑ k : Fin 27, productCoeff_12_26 k • columns k := by
  funext r
  change productColumn_12_26 r = ∑ k : Fin 27, productCoeff_12_26 k * columns k r
  fin_cases r <;> norm_num [productColumn_12_26, productCoeff_12_26, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_12_26 :
    jordan (nativeWords 12) (nativeWords 26) =
      ∑ k : Fin 27, productCoeff_12_26 k • nativeWords k := by
  change jordan value12 value26 = _
  rw [native_product_decode_12_26, productColumn_sum_12_26, decode_sum_columns]

end
end Glennie.Compact.NativeWordTableR01
