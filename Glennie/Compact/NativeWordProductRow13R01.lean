/- Concrete native Jordan product certificate for word row 13. -/
module
public import Glennie.Compact.NativeWordProductCommonR01

@[expose] public section
namespace Glennie.Compact.NativeWordTableR01
noncomputable section
open Glennie AlbertGeometry.NativeOperatorTrace
open scoped BigOperators Matrix
set_option autoImplicit false

def productCoeff_13_13 : Fin 27 → ℝ := ![(2/3), 0, 0, 0, (-5/8), 0, 0, (-7/48), 0, (-7/48), 0, 0, 0, (1/12), 0, (1/6), 0, 0, (1/8), 0, (1/8), 0, 0, (1/24), 0, 0, 0]
def productColumn_13_13 : Fin 27 → ℝ := ![(1/8), (1/4), (1/8), 0, 0, 0, 0, 0, 0, 0, 0, (1/16), 0, 0, (-1/16), 0, (1/16), (-1/16), 0, 0, 0, 0, 0, 0, 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_13_13 :
    jordan value13 value13 = decode productColumn_13_13 := by
  simp only [value13_decode, value13_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_13_13, column13, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_13_13 :
    productColumn_13_13 = ∑ k : Fin 27, productCoeff_13_13 k • columns k := by
  funext r
  change productColumn_13_13 r = ∑ k : Fin 27, productCoeff_13_13 k * columns k r
  fin_cases r <;> norm_num [productColumn_13_13, productCoeff_13_13, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_13_13 :
    jordan (nativeWords 13) (nativeWords 13) =
      ∑ k : Fin 27, productCoeff_13_13 k • nativeWords k := by
  change jordan value13 value13 = _
  rw [native_product_decode_13_13, productColumn_sum_13_13, decode_sum_columns]

def productCoeff_13_14 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, 0, 0, (7/8), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-3/4), 0, 0, 0, 0, 0, 0, 0]
def productColumn_13_14 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, (-1/4), 0, (-1/4), 0, 0, 0, 0, 0, 0, (-1/16), 0, 0, (1/16), 0, 0, 0, 0, 0, (-1/4), 0, 0, (-1/4)]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_13_14 :
    jordan value13 value14 = decode productColumn_13_14 := by
  simp only [value13_decode, value14_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_13_14, column13, column14, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_13_14 :
    productColumn_13_14 = ∑ k : Fin 27, productCoeff_13_14 k • columns k := by
  funext r
  change productColumn_13_14 r = ∑ k : Fin 27, productCoeff_13_14 k * columns k r
  fin_cases r <;> norm_num [productColumn_13_14, productCoeff_13_14, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_13_14 :
    jordan (nativeWords 13) (nativeWords 14) =
      ∑ k : Fin 27, productCoeff_13_14 k • nativeWords k := by
  change jordan value13 value14 = _
  rw [native_product_decode_13_14, productColumn_sum_13_14, decode_sum_columns]

def productCoeff_13_15 : Fin 27 → ℝ := ![(-1/3), 0, 0, 0, (5/16), 0, 0, (5/48), 0, (1/24), 0, 0, 0, (1/12), 0, (-1/12), 0, 0, (-1/16), 0, (-1/16), 0, 0, (-1/48), 0, 0, 0]
def productColumn_13_15 : Fin 27 → ℝ := ![(-1/16), (-1/8), (-1/16), 0, (1/32), (1/32), 0, (1/32), 0, 0, (-1/32), 0, 0, 0, (1/32), 0, (-1/16), (1/32), 0, 0, (1/32), (1/32), 0, (-1/32), 0, 0, (-1/32)]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_13_15 :
    jordan value13 value15 = decode productColumn_13_15 := by
  simp only [value13_decode, value15_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_13_15, column13, column15, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_13_15 :
    productColumn_13_15 = ∑ k : Fin 27, productCoeff_13_15 k • columns k := by
  funext r
  change productColumn_13_15 r = ∑ k : Fin 27, productCoeff_13_15 k * columns k r
  fin_cases r <;> norm_num [productColumn_13_15, productCoeff_13_15, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_13_15 :
    jordan (nativeWords 13) (nativeWords 15) =
      ∑ k : Fin 27, productCoeff_13_15 k • nativeWords k := by
  change jordan value13 value15 = _
  rw [native_product_decode_13_15, productColumn_sum_13_15, decode_sum_columns]

def productCoeff_13_16 : Fin 27 → ℝ := ![0, 0, 0, (1/16), 0, (-15/16), 0, 0, 0, 0, 0, (-3/8), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (1/4), 0, 0, 0, (1/8)]
def productColumn_13_16 : Fin 27 → ℝ := ![0, 0, 0, (3/32), 0, 0, (-1/32), 0, (1/32), (-1/32), 0, 0, 0, (1/16), 0, (-1/16), 0, 0, (1/16), (-3/32), 0, 0, (1/32), 0, (-1/32), (1/32), 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_13_16 :
    jordan value13 value16 = decode productColumn_13_16 := by
  simp only [value13_decode, value16_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_13_16, column13, column16, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_13_16 :
    productColumn_13_16 = ∑ k : Fin 27, productCoeff_13_16 k • columns k := by
  funext r
  change productColumn_13_16 r = ∑ k : Fin 27, productCoeff_13_16 k * columns k r
  fin_cases r <;> norm_num [productColumn_13_16, productCoeff_13_16, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_13_16 :
    jordan (nativeWords 13) (nativeWords 16) =
      ∑ k : Fin 27, productCoeff_13_16 k • nativeWords k := by
  change jordan value13 value16 = _
  rw [native_product_decode_13_16, productColumn_sum_13_16, decode_sum_columns]

def productCoeff_13_17 : Fin 27 → ℝ := ![0, 0, (1/8), 0, 0, 0, (3/8), 0, 0, 0, (-3/4), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, (-5/2), 0]
def productColumn_13_17 : Fin 27 → ℝ := ![0, 0, 0, (-1/16), 0, 0, (-1/16), 0, (5/16), (3/16), 0, 0, (1/8), (1/4), 0, 0, 0, 0, (-1/4), (-1/16), 0, 0, (3/16), 0, (5/16), (-1/16), 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_13_17 :
    jordan value13 value17 = decode productColumn_13_17 := by
  simp only [value13_decode, value17_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_13_17, column13, column17, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_13_17 :
    productColumn_13_17 = ∑ k : Fin 27, productCoeff_13_17 k • columns k := by
  funext r
  change productColumn_13_17 r = ∑ k : Fin 27, productCoeff_13_17 k * columns k r
  fin_cases r <;> norm_num [productColumn_13_17, productCoeff_13_17, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_13_17 :
    jordan (nativeWords 13) (nativeWords 17) =
      ∑ k : Fin 27, productCoeff_13_17 k • nativeWords k := by
  change jordan value13 value17 = _
  rw [native_product_decode_13_17, productColumn_sum_13_17, decode_sum_columns]

def productCoeff_13_18 : Fin 27 → ℝ := ![(-11/12), 0, 0, 0, 1, 0, 0, (1/12), 0, (11/24), 0, 0, 0, (17/12), 0, (1/3), 0, 0, 0, 0, (-1/2), 0, 0, (-1/24), 0, 0, 0]
def productColumn_13_18 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, (1/4), 0, (3/8), 0, 0, (1/8), 0, 0, 0, (-1/16), 0, (-1/8), (-1/16), 0, 0, 0, (-1/8), 0, (-3/8), 0, 0, (-1/4)]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_13_18 :
    jordan value13 value18 = decode productColumn_13_18 := by
  simp only [value13_decode, value18_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_13_18, column13, column18, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_13_18 :
    productColumn_13_18 = ∑ k : Fin 27, productCoeff_13_18 k • columns k := by
  funext r
  change productColumn_13_18 r = ∑ k : Fin 27, productCoeff_13_18 k * columns k r
  fin_cases r <;> norm_num [productColumn_13_18, productCoeff_13_18, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_13_18 :
    jordan (nativeWords 13) (nativeWords 18) =
      ∑ k : Fin 27, productCoeff_13_18 k • nativeWords k := by
  change jordan value13 value18 = _
  rw [native_product_decode_13_18, productColumn_sum_13_18, decode_sum_columns]

def productCoeff_13_19 : Fin 27 → ℝ := ![0, (-3/8), 0, 0, 0, 0, 0, 0, (-1/4), 0, 0, 0, (1/8), 0, (1/8), 0, 0, 0, 0, (1/4), 0, 0, 0, 0, -1, 0, 0]
def productColumn_13_19 : Fin 27 → ℝ := ![(-1/8), 0, (1/8), 0, (-1/16), (-1/16), 0, (1/16), 0, 0, (-1/16), 0, 0, 0, 0, 0, 0, 0, 0, 0, (1/16), (-1/16), 0, (1/16), 0, 0, (-1/16)]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_13_19 :
    jordan value13 value19 = decode productColumn_13_19 := by
  simp only [value13_decode, value19_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_13_19, column13, column19, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_13_19 :
    productColumn_13_19 = ∑ k : Fin 27, productCoeff_13_19 k • columns k := by
  funext r
  change productColumn_13_19 r = ∑ k : Fin 27, productCoeff_13_19 k * columns k r
  fin_cases r <;> norm_num [productColumn_13_19, productCoeff_13_19, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_13_19 :
    jordan (nativeWords 13) (nativeWords 19) =
      ∑ k : Fin 27, productCoeff_13_19 k • nativeWords k := by
  change jordan value13 value19 = _
  rw [native_product_decode_13_19, productColumn_sum_13_19, decode_sum_columns]

def productCoeff_13_20 : Fin 27 → ℝ := ![(11/12), 0, 0, 0, -1, 0, 0, (-11/24), 0, (-1/12), 0, 0, 0, (13/12), 0, (-1/3), 0, 0, (1/2), 0, 0, 0, 0, (1/24), 0, 0, 0]
def productColumn_13_20 : Fin 27 → ℝ := ![0, 0, 0, 0, (-1/8), (3/8), 0, (1/4), 0, 0, 0, (1/8), 0, 0, (1/16), 0, 0, (1/16), 0, 0, (-1/8), 0, 0, (-1/4), 0, 0, (-3/8)]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_13_20 :
    jordan value13 value20 = decode productColumn_13_20 := by
  simp only [value13_decode, value20_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_13_20, column13, column20, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_13_20 :
    productColumn_13_20 = ∑ k : Fin 27, productCoeff_13_20 k • columns k := by
  funext r
  change productColumn_13_20 r = ∑ k : Fin 27, productCoeff_13_20 k * columns k r
  fin_cases r <;> norm_num [productColumn_13_20, productCoeff_13_20, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_13_20 :
    jordan (nativeWords 13) (nativeWords 20) =
      ∑ k : Fin 27, productCoeff_13_20 k • nativeWords k := by
  change jordan value13 value20 = _
  rw [native_product_decode_13_20, productColumn_sum_13_20, decode_sum_columns]

def productCoeff_13_21 : Fin 27 → ℝ := ![0, 0, (1/32), 0, 0, 0, (3/32), 0, 0, 0, (-3/16), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1/8), 0]
def productColumn_13_21 : Fin 27 → ℝ := ![0, 0, 0, (-1/64), 0, 0, (-1/64), 0, (1/64), (-1/64), 0, 0, (1/32), 0, 0, 0, 0, 0, 0, (-1/64), 0, 0, (-1/64), 0, (1/64), (-1/64), 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_13_21 :
    jordan value13 value21 = decode productColumn_13_21 := by
  simp only [value13_decode, value21_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_13_21, column13, column21, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_13_21 :
    productColumn_13_21 = ∑ k : Fin 27, productCoeff_13_21 k • columns k := by
  funext r
  change productColumn_13_21 r = ∑ k : Fin 27, productCoeff_13_21 k * columns k r
  fin_cases r <;> norm_num [productColumn_13_21, productCoeff_13_21, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_13_21 :
    jordan (nativeWords 13) (nativeWords 21) =
      ∑ k : Fin 27, productCoeff_13_21 k • nativeWords k := by
  change jordan value13 value21 = _
  rw [native_product_decode_13_21, productColumn_sum_13_21, decode_sum_columns]

def productCoeff_13_22 : Fin 27 → ℝ := ![0, 0, 0, (-3/16), 0, (-15/16), 0, 0, 0, 0, 0, (9/8), 0, 0, 0, 0, (-1/8), 0, 0, 0, 0, 0, (1/4), 0, 0, 0, (1/4)]
def productColumn_13_22 : Fin 27 → ℝ := ![0, 0, 0, (-1/32), 0, 0, (-1/32), 0, (-1/32), (1/32), 0, 0, 0, (3/32), 0, (1/4), 0, 0, (3/32), (1/32), 0, 0, (-1/32), 0, (1/32), (1/32), 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_13_22 :
    jordan value13 value22 = decode productColumn_13_22 := by
  simp only [value13_decode, value22_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_13_22, column13, column22, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_13_22 :
    productColumn_13_22 = ∑ k : Fin 27, productCoeff_13_22 k • columns k := by
  funext r
  change productColumn_13_22 r = ∑ k : Fin 27, productCoeff_13_22 k * columns k r
  fin_cases r <;> norm_num [productColumn_13_22, productCoeff_13_22, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_13_22 :
    jordan (nativeWords 13) (nativeWords 22) =
      ∑ k : Fin 27, productCoeff_13_22 k • nativeWords k := by
  change jordan value13 value22 = _
  rw [native_product_decode_13_22, productColumn_sum_13_22, decode_sum_columns]

def productCoeff_13_23 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, 0, (-3/4), 0, (3/4), 0, 0, 0, (21/4), 0, 0, 0, 0, (9/8), 0, (-9/8), 0, 0, 0, 0, 0, 0]
def productColumn_13_23 : Fin 27 → ℝ := ![0, 0, 0, 0, (-3/16), (21/16), 0, (21/16), 0, 0, (3/16), (3/8), 0, 0, 0, 0, (-3/8), 0, 0, 0, (-3/16), (-3/16), 0, (-21/16), 0, 0, (-21/16)]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_13_23 :
    jordan value13 value23 = decode productColumn_13_23 := by
  simp only [value13_decode, value23_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_13_23, column13, column23, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_13_23 :
    productColumn_13_23 = ∑ k : Fin 27, productCoeff_13_23 k • columns k := by
  funext r
  change productColumn_13_23 r = ∑ k : Fin 27, productCoeff_13_23 k * columns k r
  fin_cases r <;> norm_num [productColumn_13_23, productCoeff_13_23, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_13_23 :
    jordan (nativeWords 13) (nativeWords 23) =
      ∑ k : Fin 27, productCoeff_13_23 k • nativeWords k := by
  change jordan value13 value23 = _
  rw [native_product_decode_13_23, productColumn_sum_13_23, decode_sum_columns]

def productCoeff_13_24 : Fin 27 → ℝ := ![0, (-1/32), 0, 0, 0, 0, 0, 0, (1/32), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1/16), 0, 0, 0, 0, 0, 0, 0]
def productColumn_13_24 : Fin 27 → ℝ := ![(1/32), 0, (-1/32), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (1/64), 0, 0, (-1/64), 0, 0, 0, 0, 0, 0, 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_13_24 :
    jordan value13 value24 = decode productColumn_13_24 := by
  simp only [value13_decode, value24_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_13_24, column13, column24, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_13_24 :
    productColumn_13_24 = ∑ k : Fin 27, productCoeff_13_24 k • columns k := by
  funext r
  change productColumn_13_24 r = ∑ k : Fin 27, productCoeff_13_24 k * columns k r
  fin_cases r <;> norm_num [productColumn_13_24, productCoeff_13_24, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_13_24 :
    jordan (nativeWords 13) (nativeWords 24) =
      ∑ k : Fin 27, productCoeff_13_24 k • nativeWords k := by
  change jordan value13 value24 = _
  rw [native_product_decode_13_24, productColumn_sum_13_24, decode_sum_columns]

def productCoeff_13_25 : Fin 27 → ℝ := ![0, 0, (-3/32), 0, 0, 0, 0, 0, 0, 0, (3/8), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def productColumn_13_25 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-3/32), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_13_25 :
    jordan value13 value25 = decode productColumn_13_25 := by
  simp only [value13_decode, value25_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_13_25, column13, column25, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_13_25 :
    productColumn_13_25 = ∑ k : Fin 27, productCoeff_13_25 k • columns k := by
  funext r
  change productColumn_13_25 r = ∑ k : Fin 27, productCoeff_13_25 k * columns k r
  fin_cases r <;> norm_num [productColumn_13_25, productCoeff_13_25, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_13_25 :
    jordan (nativeWords 13) (nativeWords 25) =
      ∑ k : Fin 27, productCoeff_13_25 k • nativeWords k := by
  change jordan value13 value25 = _
  rw [native_product_decode_13_25, productColumn_sum_13_25, decode_sum_columns]

def productCoeff_13_26 : Fin 27 → ℝ := ![0, 0, 0, (-1/16), 0, (-3/2), 0, 0, 0, 0, 0, (3/4), 0, 0, 0, 0, (-1/4), 0, 0, 0, 0, 0, (1/2), 0, 0, 0, (1/4)]
def productColumn_13_26 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (3/16), 0, (3/16), 0, 0, (3/16), 0, 0, 0, 0, 0, 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_13_26 :
    jordan value13 value26 = decode productColumn_13_26 := by
  simp only [value13_decode, value26_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_13_26, column13, column26, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_13_26 :
    productColumn_13_26 = ∑ k : Fin 27, productCoeff_13_26 k • columns k := by
  funext r
  change productColumn_13_26 r = ∑ k : Fin 27, productCoeff_13_26 k * columns k r
  fin_cases r <;> norm_num [productColumn_13_26, productCoeff_13_26, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_13_26 :
    jordan (nativeWords 13) (nativeWords 26) =
      ∑ k : Fin 27, productCoeff_13_26 k • nativeWords k := by
  change jordan value13 value26 = _
  rw [native_product_decode_13_26, productColumn_sum_13_26, decode_sum_columns]

end
end Glennie.Compact.NativeWordTableR01
