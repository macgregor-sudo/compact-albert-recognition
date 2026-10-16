/- Concrete native Jordan product certificate for word row 17. -/
module
public import Glennie.Compact.NativeWordProductCommonR01

@[expose] public section
namespace Glennie.Compact.NativeWordTableR01
noncomputable section
open Glennie AlbertGeometry.NativeOperatorTrace
open scoped BigOperators Matrix
set_option autoImplicit false

def productCoeff_17_17 : Fin 27 → ℝ := ![-9, 0, 0, 0, 0, 0, 0, (27/4), 0, (21/4), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-3/2), 0, 0, 0]
def productColumn_17_17 : Fin 27 → ℝ := ![9, 9, 9, 0, (15/4), (-3/4), 0, (3/4), 0, 0, (9/4), (15/4), 0, 0, (3/4), 0, (9/4), (3/4), 0, 0, (15/4), (-9/4), 0, (-3/4), 0, 0, (3/4)]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_17_17 :
    jordan value17 value17 = decode productColumn_17_17 := by
  simp only [value17_decode, value17_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_17_17, column17, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_17_17 :
    productColumn_17_17 = ∑ k : Fin 27, productCoeff_17_17 k • columns k := by
  funext r
  change productColumn_17_17 r = ∑ k : Fin 27, productCoeff_17_17 k * columns k r
  fin_cases r <;> norm_num [productColumn_17_17, productCoeff_17_17, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_17_17 :
    jordan (nativeWords 17) (nativeWords 17) =
      ∑ k : Fin 27, productCoeff_17_17 k • nativeWords k := by
  change jordan value17 value17 = _
  rw [native_product_decode_17_17, productColumn_sum_17_17, decode_sum_columns]

def productCoeff_17_18 : Fin 27 → ℝ := ![0, 0, 3, 0, 0, 0, 0, 0, 0, 0, -6, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 0, 2, 0]
def productColumn_17_18 : Fin 27 → ℝ := ![0, 0, 0, (7/2), 0, 0, (3/8), 0, (1/4), (-1/8), 0, 0, 5, (-7/8), 0, 0, 0, 0, (7/8), (7/2), 0, 0, (-1/8), 0, (1/4), (3/8), 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_17_18 :
    jordan value17 value18 = decode productColumn_17_18 := by
  simp only [value17_decode, value18_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_17_18, column17, column18, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_17_18 :
    productColumn_17_18 = ∑ k : Fin 27, productCoeff_17_18 k • columns k := by
  funext r
  change productColumn_17_18 r = ∑ k : Fin 27, productCoeff_17_18 k * columns k r
  fin_cases r <;> norm_num [productColumn_17_18, productCoeff_17_18, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_17_18 :
    jordan (nativeWords 17) (nativeWords 18) =
      ∑ k : Fin 27, productCoeff_17_18 k • nativeWords k := by
  change jordan value17 value18 = _
  rw [native_product_decode_17_18, productColumn_sum_17_18, decode_sum_columns]

def productCoeff_17_19 : Fin 27 → ℝ := ![0, 0, 0, (-5/8), 0, (-21/8), 0, 0, 0, 0, 0, (3/4), 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, (1/2), 0, 0, 0, (3/4)]
def productColumn_17_19 : Fin 27 → ℝ := ![0, 0, 0, (1/16), 0, 0, (-11/16), 0, (7/16), (9/16), 0, 0, 0, (-3/8), 0, (-3/8), 0, 0, (-3/8), (-1/16), 0, 0, (-9/16), 0, (-7/16), (11/16), 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_17_19 :
    jordan value17 value19 = decode productColumn_17_19 := by
  simp only [value17_decode, value19_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_17_19, column17, column19, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_17_19 :
    productColumn_17_19 = ∑ k : Fin 27, productCoeff_17_19 k • columns k := by
  funext r
  change productColumn_17_19 r = ∑ k : Fin 27, productCoeff_17_19 k * columns k r
  fin_cases r <;> norm_num [productColumn_17_19, productCoeff_17_19, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_17_19 :
    jordan (nativeWords 17) (nativeWords 19) =
      ∑ k : Fin 27, productCoeff_17_19 k • nativeWords k := by
  change jordan value17 value19 = _
  rw [native_product_decode_17_19, productColumn_sum_17_19, decode_sum_columns]

def productCoeff_17_20 : Fin 27 → ℝ := ![0, 0, (-7/4), 0, 0, 0, (3/4), 0, 0, 0, (-15/2), 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0, -1, 0]
def productColumn_17_20 : Fin 27 → ℝ := ![0, 0, 0, (19/8), 0, 0, (5/4), 0, (13/8), 0, 0, 0, (17/4), (-13/8), 0, 0, 0, 0, (13/8), (19/8), 0, 0, 0, 0, (13/8), (5/4), 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_17_20 :
    jordan value17 value20 = decode productColumn_17_20 := by
  simp only [value17_decode, value20_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_17_20, column17, column20, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_17_20 :
    productColumn_17_20 = ∑ k : Fin 27, productCoeff_17_20 k • columns k := by
  funext r
  change productColumn_17_20 r = ∑ k : Fin 27, productCoeff_17_20 k * columns k r
  fin_cases r <;> norm_num [productColumn_17_20, productCoeff_17_20, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_17_20 :
    jordan (nativeWords 17) (nativeWords 20) =
      ∑ k : Fin 27, productCoeff_17_20 k • nativeWords k := by
  change jordan value17 value20 = _
  rw [native_product_decode_17_20, productColumn_sum_17_20, decode_sum_columns]

def productCoeff_17_21 : Fin 27 → ℝ := ![(-5/8), 0, 0, 0, (15/16), 0, 0, (1/8), 0, (1/8), 0, 0, 0, (-1/8), 0, (-1/4), 0, 0, (-3/16), 0, (-3/16), 0, 0, 0, 0, 0, 0]
def productColumn_17_21 : Fin 27 → ℝ := ![(1/16), (-1/8), (1/16), 0, (1/32), (1/32), 0, (-1/32), 0, 0, (1/32), (-1/16), 0, 0, (1/16), 0, (-1/16), (1/16), 0, 0, (1/32), (-1/32), 0, (1/32), 0, 0, (-1/32)]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_17_21 :
    jordan value17 value21 = decode productColumn_17_21 := by
  simp only [value17_decode, value21_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_17_21, column17, column21, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_17_21 :
    productColumn_17_21 = ∑ k : Fin 27, productCoeff_17_21 k • columns k := by
  funext r
  change productColumn_17_21 r = ∑ k : Fin 27, productCoeff_17_21 k * columns k r
  fin_cases r <;> norm_num [productColumn_17_21, productCoeff_17_21, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_17_21 :
    jordan (nativeWords 17) (nativeWords 21) =
      ∑ k : Fin 27, productCoeff_17_21 k • nativeWords k := by
  change jordan value17 value21 = _
  rw [native_product_decode_17_21, productColumn_sum_17_21, decode_sum_columns]

def productCoeff_17_22 : Fin 27 → ℝ := ![0, (57/8), 0, 0, 0, 0, 0, 0, (9/8), 0, 0, 0, (-15/8), 0, (-3/4), 0, 0, 0, 0, (-3/2), 0, 0, 0, 0, (3/2), 0, 0]
def productColumn_17_22 : Fin 27 → ℝ := ![(-15/8), 0, (15/8), 0, (15/16), 0, 0, (-3/16), 0, 0, (3/8), 0, 0, 0, (3/16), 0, 0, (-3/16), 0, 0, (-15/16), (3/8), 0, (-3/16), 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_17_22 :
    jordan value17 value22 = decode productColumn_17_22 := by
  simp only [value17_decode, value22_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_17_22, column17, column22, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_17_22 :
    productColumn_17_22 = ∑ k : Fin 27, productCoeff_17_22 k • columns k := by
  funext r
  change productColumn_17_22 r = ∑ k : Fin 27, productCoeff_17_22 k * columns k r
  fin_cases r <;> norm_num [productColumn_17_22, productCoeff_17_22, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_17_22 :
    jordan (nativeWords 17) (nativeWords 22) =
      ∑ k : Fin 27, productCoeff_17_22 k • nativeWords k := by
  change jordan value17 value22 = _
  rw [native_product_decode_17_22, productColumn_sum_17_22, decode_sum_columns]

def productCoeff_17_23 : Fin 27 → ℝ := ![0, 0, (-9/4), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (15/2), 0, 0, 0, 0, 0, 0, 0, 0, 0]
def productColumn_17_23 : Fin 27 → ℝ := ![0, 0, 0, (51/4), 0, 0, (15/4), 0, (15/4), 0, 0, 0, (51/4), (-15/4), 0, 0, 0, 0, (15/4), (51/4), 0, 0, 0, 0, (15/4), (15/4), 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_17_23 :
    jordan value17 value23 = decode productColumn_17_23 := by
  simp only [value17_decode, value23_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_17_23, column17, column23, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_17_23 :
    productColumn_17_23 = ∑ k : Fin 27, productCoeff_17_23 k • columns k := by
  funext r
  change productColumn_17_23 r = ∑ k : Fin 27, productCoeff_17_23 k * columns k r
  fin_cases r <;> norm_num [productColumn_17_23, productCoeff_17_23, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_17_23 :
    jordan (nativeWords 17) (nativeWords 23) =
      ∑ k : Fin 27, productCoeff_17_23 k • nativeWords k := by
  change jordan value17 value23 = _
  rw [native_product_decode_17_23, productColumn_sum_17_23, decode_sum_columns]

def productCoeff_17_24 : Fin 27 → ℝ := ![0, 0, 0, (3/16), 0, (-21/16), 0, 0, 0, 0, 0, (-3/4), 0, 0, 0, 0, (-1/4), 0, 0, 0, 0, 0, (3/8), 0, 0, 0, (1/4)]
def productColumn_17_24 : Fin 27 → ℝ := ![0, 0, 0, (1/32), 0, 0, 0, 0, (-1/32), (-1/8), 0, 0, 0, (5/32), 0, (-1/16), 0, 0, (5/32), (-1/32), 0, 0, (1/8), 0, (1/32), 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_17_24 :
    jordan value17 value24 = decode productColumn_17_24 := by
  simp only [value17_decode, value24_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_17_24, column17, column24, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_17_24 :
    productColumn_17_24 = ∑ k : Fin 27, productCoeff_17_24 k • columns k := by
  funext r
  change productColumn_17_24 r = ∑ k : Fin 27, productCoeff_17_24 k * columns k r
  fin_cases r <;> norm_num [productColumn_17_24, productCoeff_17_24, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_17_24 :
    jordan (nativeWords 17) (nativeWords 24) =
      ∑ k : Fin 27, productCoeff_17_24 k • nativeWords k := by
  change jordan value17 value24 = _
  rw [native_product_decode_17_24, productColumn_sum_17_24, decode_sum_columns]

def productCoeff_17_25 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, 0, (-3/8), 0, (3/8), 0, 0, 0, (-3/8), 0, (3/4), 0, 0, (9/16), 0, (-9/16), 0, 0, 0, 0, 0, 0]
def productColumn_17_25 : Fin 27 → ℝ := ![0, 0, 0, 0, (-3/32), (-9/32), 0, (-3/32), 0, 0, (3/32), (3/16), 0, 0, (-3/16), 0, (-3/16), (-3/16), 0, 0, (-3/32), (-3/32), 0, (3/32), 0, 0, (9/32)]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_17_25 :
    jordan value17 value25 = decode productColumn_17_25 := by
  simp only [value17_decode, value25_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_17_25, column17, column25, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_17_25 :
    productColumn_17_25 = ∑ k : Fin 27, productCoeff_17_25 k • columns k := by
  funext r
  change productColumn_17_25 r = ∑ k : Fin 27, productCoeff_17_25 k * columns k r
  fin_cases r <;> norm_num [productColumn_17_25, productCoeff_17_25, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_17_25 :
    jordan (nativeWords 17) (nativeWords 25) =
      ∑ k : Fin 27, productCoeff_17_25 k • nativeWords k := by
  change jordan value17 value25 = _
  rw [native_product_decode_17_25, productColumn_sum_17_25, decode_sum_columns]

def productCoeff_17_26 : Fin 27 → ℝ := ![0, (33/4), 0, 0, 0, 0, 0, 0, (-3/4), 0, 0, 0, (-15/8), 0, (-9/8), 0, 0, 0, 0, (3/4), 0, 0, 0, 0, -3, 0, 0]
def productColumn_17_26 : Fin 27 → ℝ := ![(-9/4), 0, (9/4), 0, (15/16), (-3/16), 0, (3/16), 0, 0, (9/16), 0, 0, 0, 0, 0, 0, 0, 0, 0, (-15/16), (9/16), 0, (3/16), 0, 0, (-3/16)]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_17_26 :
    jordan value17 value26 = decode productColumn_17_26 := by
  simp only [value17_decode, value26_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_17_26, column17, column26, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_17_26 :
    productColumn_17_26 = ∑ k : Fin 27, productCoeff_17_26 k • columns k := by
  funext r
  change productColumn_17_26 r = ∑ k : Fin 27, productCoeff_17_26 k * columns k r
  fin_cases r <;> norm_num [productColumn_17_26, productCoeff_17_26, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_17_26 :
    jordan (nativeWords 17) (nativeWords 26) =
      ∑ k : Fin 27, productCoeff_17_26 k • nativeWords k := by
  change jordan value17 value26 = _
  rw [native_product_decode_17_26, productColumn_sum_17_26, decode_sum_columns]

end
end Glennie.Compact.NativeWordTableR01
