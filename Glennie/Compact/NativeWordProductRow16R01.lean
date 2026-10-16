/- Concrete native Jordan product certificate for word row 16. -/
module
public import Glennie.Compact.NativeWordProductCommonR01

@[expose] public section
namespace Glennie.Compact.NativeWordTableR01
noncomputable section
open Glennie AlbertGeometry.NativeOperatorTrace
open scoped BigOperators Matrix
set_option autoImplicit false

def productCoeff_16_16 : Fin 27 → ℝ := ![(9/4), 0, 0, 0, 0, 0, 0, (-15/16), 0, (-9/16), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (3/8), 0, 0, 0]
def productColumn_16_16 : Fin 27 → ℝ := ![(3/4), (3/4), (3/4), 0, (-3/16), (3/16), 0, (-3/16), 0, 0, (3/16), (-3/16), 0, 0, (-3/16), 0, (3/16), (-3/16), 0, 0, (-3/16), (-3/16), 0, (3/16), 0, 0, (-3/16)]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_16_16 :
    jordan value16 value16 = decode productColumn_16_16 := by
  simp only [value16_decode, value16_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_16_16, column16, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_16_16 :
    productColumn_16_16 = ∑ k : Fin 27, productCoeff_16_16 k • columns k := by
  funext r
  change productColumn_16_16 r = ∑ k : Fin 27, productCoeff_16_16 k * columns k r
  fin_cases r <;> norm_num [productColumn_16_16, productCoeff_16_16, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_16_16 :
    jordan (nativeWords 16) (nativeWords 16) =
      ∑ k : Fin 27, productCoeff_16_16 k • nativeWords k := by
  change jordan value16 value16 = _
  rw [native_product_decode_16_16, productColumn_sum_16_16, decode_sum_columns]

def productCoeff_16_17 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, 0, 0, (3/2), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def productColumn_16_17 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, (-3/4), 0, (-3/4), 0, 0, 0, 0, 0, 0, (-3/4), 0, 0, (3/4), 0, 0, 0, 0, 0, (-3/4), 0, 0, (-3/4)]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_16_17 :
    jordan value16 value17 = decode productColumn_16_17 := by
  simp only [value16_decode, value17_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_16_17, column16, column17, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_16_17 :
    productColumn_16_17 = ∑ k : Fin 27, productCoeff_16_17 k • columns k := by
  funext r
  change productColumn_16_17 r = ∑ k : Fin 27, productCoeff_16_17 k * columns k r
  fin_cases r <;> norm_num [productColumn_16_17, productCoeff_16_17, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_16_17 :
    jordan (nativeWords 16) (nativeWords 17) =
      ∑ k : Fin 27, productCoeff_16_17 k • nativeWords k := by
  change jordan value16 value17 = _
  rw [native_product_decode_16_17, productColumn_sum_16_17, decode_sum_columns]

def productCoeff_16_18 : Fin 27 → ℝ := ![0, 0, 0, (3/8), 0, 3, 0, 0, 0, 0, 0, (-9/4), 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, (-3/4), 0, 0, 0, (-3/4)]
def productColumn_16_18 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, (-1/16), 0, (1/4), (5/16), 0, 0, 0, (-7/16), 0, (-7/8), 0, 0, (-7/16), 0, 0, 0, (-5/16), 0, (-1/4), (1/16), 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_16_18 :
    jordan value16 value18 = decode productColumn_16_18 := by
  simp only [value16_decode, value18_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_16_18, column16, column18, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_16_18 :
    productColumn_16_18 = ∑ k : Fin 27, productCoeff_16_18 k • columns k := by
  funext r
  change productColumn_16_18 r = ∑ k : Fin 27, productCoeff_16_18 k * columns k r
  fin_cases r <;> norm_num [productColumn_16_18, productCoeff_16_18, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_16_18 :
    jordan (nativeWords 16) (nativeWords 18) =
      ∑ k : Fin 27, productCoeff_16_18 k • nativeWords k := by
  change jordan value16 value18 = _
  rw [native_product_decode_16_18, productColumn_sum_16_18, decode_sum_columns]

def productCoeff_16_19 : Fin 27 → ℝ := ![0, 0, (3/16), 0, 0, 0, (-3/16), 0, 0, 0, (3/8), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (1/4), 0]
def productColumn_16_19 : Fin 27 → ℝ := ![0, 0, 0, (9/32), 0, 0, (1/32), 0, (-1/32), (1/32), 0, 0, (3/16), 0, 0, 0, 0, 0, 0, (9/32), 0, 0, (1/32), 0, (-1/32), (1/32), 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_16_19 :
    jordan value16 value19 = decode productColumn_16_19 := by
  simp only [value16_decode, value19_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_16_19, column16, column19, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_16_19 :
    productColumn_16_19 = ∑ k : Fin 27, productCoeff_16_19 k • columns k := by
  funext r
  change productColumn_16_19 r = ∑ k : Fin 27, productCoeff_16_19 k * columns k r
  fin_cases r <;> norm_num [productColumn_16_19, productCoeff_16_19, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_16_19 :
    jordan (nativeWords 16) (nativeWords 19) =
      ∑ k : Fin 27, productCoeff_16_19 k • nativeWords k := by
  change jordan value16 value19 = _
  rw [native_product_decode_16_19, productColumn_sum_16_19, decode_sum_columns]

def productCoeff_16_20 : Fin 27 → ℝ := ![0, 0, 0, (3/4), 0, (21/8), 0, 0, 0, 0, 0, (-3/2), 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, (-3/4), 0, 0, 0, (-1/2)]
def productColumn_16_20 : Fin 27 → ℝ := ![0, 0, 0, (-1/16), 0, 0, (-1/8), 0, (3/16), (7/8), 0, 0, 0, (-7/16), 0, (-5/4), 0, 0, (-7/16), (1/16), 0, 0, (-7/8), 0, (-3/16), (1/8), 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_16_20 :
    jordan value16 value20 = decode productColumn_16_20 := by
  simp only [value16_decode, value20_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_16_20, column16, column20, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_16_20 :
    productColumn_16_20 = ∑ k : Fin 27, productCoeff_16_20 k • columns k := by
  funext r
  change productColumn_16_20 r = ∑ k : Fin 27, productCoeff_16_20 k * columns k r
  fin_cases r <;> norm_num [productColumn_16_20, productCoeff_16_20, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_16_20 :
    jordan (nativeWords 16) (nativeWords 20) =
      ∑ k : Fin 27, productCoeff_16_20 k • nativeWords k := by
  change jordan value16 value20 = _
  rw [native_product_decode_16_20, productColumn_sum_16_20, decode_sum_columns]

def productCoeff_16_21 : Fin 27 → ℝ := ![0, (-15/32), 0, 0, 0, 0, 0, 0, (-3/16), 0, 0, 0, (3/32), 0, (3/32), 0, 0, 0, 0, (3/16), 0, 0, 0, 0, (-3/4), 0, 0]
def productColumn_16_21 : Fin 27 → ℝ := ![(3/32), 0, (-3/32), 0, (-3/64), (-3/64), 0, (3/64), 0, 0, (-3/64), 0, 0, 0, 0, 0, 0, 0, 0, 0, (3/64), (-3/64), 0, (3/64), 0, 0, (-3/64)]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_16_21 :
    jordan value16 value21 = decode productColumn_16_21 := by
  simp only [value16_decode, value21_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_16_21, column16, column21, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_16_21 :
    productColumn_16_21 = ∑ k : Fin 27, productCoeff_16_21 k • columns k := by
  funext r
  change productColumn_16_21 r = ∑ k : Fin 27, productCoeff_16_21 k * columns k r
  fin_cases r <;> norm_num [productColumn_16_21, productCoeff_16_21, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_16_21 :
    jordan (nativeWords 16) (nativeWords 21) =
      ∑ k : Fin 27, productCoeff_16_21 k • nativeWords k := by
  change jordan value16 value21 = _
  rw [native_product_decode_16_21, productColumn_sum_16_21, decode_sum_columns]

def productCoeff_16_22 : Fin 27 → ℝ := ![(11/8), 0, 0, 0, (-33/16), 0, 0, (-1/8), 0, (-1/2), 0, 0, 0, (-5/8), 0, (-1/8), 0, 0, (3/16), 0, (3/4), 0, 0, 0, 0, 0, 0]
def productColumn_16_22 : Fin 27 → ℝ := ![(-1/16), (1/8), (-1/16), 0, (-1/32), (-1/8), 0, (-5/32), 0, 0, (-1/8), (1/16), 0, 0, (1/32), 0, (1/4), (1/32), 0, 0, (-1/32), (1/8), 0, (5/32), 0, 0, (1/8)]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_16_22 :
    jordan value16 value22 = decode productColumn_16_22 := by
  simp only [value16_decode, value22_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_16_22, column16, column22, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_16_22 :
    productColumn_16_22 = ∑ k : Fin 27, productCoeff_16_22 k • columns k := by
  funext r
  change productColumn_16_22 r = ∑ k : Fin 27, productCoeff_16_22 k * columns k r
  fin_cases r <;> norm_num [productColumn_16_22, productCoeff_16_22, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_16_22 :
    jordan (nativeWords 16) (nativeWords 22) =
      ∑ k : Fin 27, productCoeff_16_22 k • nativeWords k := by
  change jordan value16 value22 = _
  rw [native_product_decode_16_22, productColumn_sum_16_22, decode_sum_columns]

def productCoeff_16_23 : Fin 27 → ℝ := ![0, 0, 0, (9/8), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def productColumn_16_23 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, (-3/4), 0, (3/4), (21/8), 0, 0, 0, (-3/4), 0, (-21/8), 0, 0, (-3/4), 0, 0, 0, (-21/8), 0, (-3/4), (3/4), 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_16_23 :
    jordan value16 value23 = decode productColumn_16_23 := by
  simp only [value16_decode, value23_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_16_23, column16, column23, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_16_23 :
    productColumn_16_23 = ∑ k : Fin 27, productCoeff_16_23 k • columns k := by
  funext r
  change productColumn_16_23 r = ∑ k : Fin 27, productCoeff_16_23 k * columns k r
  fin_cases r <;> norm_num [productColumn_16_23, productCoeff_16_23, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_16_23 :
    jordan (nativeWords 16) (nativeWords 23) =
      ∑ k : Fin 27, productCoeff_16_23 k • nativeWords k := by
  change jordan value16 value23 = _
  rw [native_product_decode_16_23, productColumn_sum_16_23, decode_sum_columns]

def productCoeff_16_24 : Fin 27 → ℝ := ![0, 0, (-1/16), 0, 0, 0, (-3/32), 0, 0, 0, (3/16), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1/8), 0, 0, 0, (1/8), 0]
def productColumn_16_24 : Fin 27 → ℝ := ![0, 0, 0, (-1/64), 0, 0, (1/32), 0, (-1/64), 0, 0, 0, (-1/16), (1/64), 0, 0, 0, 0, (-1/64), (-1/64), 0, 0, 0, 0, (-1/64), (1/32), 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_16_24 :
    jordan value16 value24 = decode productColumn_16_24 := by
  simp only [value16_decode, value24_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_16_24, column16, column24, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_16_24 :
    productColumn_16_24 = ∑ k : Fin 27, productCoeff_16_24 k • columns k := by
  funext r
  change productColumn_16_24 r = ∑ k : Fin 27, productCoeff_16_24 k * columns k r
  fin_cases r <;> norm_num [productColumn_16_24, productCoeff_16_24, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_16_24 :
    jordan (nativeWords 16) (nativeWords 24) =
      ∑ k : Fin 27, productCoeff_16_24 k • nativeWords k := by
  change jordan value16 value24 = _
  rw [native_product_decode_16_24, productColumn_sum_16_24, decode_sum_columns]

def productCoeff_16_25 : Fin 27 → ℝ := ![0, (3/16), 0, 0, 0, 0, 0, 0, (3/16), 0, 0, 0, (3/32), 0, (-3/32), 0, 0, 0, 0, (-3/16), 0, 0, 0, 0, (3/4), 0, 0]
def productColumn_16_25 : Fin 27 → ℝ := ![(-3/16), 0, (3/16), 0, (-3/64), (3/64), 0, (-3/64), 0, 0, (3/64), 0, 0, 0, 0, 0, 0, 0, 0, 0, (3/64), (3/64), 0, (-3/64), 0, 0, (3/64)]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_16_25 :
    jordan value16 value25 = decode productColumn_16_25 := by
  simp only [value16_decode, value25_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_16_25, column16, column25, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_16_25 :
    productColumn_16_25 = ∑ k : Fin 27, productCoeff_16_25 k • columns k := by
  funext r
  change productColumn_16_25 r = ∑ k : Fin 27, productCoeff_16_25 k * columns k r
  fin_cases r <;> norm_num [productColumn_16_25, productCoeff_16_25, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_16_25 :
    jordan (nativeWords 16) (nativeWords 25) =
      ∑ k : Fin 27, productCoeff_16_25 k • nativeWords k := by
  change jordan value16 value25 = _
  rw [native_product_decode_16_25, productColumn_sum_16_25, decode_sum_columns]

def productCoeff_16_26 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, 0, (3/8), 0, (-3/8), 0, 0, 0, (-9/8), 0, (-3/4), 0, 0, (-9/16), 0, (9/16), 0, 0, 0, 0, 0, 0]
def productColumn_16_26 : Fin 27 → ℝ := ![0, 0, 0, 0, (3/32), (-3/32), 0, (-9/32), 0, 0, (-3/32), (-3/16), 0, 0, (3/16), 0, (3/16), (3/16), 0, 0, (3/32), (3/32), 0, (9/32), 0, 0, (3/32)]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_16_26 :
    jordan value16 value26 = decode productColumn_16_26 := by
  simp only [value16_decode, value26_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_16_26, column16, column26, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_16_26 :
    productColumn_16_26 = ∑ k : Fin 27, productCoeff_16_26 k • columns k := by
  funext r
  change productColumn_16_26 r = ∑ k : Fin 27, productCoeff_16_26 k * columns k r
  fin_cases r <;> norm_num [productColumn_16_26, productCoeff_16_26, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_16_26 :
    jordan (nativeWords 16) (nativeWords 26) =
      ∑ k : Fin 27, productCoeff_16_26 k • nativeWords k := by
  change jordan value16 value26 = _
  rw [native_product_decode_16_26, productColumn_sum_16_26, decode_sum_columns]

end
end Glennie.Compact.NativeWordTableR01
