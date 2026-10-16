/- Concrete native Jordan product certificate for word row 15. -/
module
public import Glennie.Compact.NativeWordProductCommonR01

@[expose] public section
namespace Glennie.Compact.NativeWordTableR01
noncomputable section
open Glennie AlbertGeometry.NativeOperatorTrace
open scoped BigOperators Matrix
set_option autoImplicit false

def productCoeff_15_15 : Fin 27 → ℝ := ![(2/3), 0, 0, 0, (-7/16), 0, 0, (-5/24), 0, (-7/48), 0, 0, 0, (-1/6), 0, (-1/12), 0, 0, (1/8), 0, (1/8), 0, 0, (1/24), 0, 0, 0]
def productColumn_15_15 : Fin 27 → ℝ := ![(3/16), (1/8), (3/16), 0, (-1/16), 0, 0, (-1/16), 0, 0, 0, 0, 0, 0, 0, 0, (1/16), 0, 0, 0, (-1/16), 0, 0, (1/16), 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_15_15 :
    jordan value15 value15 = decode productColumn_15_15 := by
  simp only [value15_decode, value15_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_15_15, column15, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_15_15 :
    productColumn_15_15 = ∑ k : Fin 27, productCoeff_15_15 k • columns k := by
  funext r
  change productColumn_15_15 r = ∑ k : Fin 27, productCoeff_15_15 k * columns k r
  fin_cases r <;> norm_num [productColumn_15_15, productCoeff_15_15, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_15_15 :
    jordan (nativeWords 15) (nativeWords 15) =
      ∑ k : Fin 27, productCoeff_15_15 k • nativeWords k := by
  change jordan value15 value15 = _
  rw [native_product_decode_15_15, productColumn_sum_15_15, decode_sum_columns]

def productCoeff_15_16 : Fin 27 → ℝ := ![0, 0, 0, (-1/16), 0, 0, 0, 0, 0, 0, 0, (3/8), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (1/8), 0, 0, 0, (-1/8)]
def productColumn_15_16 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, (1/32), 0, (1/16), (1/32), 0, 0, 0, (1/32), 0, (1/16), 0, 0, (1/32), 0, 0, 0, (-1/32), 0, (-1/16), (-1/32), 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_15_16 :
    jordan value15 value16 = decode productColumn_15_16 := by
  simp only [value15_decode, value16_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_15_16, column15, column16, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_15_16 :
    productColumn_15_16 = ∑ k : Fin 27, productCoeff_15_16 k • columns k := by
  funext r
  change productColumn_15_16 r = ∑ k : Fin 27, productCoeff_15_16 k * columns k r
  fin_cases r <;> norm_num [productColumn_15_16, productCoeff_15_16, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_15_16 :
    jordan (nativeWords 15) (nativeWords 16) =
      ∑ k : Fin 27, productCoeff_15_16 k • nativeWords k := by
  change jordan value15 value16 = _
  rw [native_product_decode_15_16, productColumn_sum_15_16, decode_sum_columns]

def productCoeff_15_17 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, (3/2), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (3/2), 0, 0, 0, 0, 0]
def productColumn_15_17 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, (-3/16), 0, 0, (-9/16), 0, 0, 0, (-3/16), 0, 0, 0, 0, (3/16), 0, 0, 0, (-9/16), 0, 0, (-3/16), 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_15_17 :
    jordan value15 value17 = decode productColumn_15_17 := by
  simp only [value15_decode, value17_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_15_17, column15, column17, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_15_17 :
    productColumn_15_17 = ∑ k : Fin 27, productCoeff_15_17 k • columns k := by
  funext r
  change productColumn_15_17 r = ∑ k : Fin 27, productCoeff_15_17 k * columns k r
  fin_cases r <;> norm_num [productColumn_15_17, productCoeff_15_17, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_15_17 :
    jordan (nativeWords 15) (nativeWords 17) =
      ∑ k : Fin 27, productCoeff_15_17 k • nativeWords k := by
  change jordan value15 value17 = _
  rw [native_product_decode_15_17, productColumn_sum_15_17, decode_sum_columns]

def productCoeff_15_18 : Fin 27 → ℝ := ![(11/12), 0, 0, 0, (-1/4), 0, 0, (-1/3), 0, (-11/24), 0, 0, 0, (1/3), 0, (17/12), 0, 0, 0, 0, (1/8), 0, 0, (1/6), 0, 0, 0]
def productColumn_15_18 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, (-3/16), 0, 0, 0, 0, (-1/16), 0, 0, 0, (-7/16), 0, 0, (-7/16), 0, 0, 0, (1/16), 0, 0, 0, 0, (3/16)]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_15_18 :
    jordan value15 value18 = decode productColumn_15_18 := by
  simp only [value15_decode, value18_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_15_18, column15, column18, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_15_18 :
    productColumn_15_18 = ∑ k : Fin 27, productCoeff_15_18 k • columns k := by
  funext r
  change productColumn_15_18 r = ∑ k : Fin 27, productCoeff_15_18 k * columns k r
  fin_cases r <;> norm_num [productColumn_15_18, productCoeff_15_18, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_15_18 :
    jordan (nativeWords 15) (nativeWords 18) =
      ∑ k : Fin 27, productCoeff_15_18 k • nativeWords k := by
  change jordan value15 value18 = _
  rw [native_product_decode_15_18, productColumn_sum_15_18, decode_sum_columns]

def productCoeff_15_19 : Fin 27 → ℝ := ![0, (3/16), 0, 0, 0, 0, 0, 0, (1/16), 0, 0, 0, (-3/16), 0, (1/16), 0, 0, 0, 0, 0, 0, 0, 0, 0, (1/2), 0, 0]
def productColumn_15_19 : Fin 27 → ℝ := ![(1/16), 0, (-1/16), 0, (3/32), (1/32), 0, (-1/32), 0, 0, (-1/32), 0, 0, 0, (-1/32), 0, 0, (1/32), 0, 0, (-3/32), (-1/32), 0, (-1/32), 0, 0, (1/32)]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_15_19 :
    jordan value15 value19 = decode productColumn_15_19 := by
  simp only [value15_decode, value19_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_15_19, column15, column19, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_15_19 :
    productColumn_15_19 = ∑ k : Fin 27, productCoeff_15_19 k • columns k := by
  funext r
  change productColumn_15_19 r = ∑ k : Fin 27, productCoeff_15_19 k * columns k r
  fin_cases r <;> norm_num [productColumn_15_19, productCoeff_15_19, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_15_19 :
    jordan (nativeWords 15) (nativeWords 19) =
      ∑ k : Fin 27, productCoeff_15_19 k • nativeWords k := by
  change jordan value15 value19 = _
  rw [native_product_decode_15_19, productColumn_sum_15_19, decode_sum_columns]

def productCoeff_15_20 : Fin 27 → ℝ := ![0, 0, 0, 0, (3/4), 0, 0, 0, 0, (-1/4), 0, 0, 0, 0, 0, (7/4), 0, 0, (-3/8), 0, 0, 0, 0, (1/8), 0, 0, 0]
def productColumn_15_20 : Fin 27 → ℝ := ![0, 0, 0, 0, (1/16), (-3/8), 0, (-1/16), 0, 0, 0, (-1/8), 0, 0, (-1/2), 0, 0, (-1/2), 0, 0, (1/16), 0, 0, (1/16), 0, 0, (3/8)]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_15_20 :
    jordan value15 value20 = decode productColumn_15_20 := by
  simp only [value15_decode, value20_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_15_20, column15, column20, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_15_20 :
    productColumn_15_20 = ∑ k : Fin 27, productCoeff_15_20 k • columns k := by
  funext r
  change productColumn_15_20 r = ∑ k : Fin 27, productCoeff_15_20 k * columns k r
  fin_cases r <;> norm_num [productColumn_15_20, productCoeff_15_20, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_15_20 :
    jordan (nativeWords 15) (nativeWords 20) =
      ∑ k : Fin 27, productCoeff_15_20 k • nativeWords k := by
  change jordan value15 value20 = _
  rw [native_product_decode_15_20, productColumn_sum_15_20, decode_sum_columns]

def productCoeff_15_21 : Fin 27 → ℝ := ![0, 0, (1/32), 0, 0, 0, (-3/32), 0, 0, 0, (3/16), 0, 0, 0, 0, 0, 0, (-1/32), 0, 0, 0, (1/8), 0, 0, 0, (1/4), 0]
def productColumn_15_21 : Fin 27 → ℝ := ![0, 0, 0, (1/64), 0, 0, 0, 0, (-3/64), 0, 0, 0, (-1/32), 0, 0, 0, 0, 0, 0, (1/64), 0, 0, 0, 0, (-3/64), 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_15_21 :
    jordan value15 value21 = decode productColumn_15_21 := by
  simp only [value15_decode, value21_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_15_21, column15, column21, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_15_21 :
    productColumn_15_21 = ∑ k : Fin 27, productCoeff_15_21 k • columns k := by
  funext r
  change productColumn_15_21 r = ∑ k : Fin 27, productCoeff_15_21 k * columns k r
  fin_cases r <;> norm_num [productColumn_15_21, productCoeff_15_21, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_15_21 :
    jordan (nativeWords 15) (nativeWords 21) =
      ∑ k : Fin 27, productCoeff_15_21 k • nativeWords k := by
  change jordan value15 value21 = _
  rw [native_product_decode_15_21, productColumn_sum_15_21, decode_sum_columns]

def productCoeff_15_22 : Fin 27 → ℝ := ![0, 0, 0, (-3/16), 0, (-9/16), 0, 0, 0, 0, 0, (-3/8), 0, 0, 0, 0, (3/8), 0, 0, 0, 0, 0, 0, 0, 0, 0, (1/4)]
def productColumn_15_22 : Fin 27 → ℝ := ![0, 0, 0, (1/32), 0, 0, (-5/32), 0, (1/32), (-3/32), 0, 0, 0, (-3/32), 0, 0, 0, 0, (-3/32), (-1/32), 0, 0, (3/32), 0, (-1/32), (5/32), 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_15_22 :
    jordan value15 value22 = decode productColumn_15_22 := by
  simp only [value15_decode, value22_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_15_22, column15, column22, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_15_22 :
    productColumn_15_22 = ∑ k : Fin 27, productCoeff_15_22 k • columns k := by
  funext r
  change productColumn_15_22 r = ∑ k : Fin 27, productCoeff_15_22 k * columns k r
  fin_cases r <;> norm_num [productColumn_15_22, productCoeff_15_22, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_15_22 :
    jordan (nativeWords 15) (nativeWords 22) =
      ∑ k : Fin 27, productCoeff_15_22 k • nativeWords k := by
  change jordan value15 value22 = _
  rw [native_product_decode_15_22, productColumn_sum_15_22, decode_sum_columns]

def productCoeff_15_23 : Fin 27 → ℝ := ![(-11/4), 0, 0, 0, (33/8), 0, 0, 1, 0, (1/4), 0, 0, 0, -1, 0, (13/4), 0, 0, (-3/2), 0, (-3/8), 0, 0, 0, 0, 0, 0]
def productColumn_15_23 : Fin 27 → ℝ := ![(1/8), (-1/4), (1/8), 0, (1/4), (-17/16), 0, (-1/4), 0, 0, (1/16), (-1/2), 0, 0, (-13/16), 0, (-1/8), (-13/16), 0, 0, (1/4), (-1/16), 0, (1/4), 0, 0, (17/16)]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_15_23 :
    jordan value15 value23 = decode productColumn_15_23 := by
  simp only [value15_decode, value23_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_15_23, column15, column23, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_15_23 :
    productColumn_15_23 = ∑ k : Fin 27, productCoeff_15_23 k • columns k := by
  funext r
  change productColumn_15_23 r = ∑ k : Fin 27, productCoeff_15_23 k * columns k r
  fin_cases r <;> norm_num [productColumn_15_23, productCoeff_15_23, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_15_23 :
    jordan (nativeWords 15) (nativeWords 23) =
      ∑ k : Fin 27, productCoeff_15_23 k • nativeWords k := by
  change jordan value15 value23 = _
  rw [native_product_decode_15_23, productColumn_sum_15_23, decode_sum_columns]

def productCoeff_15_24 : Fin 27 → ℝ := ![0, (-1/32), 0, 0, 0, 0, 0, 0, (1/16), 0, 0, 0, (1/32), 0, 0, 0, 0, 0, 0, (-1/16), 0, 0, 0, 0, (1/8), 0, 0]
def productColumn_15_24 : Fin 27 → ℝ := ![(-1/32), 0, (1/32), 0, (-1/64), 0, 0, (-1/64), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (1/64), 0, 0, (-1/64), 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_15_24 :
    jordan value15 value24 = decode productColumn_15_24 := by
  simp only [value15_decode, value24_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_15_24, column15, column24, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_15_24 :
    productColumn_15_24 = ∑ k : Fin 27, productCoeff_15_24 k • columns k := by
  funext r
  change productColumn_15_24 r = ∑ k : Fin 27, productCoeff_15_24 k * columns k r
  fin_cases r <;> norm_num [productColumn_15_24, productCoeff_15_24, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_15_24 :
    jordan (nativeWords 15) (nativeWords 24) =
      ∑ k : Fin 27, productCoeff_15_24 k • nativeWords k := by
  change jordan value15 value24 = _
  rw [native_product_decode_15_24, productColumn_sum_15_24, decode_sum_columns]

def productCoeff_15_25 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, (3/32), 0, 0, 0, (-3/16), 0, 0, 0, 0, 0, 0, (1/32), 0, 0, 0, 0, 0, 0, 0, (-1/4), 0]
def productColumn_15_25 : Fin 27 → ℝ := ![0, 0, 0, (1/64), 0, 0, (-1/64), 0, (3/64), (1/64), 0, 0, (1/16), (-1/64), 0, 0, 0, 0, (1/64), (1/64), 0, 0, (1/64), 0, (3/64), (-1/64), 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_15_25 :
    jordan value15 value25 = decode productColumn_15_25 := by
  simp only [value15_decode, value25_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_15_25, column15, column25, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_15_25 :
    productColumn_15_25 = ∑ k : Fin 27, productCoeff_15_25 k • columns k := by
  funext r
  change productColumn_15_25 r = ∑ k : Fin 27, productCoeff_15_25 k * columns k r
  fin_cases r <;> norm_num [productColumn_15_25, productCoeff_15_25, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_15_25 :
    jordan (nativeWords 15) (nativeWords 25) =
      ∑ k : Fin 27, productCoeff_15_25 k • nativeWords k := by
  change jordan value15 value25 = _
  rw [native_product_decode_15_25, productColumn_sum_15_25, decode_sum_columns]

def productCoeff_15_26 : Fin 27 → ℝ := ![0, 0, 0, (-1/4), 0, (9/16), 0, 0, 0, 0, 0, (-3/8), 0, 0, 0, 0, (3/8), 0, 0, 0, 0, 0, (-1/4), 0, 0, 0, 0]
def productColumn_15_26 : Fin 27 → ℝ := ![0, 0, 0, (-1/32), 0, 0, (-3/32), 0, (1/32), (-5/32), 0, 0, 0, (-5/32), 0, (1/16), 0, 0, (-5/32), (1/32), 0, 0, (5/32), 0, (-1/32), (3/32), 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_15_26 :
    jordan value15 value26 = decode productColumn_15_26 := by
  simp only [value15_decode, value26_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_15_26, column15, column26, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_15_26 :
    productColumn_15_26 = ∑ k : Fin 27, productCoeff_15_26 k • columns k := by
  funext r
  change productColumn_15_26 r = ∑ k : Fin 27, productCoeff_15_26 k * columns k r
  fin_cases r <;> norm_num [productColumn_15_26, productCoeff_15_26, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_15_26 :
    jordan (nativeWords 15) (nativeWords 26) =
      ∑ k : Fin 27, productCoeff_15_26 k • nativeWords k := by
  change jordan value15 value26 = _
  rw [native_product_decode_15_26, productColumn_sum_15_26, decode_sum_columns]

end
end Glennie.Compact.NativeWordTableR01
