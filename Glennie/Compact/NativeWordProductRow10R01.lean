/- Concrete native Jordan product certificate for word row 10. -/
module
public import Glennie.Compact.NativeWordProductCommonR01

@[expose] public section
namespace Glennie.Compact.NativeWordTableR01
noncomputable section
open Glennie AlbertGeometry.NativeOperatorTrace
open scoped BigOperators Matrix
set_option autoImplicit false

def productCoeff_10_10 : Fin 27 → ℝ := ![(1/4), 0, 0, 0, (-5/16), 0, 0, (-1/16), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (1/8), 0, 0, 0, 0, 0, 0, 0, 0]
def productColumn_10_10 : Fin 27 → ℝ := ![(1/16), (1/8), (1/16), 0, 0, 0, 0, 0, 0, 0, 0, (1/16), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_10_10 :
    jordan value10 value10 = decode productColumn_10_10 := by
  simp only [value10_decode, value10_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_10_10, column10, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_10_10 :
    productColumn_10_10 = ∑ k : Fin 27, productCoeff_10_10 k • columns k := by
  funext r
  change productColumn_10_10 r = ∑ k : Fin 27, productCoeff_10_10 k * columns k r
  fin_cases r <;> norm_num [productColumn_10_10, productCoeff_10_10, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_10_10 :
    jordan (nativeWords 10) (nativeWords 10) =
      ∑ k : Fin 27, productCoeff_10_10 k • nativeWords k := by
  change jordan value10 value10 = _
  rw [native_product_decode_10_10, productColumn_sum_10_10, decode_sum_columns]

def productCoeff_10_11 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, 0, 0, (-1/16), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (1/8), 0, 0, 0, 0, 0, 0, 0]
def productColumn_10_11 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1/32), 0, 0, (1/32), 0, 0, 0, 0, 0, 0, 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_10_11 :
    jordan value10 value11 = decode productColumn_10_11 := by
  simp only [value10_decode, value11_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_10_11, column10, column11, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_10_11 :
    productColumn_10_11 = ∑ k : Fin 27, productCoeff_10_11 k • columns k := by
  funext r
  change productColumn_10_11 r = ∑ k : Fin 27, productCoeff_10_11 k * columns k r
  fin_cases r <;> norm_num [productColumn_10_11, productCoeff_10_11, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_10_11 :
    jordan (nativeWords 10) (nativeWords 11) =
      ∑ k : Fin 27, productCoeff_10_11 k • nativeWords k := by
  change jordan value10 value11 = _
  rw [native_product_decode_10_11, productColumn_sum_10_11, decode_sum_columns]

def productCoeff_10_12 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, (1/2), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def productColumn_10_12 : Fin 27 → ℝ := ![0, 0, 0, (-1/4), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (1/4), 0, 0, 0, 0, 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_10_12 :
    jordan value10 value12 = decode productColumn_10_12 := by
  simp only [value10_decode, value12_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_10_12, column10, column12, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_10_12 :
    productColumn_10_12 = ∑ k : Fin 27, productCoeff_10_12 k • columns k := by
  funext r
  change productColumn_10_12 r = ∑ k : Fin 27, productCoeff_10_12 k * columns k r
  fin_cases r <;> norm_num [productColumn_10_12, productCoeff_10_12, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_10_12 :
    jordan (nativeWords 10) (nativeWords 12) =
      ∑ k : Fin 27, productCoeff_10_12 k • nativeWords k := by
  change jordan value10 value12 = _
  rw [native_product_decode_10_12, productColumn_sum_10_12, decode_sum_columns]

def productCoeff_10_13 : Fin 27 → ℝ := ![0, 0, (1/24), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1/48), 0, 0, 0, (-1/6), 0, 0, 0, (-1/12), 0]
def productColumn_10_13 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (1/32), 0, 0, 0, 0, (-1/32), 0, 0, 0, 0, 0, 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_10_13 :
    jordan value10 value13 = decode productColumn_10_13 := by
  simp only [value10_decode, value13_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_10_13, column10, column13, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_10_13 :
    productColumn_10_13 = ∑ k : Fin 27, productCoeff_10_13 k • columns k := by
  funext r
  change productColumn_10_13 r = ∑ k : Fin 27, productCoeff_10_13 k * columns k r
  fin_cases r <;> norm_num [productColumn_10_13, productCoeff_10_13, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_10_13 :
    jordan (nativeWords 10) (nativeWords 13) =
      ∑ k : Fin 27, productCoeff_10_13 k • nativeWords k := by
  change jordan value10 value13 = _
  rw [native_product_decode_10_13, productColumn_sum_10_13, decode_sum_columns]

def productCoeff_10_14 : Fin 27 → ℝ := ![0, 0, 0, (-1/24), 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (1/12), 0, 0, 0, 0, 0, (-1/6), 0, 0, 0, (-1/12)]
def productColumn_10_14 : Fin 27 → ℝ := ![0, 0, 0, (-1/4), 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1/16), 0, 0, 0, 0, (-1/16), (1/4), 0, 0, 0, 0, 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_10_14 :
    jordan value10 value14 = decode productColumn_10_14 := by
  simp only [value10_decode, value14_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_10_14, column10, column14, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_10_14 :
    productColumn_10_14 = ∑ k : Fin 27, productCoeff_10_14 k • columns k := by
  funext r
  change productColumn_10_14 r = ∑ k : Fin 27, productCoeff_10_14 k * columns k r
  fin_cases r <;> norm_num [productColumn_10_14, productCoeff_10_14, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_10_14 :
    jordan (nativeWords 10) (nativeWords 14) =
      ∑ k : Fin 27, productCoeff_10_14 k • nativeWords k := by
  change jordan value10 value14 = _
  rw [native_product_decode_10_14, productColumn_sum_10_14, decode_sum_columns]

def productCoeff_10_15 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, (1/8), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (1/4), 0, 0, 0, 0, 0]
def productColumn_10_15 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, (-1/32), 0, 0, (-1/32), 0, 0, 0, (-1/32), 0, 0, 0, 0, (1/32), 0, 0, 0, (-1/32), 0, 0, (-1/32), 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_10_15 :
    jordan value10 value15 = decode productColumn_10_15 := by
  simp only [value10_decode, value15_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_10_15, column10, column15, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_10_15 :
    productColumn_10_15 = ∑ k : Fin 27, productCoeff_10_15 k • columns k := by
  funext r
  change productColumn_10_15 r = ∑ k : Fin 27, productCoeff_10_15 k * columns k r
  fin_cases r <;> norm_num [productColumn_10_15, productCoeff_10_15, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_10_15 :
    jordan (nativeWords 10) (nativeWords 15) =
      ∑ k : Fin 27, productCoeff_10_15 k • nativeWords k := by
  change jordan value10 value15 = _
  rw [native_product_decode_10_15, productColumn_sum_10_15, decode_sum_columns]

def productCoeff_10_16 : Fin 27 → ℝ := ![0, (-1/8), 0, 0, 0, 0, 0, 0, (1/16), 0, 0, 0, 0, 0, (1/16), 0, 0, 0, 0, (1/8), 0, 0, 0, 0, (1/4), 0, 0]
def productColumn_10_16 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, (-1/32), 0, (-1/16), 0, 0, (-1/32), 0, 0, 0, (-3/32), 0, 0, (3/32), 0, 0, 0, (-1/32), 0, (-1/16), 0, 0, (-1/32)]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_10_16 :
    jordan value10 value16 = decode productColumn_10_16 := by
  simp only [value10_decode, value16_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_10_16, column10, column16, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_10_16 :
    productColumn_10_16 = ∑ k : Fin 27, productCoeff_10_16 k • columns k := by
  funext r
  change productColumn_10_16 r = ∑ k : Fin 27, productCoeff_10_16 k * columns k r
  fin_cases r <;> norm_num [productColumn_10_16, productCoeff_10_16, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_10_16 :
    jordan (nativeWords 10) (nativeWords 16) =
      ∑ k : Fin 27, productCoeff_10_16 k • nativeWords k := by
  change jordan value10 value16 = _
  rw [native_product_decode_10_16, productColumn_sum_10_16, decode_sum_columns]

def productCoeff_10_17 : Fin 27 → ℝ := ![(2/3), 0, 0, 0, (-7/4), 0, 0, (1/6), 0, (1/6), 0, 0, 0, (-1/6), 0, (-1/12), 0, 0, (1/2), 0, (1/8), 0, 0, (-1/12), 0, 0, 0]
def productColumn_10_17 : Fin 27 → ℝ := ![(1/2), 1, (1/2), 0, (1/4), (-1/16), 0, 0, 0, 0, (1/16), (1/2), 0, 0, (1/16), 0, (1/8), (1/16), 0, 0, (1/4), (-1/16), 0, 0, 0, 0, (1/16)]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_10_17 :
    jordan value10 value17 = decode productColumn_10_17 := by
  simp only [value10_decode, value17_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_10_17, column10, column17, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_10_17 :
    productColumn_10_17 = ∑ k : Fin 27, productCoeff_10_17 k • columns k := by
  funext r
  change productColumn_10_17 r = ∑ k : Fin 27, productCoeff_10_17 k * columns k r
  fin_cases r <;> norm_num [productColumn_10_17, productCoeff_10_17, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_10_17 :
    jordan (nativeWords 10) (nativeWords 17) =
      ∑ k : Fin 27, productCoeff_10_17 k • nativeWords k := by
  change jordan value10 value17 = _
  rw [native_product_decode_10_17, productColumn_sum_10_17, decode_sum_columns]

def productCoeff_10_18 : Fin 27 → ℝ := ![0, 0, (1/8), 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def productColumn_10_18 : Fin 27 → ℝ := ![0, 0, 0, (3/8), 0, 0, 0, 0, 0, 0, 0, 0, (1/8), 0, 0, 0, 0, 0, 0, (3/8), 0, 0, 0, 0, 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_10_18 :
    jordan value10 value18 = decode productColumn_10_18 := by
  simp only [value10_decode, value18_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_10_18, column10, column18, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_10_18 :
    productColumn_10_18 = ∑ k : Fin 27, productCoeff_10_18 k • columns k := by
  funext r
  change productColumn_10_18 r = ∑ k : Fin 27, productCoeff_10_18 k * columns k r
  fin_cases r <;> norm_num [productColumn_10_18, productCoeff_10_18, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_10_18 :
    jordan (nativeWords 10) (nativeWords 18) =
      ∑ k : Fin 27, productCoeff_10_18 k • nativeWords k := by
  change jordan value10 value18 = _
  rw [native_product_decode_10_18, productColumn_sum_10_18, decode_sum_columns]

def productCoeff_10_19 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, (-1/4), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (1/8), 0, 0, 0, 0, 0, 0, 0, 0, 0, (1/8)]
def productColumn_10_19 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, (-1/16), 0, 0, (1/16), 0, 0, 0, (-1/32), 0, (-1/16), 0, 0, (-1/32), 0, 0, 0, (-1/16), 0, 0, (1/16), 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_10_19 :
    jordan value10 value19 = decode productColumn_10_19 := by
  simp only [value10_decode, value19_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_10_19, column10, column19, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_10_19 :
    productColumn_10_19 = ∑ k : Fin 27, productCoeff_10_19 k • columns k := by
  funext r
  change productColumn_10_19 r = ∑ k : Fin 27, productCoeff_10_19 k * columns k r
  fin_cases r <;> norm_num [productColumn_10_19, productCoeff_10_19, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_10_19 :
    jordan (nativeWords 10) (nativeWords 19) =
      ∑ k : Fin 27, productCoeff_10_19 k • nativeWords k := by
  change jordan value10 value19 = _
  rw [native_product_decode_10_19, productColumn_sum_10_19, decode_sum_columns]

def productCoeff_10_20 : Fin 27 → ℝ := ![0, 0, (-1/4), 0, 0, 0, (1/4), 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, (1/8), 0, 0, 0, 0, 0, 0, 0, (-1/2), 0]
def productColumn_10_20 : Fin 27 → ℝ := ![0, 0, 0, (1/4), 0, 0, 0, 0, (1/8), 0, 0, 0, 0, (-1/16), 0, 0, 0, 0, (1/16), (1/4), 0, 0, 0, 0, (1/8), 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_10_20 :
    jordan value10 value20 = decode productColumn_10_20 := by
  simp only [value10_decode, value20_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_10_20, column10, column20, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_10_20 :
    productColumn_10_20 = ∑ k : Fin 27, productCoeff_10_20 k • columns k := by
  funext r
  change productColumn_10_20 r = ∑ k : Fin 27, productCoeff_10_20 k * columns k r
  fin_cases r <;> norm_num [productColumn_10_20, productCoeff_10_20, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_10_20 :
    jordan (nativeWords 10) (nativeWords 20) =
      ∑ k : Fin 27, productCoeff_10_20 k • nativeWords k := by
  change jordan value10 value20 = _
  rw [native_product_decode_10_20, productColumn_sum_10_20, decode_sum_columns]

def productCoeff_10_21 : Fin 27 → ℝ := ![(-5/48), 0, 0, 0, (1/16), 0, 0, (1/48), 0, (5/96), 0, 0, 0, (-1/48), 0, (1/48), 0, 0, 0, 0, (-1/32), 0, 0, (-1/96), 0, 0, 0]
def productColumn_10_21 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, (-1/64), 0, 0, 0, 0, (1/64), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1/64), 0, 0, 0, 0, (1/64)]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_10_21 :
    jordan value10 value21 = decode productColumn_10_21 := by
  simp only [value10_decode, value21_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_10_21, column10, column21, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_10_21 :
    productColumn_10_21 = ∑ k : Fin 27, productCoeff_10_21 k • columns k := by
  funext r
  change productColumn_10_21 r = ∑ k : Fin 27, productCoeff_10_21 k * columns k r
  fin_cases r <;> norm_num [productColumn_10_21, productCoeff_10_21, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_10_21 :
    jordan (nativeWords 10) (nativeWords 21) =
      ∑ k : Fin 27, productCoeff_10_21 k • nativeWords k := by
  change jordan value10 value21 = _
  rw [native_product_decode_10_21, productColumn_sum_10_21, decode_sum_columns]

def productCoeff_10_22 : Fin 27 → ℝ := ![0, (3/8), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1/16), 0, 0, 0, 0, 0, 0, 0, 0, 0, (1/4), 0, 0]
def productColumn_10_22 : Fin 27 → ℝ := ![(-1/4), 0, (1/4), 0, 0, (1/32), 0, 0, 0, 0, (1/32), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (1/32), 0, 0, 0, 0, (1/32)]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_10_22 :
    jordan value10 value22 = decode productColumn_10_22 := by
  simp only [value10_decode, value22_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_10_22, column10, column22, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_10_22 :
    productColumn_10_22 = ∑ k : Fin 27, productCoeff_10_22 k • columns k := by
  funext r
  change productColumn_10_22 r = ∑ k : Fin 27, productCoeff_10_22 k * columns k r
  fin_cases r <;> norm_num [productColumn_10_22, productCoeff_10_22, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_10_22 :
    jordan (nativeWords 10) (nativeWords 22) =
      ∑ k : Fin 27, productCoeff_10_22 k • nativeWords k := by
  change jordan value10 value22 = _
  rw [native_product_decode_10_22, productColumn_sum_10_22, decode_sum_columns]

def productCoeff_10_23 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, (3/4), 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, (1/4), 0, 0, 0, (1/2), 0, 0, 0, -1, 0]
def productColumn_10_23 : Fin 27 → ℝ := ![0, 0, 0, (5/4), 0, 0, (-1/16), 0, (1/4), (-1/16), 0, 0, (1/2), (-3/16), 0, 0, 0, 0, (3/16), (5/4), 0, 0, (-1/16), 0, (1/4), (-1/16), 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_10_23 :
    jordan value10 value23 = decode productColumn_10_23 := by
  simp only [value10_decode, value23_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_10_23, column10, column23, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_10_23 :
    productColumn_10_23 = ∑ k : Fin 27, productCoeff_10_23 k • columns k := by
  funext r
  change productColumn_10_23 r = ∑ k : Fin 27, productCoeff_10_23 k * columns k r
  fin_cases r <;> norm_num [productColumn_10_23, productCoeff_10_23, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_10_23 :
    jordan (nativeWords 10) (nativeWords 23) =
      ∑ k : Fin 27, productCoeff_10_23 k • nativeWords k := by
  change jordan value10 value23 = _
  rw [native_product_decode_10_23, productColumn_sum_10_23, decode_sum_columns]

def productCoeff_10_24 : Fin 27 → ℝ := ![0, 0, 0, (1/96), 0, (-1/8), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1/48), 0, 0, 0, 0, 0, (1/24), 0, 0, 0, (1/48)]
def productColumn_10_24 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (1/64), 0, 0, 0, 0, (1/64), 0, 0, 0, 0, 0, 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_10_24 :
    jordan value10 value24 = decode productColumn_10_24 := by
  simp only [value10_decode, value24_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_10_24, column10, column24, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_10_24 :
    productColumn_10_24 = ∑ k : Fin 27, productCoeff_10_24 k • columns k := by
  funext r
  change productColumn_10_24 r = ∑ k : Fin 27, productCoeff_10_24 k * columns k r
  fin_cases r <;> norm_num [productColumn_10_24, productCoeff_10_24, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_10_24 :
    jordan (nativeWords 10) (nativeWords 24) =
      ∑ k : Fin 27, productCoeff_10_24 k • nativeWords k := by
  change jordan value10 value24 = _
  rw [native_product_decode_10_24, productColumn_sum_10_24, decode_sum_columns]

def productCoeff_10_25 : Fin 27 → ℝ := ![(-1/48), 0, 0, 0, (1/8), 0, 0, (-1/48), 0, (1/96), 0, 0, 0, (1/48), 0, (1/24), 0, 0, 0, 0, (-1/16), 0, 0, (1/96), 0, 0, 0]
def productColumn_10_25 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1/64), 0, (-1/32), (-1/64), 0, 0, 0, 0, 0, 0, 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_10_25 :
    jordan value10 value25 = decode productColumn_10_25 := by
  simp only [value10_decode, value25_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_10_25, column10, column25, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_10_25 :
    productColumn_10_25 = ∑ k : Fin 27, productCoeff_10_25 k • columns k := by
  funext r
  change productColumn_10_25 r = ∑ k : Fin 27, productCoeff_10_25 k * columns k r
  fin_cases r <;> norm_num [productColumn_10_25, productCoeff_10_25, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_10_25 :
    jordan (nativeWords 10) (nativeWords 25) =
      ∑ k : Fin 27, productCoeff_10_25 k • nativeWords k := by
  change jordan value10 value25 = _
  rw [native_product_decode_10_25, productColumn_sum_10_25, decode_sum_columns]

def productCoeff_10_26 : Fin 27 → ℝ := ![0, (1/4), 0, 0, 0, 0, 0, 0, (-1/16), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (1/8), 0, 0, 0, 0, 0, 0, 0]
def productColumn_10_26 : Fin 27 → ℝ := ![(-1/4), 0, (1/4), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1/32), 0, 0, (1/32), 0, 0, 0, 0, 0, 0, 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_10_26 :
    jordan value10 value26 = decode productColumn_10_26 := by
  simp only [value10_decode, value26_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_10_26, column10, column26, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_10_26 :
    productColumn_10_26 = ∑ k : Fin 27, productCoeff_10_26 k • columns k := by
  funext r
  change productColumn_10_26 r = ∑ k : Fin 27, productCoeff_10_26 k * columns k r
  fin_cases r <;> norm_num [productColumn_10_26, productCoeff_10_26, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_10_26 :
    jordan (nativeWords 10) (nativeWords 26) =
      ∑ k : Fin 27, productCoeff_10_26 k • nativeWords k := by
  change jordan value10 value26 = _
  rw [native_product_decode_10_26, productColumn_sum_10_26, decode_sum_columns]

end
end Glennie.Compact.NativeWordTableR01
