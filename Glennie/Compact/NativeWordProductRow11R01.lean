/- Concrete native Jordan product certificate for word row 11. -/
module
public import Glennie.Compact.NativeWordProductCommonR01

@[expose] public section
namespace Glennie.Compact.NativeWordTableR01
noncomputable section
open Glennie AlbertGeometry.NativeOperatorTrace
open scoped BigOperators Matrix
set_option autoImplicit false

def productCoeff_11_11 : Fin 27 → ℝ := ![(1/4), 0, 0, 0, (-5/16), 0, 0, 0, 0, (-1/16), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (1/8), 0, 0, 0, 0, 0, 0]
def productColumn_11_11 : Fin 27 → ℝ := ![(1/16), (1/8), (1/16), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (1/16), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_11_11 :
    jordan value11 value11 = decode productColumn_11_11 := by
  simp only [value11_decode, value11_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_11_11, column11, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_11_11 :
    productColumn_11_11 = ∑ k : Fin 27, productCoeff_11_11 k • columns k := by
  funext r
  change productColumn_11_11 r = ∑ k : Fin 27, productCoeff_11_11 k * columns k r
  fin_cases r <;> norm_num [productColumn_11_11, productCoeff_11_11, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_11_11 :
    jordan (nativeWords 11) (nativeWords 11) =
      ∑ k : Fin 27, productCoeff_11_11 k • nativeWords k := by
  change jordan value11 value11 = _
  rw [native_product_decode_11_11, productColumn_sum_11_11, decode_sum_columns]

def productCoeff_11_12 : Fin 27 → ℝ := ![0, 0, (-1/12), 0, 0, 0, (1/2), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (1/24), 0, 0, 0, (1/3), 0, 0, 0, (1/6), 0]
def productColumn_11_12 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, (-1/4), 0, 0, 0, (-1/16), 0, 0, 0, 0, (1/16), 0, 0, 0, (-1/4), 0, 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_11_12 :
    jordan value11 value12 = decode productColumn_11_12 := by
  simp only [value11_decode, value12_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_11_12, column11, column12, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_11_12 :
    productColumn_11_12 = ∑ k : Fin 27, productCoeff_11_12 k • columns k := by
  funext r
  change productColumn_11_12 r = ∑ k : Fin 27, productCoeff_11_12 k * columns k r
  fin_cases r <;> norm_num [productColumn_11_12, productCoeff_11_12, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_11_12 :
    jordan (nativeWords 11) (nativeWords 12) =
      ∑ k : Fin 27, productCoeff_11_12 k • nativeWords k := by
  change jordan value11 value12 = _
  rw [native_product_decode_11_12, productColumn_sum_11_12, decode_sum_columns]

def productCoeff_11_13 : Fin 27 → ℝ := ![0, 0, 0, (1/48), 0, (-1/4), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1/24), 0, 0, 0, 0, 0, (1/12), 0, 0, 0, (1/24)]
def productColumn_11_13 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (1/32), 0, 0, 0, 0, (1/32), 0, 0, 0, 0, 0, 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_11_13 :
    jordan value11 value13 = decode productColumn_11_13 := by
  simp only [value11_decode, value13_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_11_13, column11, column13, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_11_13 :
    productColumn_11_13 = ∑ k : Fin 27, productCoeff_11_13 k • columns k := by
  funext r
  change productColumn_11_13 r = ∑ k : Fin 27, productCoeff_11_13 k * columns k r
  fin_cases r <;> norm_num [productColumn_11_13, productCoeff_11_13, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_11_13 :
    jordan (nativeWords 11) (nativeWords 13) =
      ∑ k : Fin 27, productCoeff_11_13 k • nativeWords k := by
  change jordan value11 value13 = _
  rw [native_product_decode_11_13, productColumn_sum_11_13, decode_sum_columns]

def productCoeff_11_14 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, (1/2), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def productColumn_11_14 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, (-1/4), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1/4), 0, 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_11_14 :
    jordan value11 value14 = decode productColumn_11_14 := by
  simp only [value11_decode, value14_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_11_14, column11, column14, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_11_14 :
    productColumn_11_14 = ∑ k : Fin 27, productCoeff_11_14 k • columns k := by
  funext r
  change productColumn_11_14 r = ∑ k : Fin 27, productCoeff_11_14 k * columns k r
  fin_cases r <;> norm_num [productColumn_11_14, productCoeff_11_14, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_11_14 :
    jordan (nativeWords 11) (nativeWords 14) =
      ∑ k : Fin 27, productCoeff_11_14 k • nativeWords k := by
  change jordan value11 value14 = _
  rw [native_product_decode_11_14, productColumn_sum_11_14, decode_sum_columns]

def productCoeff_11_15 : Fin 27 → ℝ := ![0, 0, 0, (-1/48), 0, (-1/16), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (1/24), 0, 0, 0, 0, 0, (1/24), 0, 0, 0, (-1/24)]
def productColumn_11_15 : Fin 27 → ℝ := ![0, 0, 0, (1/32), 0, 0, 0, 0, (1/32), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1/32), 0, 0, 0, 0, (-1/32), 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_11_15 :
    jordan value11 value15 = decode productColumn_11_15 := by
  simp only [value11_decode, value15_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_11_15, column11, column15, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_11_15 :
    productColumn_11_15 = ∑ k : Fin 27, productCoeff_11_15 k • columns k := by
  funext r
  change productColumn_11_15 r = ∑ k : Fin 27, productCoeff_11_15 k * columns k r
  fin_cases r <;> norm_num [productColumn_11_15, productCoeff_11_15, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_11_15 :
    jordan (nativeWords 11) (nativeWords 15) =
      ∑ k : Fin 27, productCoeff_11_15 k • nativeWords k := by
  change jordan value11 value15 = _
  rw [native_product_decode_11_15, productColumn_sum_11_15, decode_sum_columns]

def productCoeff_11_16 : Fin 27 → ℝ := ![(5/12), 0, 0, 0, (-1/4), 0, 0, (-1/12), 0, (-1/12), 0, 0, 0, (-1/24), 0, (1/24), 0, 0, (-1/16), 0, (1/8), 0, 0, (1/24), 0, 0, 0]
def productColumn_11_16 : Fin 27 → ℝ := ![(1/8), (1/4), (1/8), 0, (-1/32), 0, 0, (-1/32), 0, 0, (1/16), (-1/16), 0, 0, (-1/32), 0, (1/8), (-1/32), 0, 0, (-1/32), (-1/16), 0, (1/32), 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_11_16 :
    jordan value11 value16 = decode productColumn_11_16 := by
  simp only [value11_decode, value16_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_11_16, column11, column16, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_11_16 :
    productColumn_11_16 = ∑ k : Fin 27, productCoeff_11_16 k • columns k := by
  funext r
  change productColumn_11_16 r = ∑ k : Fin 27, productCoeff_11_16 k * columns k r
  fin_cases r <;> norm_num [productColumn_11_16, productCoeff_11_16, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_11_16 :
    jordan (nativeWords 11) (nativeWords 16) =
      ∑ k : Fin 27, productCoeff_11_16 k • nativeWords k := by
  change jordan value11 value16 = _
  rw [native_product_decode_11_16, productColumn_sum_11_16, decode_sum_columns]

def productCoeff_11_17 : Fin 27 → ℝ := ![0, (-1/4), 0, 0, 0, 0, 0, 0, (-5/8), 0, 0, 0, (1/8), 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, (-5/2), 0, 0]
def productColumn_11_17 : Fin 27 → ℝ := ![0, 0, 0, 0, (-1/16), (-1/4), 0, (1/16), 0, 0, 0, 0, 0, 0, (-3/16), 0, 0, (3/16), 0, 0, (1/16), 0, 0, (1/16), 0, 0, (-1/4)]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_11_17 :
    jordan value11 value17 = decode productColumn_11_17 := by
  simp only [value11_decode, value17_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_11_17, column11, column17, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_11_17 :
    productColumn_11_17 = ∑ k : Fin 27, productCoeff_11_17 k • columns k := by
  funext r
  change productColumn_11_17 r = ∑ k : Fin 27, productCoeff_11_17 k * columns k r
  fin_cases r <;> norm_num [productColumn_11_17, productCoeff_11_17, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_11_17 :
    jordan (nativeWords 11) (nativeWords 17) =
      ∑ k : Fin 27, productCoeff_11_17 k • nativeWords k := by
  change jordan value11 value17 = _
  rw [native_product_decode_11_17, productColumn_sum_11_17, decode_sum_columns]

def productCoeff_11_18 : Fin 27 → ℝ := ![0, 0, 0, (1/8), 0, (1/2), 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, (-1/4), 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1/4)]
def productColumn_11_18 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, (1/8), 0, 0, (1/4), 0, 0, 0, (1/16), 0, 0, 0, 0, (1/16), 0, 0, 0, (-1/4), 0, 0, (-1/8), 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_11_18 :
    jordan value11 value18 = decode productColumn_11_18 := by
  simp only [value11_decode, value18_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_11_18, column11, column18, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_11_18 :
    productColumn_11_18 = ∑ k : Fin 27, productCoeff_11_18 k • columns k := by
  funext r
  change productColumn_11_18 r = ∑ k : Fin 27, productCoeff_11_18 k * columns k r
  fin_cases r <;> norm_num [productColumn_11_18, productCoeff_11_18, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_11_18 :
    jordan (nativeWords 11) (nativeWords 18) =
      ∑ k : Fin 27, productCoeff_11_18 k • nativeWords k := by
  change jordan value11 value18 = _
  rw [native_product_decode_11_18, productColumn_sum_11_18, decode_sum_columns]

def productCoeff_11_19 : Fin 27 → ℝ := ![0, 0, (3/16), 0, 0, 0, (-1/8), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1/16), 0, 0, 0, 0, 0, 0, 0, (1/4), 0]
def productColumn_11_19 : Fin 27 → ℝ := ![0, 0, 0, (1/16), 0, 0, 0, 0, (-1/16), 0, 0, 0, (1/16), (1/32), 0, 0, 0, 0, (-1/32), (1/16), 0, 0, 0, 0, (-1/16), 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_11_19 :
    jordan value11 value19 = decode productColumn_11_19 := by
  simp only [value11_decode, value19_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_11_19, column11, column19, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_11_19 :
    productColumn_11_19 = ∑ k : Fin 27, productCoeff_11_19 k • columns k := by
  funext r
  change productColumn_11_19 r = ∑ k : Fin 27, productCoeff_11_19 k * columns k r
  fin_cases r <;> norm_num [productColumn_11_19, productCoeff_11_19, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_11_19 :
    jordan (nativeWords 11) (nativeWords 19) =
      ∑ k : Fin 27, productCoeff_11_19 k • nativeWords k := by
  change jordan value11 value19 = _
  rw [native_product_decode_11_19, productColumn_sum_11_19, decode_sum_columns]

def productCoeff_11_20 : Fin 27 → ℝ := ![0, 0, 0, (1/8), 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def productColumn_11_20 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, (3/8), 0, 0, 0, 0, 0, (-1/8), 0, 0, 0, 0, 0, 0, (-3/8), 0, 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_11_20 :
    jordan value11 value20 = decode productColumn_11_20 := by
  simp only [value11_decode, value20_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_11_20, column11, column20, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_11_20 :
    productColumn_11_20 = ∑ k : Fin 27, productCoeff_11_20 k • columns k := by
  funext r
  change productColumn_11_20 r = ∑ k : Fin 27, productCoeff_11_20 k * columns k r
  fin_cases r <;> norm_num [productColumn_11_20, productCoeff_11_20, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_11_20 :
    jordan (nativeWords 11) (nativeWords 20) =
      ∑ k : Fin 27, productCoeff_11_20 k • nativeWords k := by
  change jordan value11 value20 = _
  rw [native_product_decode_11_20, productColumn_sum_11_20, decode_sum_columns]

def productCoeff_11_21 : Fin 27 → ℝ := ![0, (-3/32), 0, 0, 0, 0, 0, 0, (-1/16), 0, 0, 0, (1/32), 0, 0, 0, 0, 0, 0, (1/16), 0, 0, 0, 0, (-1/8), 0, 0]
def productColumn_11_21 : Fin 27 → ℝ := ![(1/32), 0, (-1/32), 0, (-1/64), 0, 0, (1/64), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (1/64), 0, 0, (1/64), 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_11_21 :
    jordan value11 value21 = decode productColumn_11_21 := by
  simp only [value11_decode, value21_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_11_21, column11, column21, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_11_21 :
    productColumn_11_21 = ∑ k : Fin 27, productCoeff_11_21 k • columns k := by
  funext r
  change productColumn_11_21 r = ∑ k : Fin 27, productCoeff_11_21 k * columns k r
  fin_cases r <;> norm_num [productColumn_11_21, productCoeff_11_21, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_11_21 :
    jordan (nativeWords 11) (nativeWords 21) =
      ∑ k : Fin 27, productCoeff_11_21 k • nativeWords k := by
  change jordan value11 value21 = _
  rw [native_product_decode_11_21, productColumn_sum_11_21, decode_sum_columns]

def productCoeff_11_22 : Fin 27 → ℝ := ![(-11/24), 0, 0, 0, (1/8), 0, 0, (11/48), 0, (1/6), 0, 0, 0, (-1/24), 0, (-5/24), 0, 0, (-1/16), 0, 0, 0, 0, (-1/12), 0, 0, 0]
def productColumn_11_22 : Fin 27 → ℝ := ![0, 0, 0, 0, (1/32), 0, 0, (1/32), 0, 0, 0, 0, 0, 0, (3/32), 0, 0, (3/32), 0, 0, (1/32), 0, 0, (-1/32), 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_11_22 :
    jordan value11 value22 = decode productColumn_11_22 := by
  simp only [value11_decode, value22_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_11_22, column11, column22, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_11_22 :
    productColumn_11_22 = ∑ k : Fin 27, productCoeff_11_22 k • columns k := by
  funext r
  change productColumn_11_22 r = ∑ k : Fin 27, productCoeff_11_22 k * columns k r
  fin_cases r <;> norm_num [productColumn_11_22, productCoeff_11_22, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_11_22 :
    jordan (nativeWords 11) (nativeWords 22) =
      ∑ k : Fin 27, productCoeff_11_22 k • nativeWords k := by
  change jordan value11 value22 = _
  rw [native_product_decode_11_22, productColumn_sum_11_22, decode_sum_columns]

def productCoeff_11_23 : Fin 27 → ℝ := ![0, 0, 0, (3/4), 0, (3/8), 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, (-1/2), 0, 0, 0, 0, 0, (1/4), 0, 0, 0, (-1/2)]
def productColumn_11_23 : Fin 27 → ℝ := ![0, 0, 0, (1/16), 0, 0, (1/4), 0, (1/16), (5/4), 0, 0, 0, (3/16), 0, (-1/2), 0, 0, (3/16), (-1/16), 0, 0, (-5/4), 0, (-1/16), (-1/4), 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_11_23 :
    jordan value11 value23 = decode productColumn_11_23 := by
  simp only [value11_decode, value23_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_11_23, column11, column23, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_11_23 :
    productColumn_11_23 = ∑ k : Fin 27, productCoeff_11_23 k • columns k := by
  funext r
  change productColumn_11_23 r = ∑ k : Fin 27, productCoeff_11_23 k * columns k r
  fin_cases r <;> norm_num [productColumn_11_23, productCoeff_11_23, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_11_23 :
    jordan (nativeWords 11) (nativeWords 23) =
      ∑ k : Fin 27, productCoeff_11_23 k • nativeWords k := by
  change jordan value11 value23 = _
  rw [native_product_decode_11_23, productColumn_sum_11_23, decode_sum_columns]

def productCoeff_11_24 : Fin 27 → ℝ := ![0, 0, (-1/32), 0, 0, 0, 0, 0, 0, 0, (1/8), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def productColumn_11_24 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1/32), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_11_24 :
    jordan value11 value24 = decode productColumn_11_24 := by
  simp only [value11_decode, value24_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_11_24, column11, column24, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_11_24 :
    productColumn_11_24 = ∑ k : Fin 27, productCoeff_11_24 k • columns k := by
  funext r
  change productColumn_11_24 r = ∑ k : Fin 27, productCoeff_11_24 k * columns k r
  fin_cases r <;> norm_num [productColumn_11_24, productCoeff_11_24, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_11_24 :
    jordan (nativeWords 11) (nativeWords 24) =
      ∑ k : Fin 27, productCoeff_11_24 k • nativeWords k := by
  change jordan value11 value24 = _
  rw [native_product_decode_11_24, productColumn_sum_11_24, decode_sum_columns]

def productCoeff_11_25 : Fin 27 → ℝ := ![0, (1/16), 0, 0, 0, 0, 0, 0, (-1/32), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (1/16), 0, 0, 0, 0, 0, 0, 0]
def productColumn_11_25 : Fin 27 → ℝ := ![(-1/16), 0, (1/16), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1/64), 0, 0, (1/64), 0, 0, 0, 0, 0, 0, 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_11_25 :
    jordan value11 value25 = decode productColumn_11_25 := by
  simp only [value11_decode, value25_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_11_25, column11, column25, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_11_25 :
    productColumn_11_25 = ∑ k : Fin 27, productCoeff_11_25 k • columns k := by
  funext r
  change productColumn_11_25 r = ∑ k : Fin 27, productCoeff_11_25 k * columns k r
  fin_cases r <;> norm_num [productColumn_11_25, productCoeff_11_25, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_11_25 :
    jordan (nativeWords 11) (nativeWords 25) =
      ∑ k : Fin 27, productCoeff_11_25 k • nativeWords k := by
  change jordan value11 value25 = _
  rw [native_product_decode_11_25, productColumn_sum_11_25, decode_sum_columns]

def productCoeff_11_26 : Fin 27 → ℝ := ![(-13/24), 0, 0, 0, (1/4), 0, 0, (13/48), 0, (5/24), 0, 0, 0, (-5/24), 0, (-5/12), 0, 0, (-1/8), 0, 0, 0, 0, (-5/48), 0, 0, 0]
def productColumn_11_26 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1/16), 0, 0, (5/32), 0, 0, (5/32), 0, 0, 0, 0, 0, 0, 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_11_26 :
    jordan value11 value26 = decode productColumn_11_26 := by
  simp only [value11_decode, value26_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_11_26, column11, column26, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_11_26 :
    productColumn_11_26 = ∑ k : Fin 27, productCoeff_11_26 k • columns k := by
  funext r
  change productColumn_11_26 r = ∑ k : Fin 27, productCoeff_11_26 k * columns k r
  fin_cases r <;> norm_num [productColumn_11_26, productCoeff_11_26, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_11_26 :
    jordan (nativeWords 11) (nativeWords 26) =
      ∑ k : Fin 27, productCoeff_11_26 k • nativeWords k := by
  change jordan value11 value26 = _
  rw [native_product_decode_11_26, productColumn_sum_11_26, decode_sum_columns]

end
end Glennie.Compact.NativeWordTableR01
