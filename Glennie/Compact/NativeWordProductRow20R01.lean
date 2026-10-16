/- Concrete native Jordan product certificate for word row 20. -/
module
public import Glennie.Compact.NativeWordProductCommonR01

@[expose] public section
namespace Glennie.Compact.NativeWordTableR01
noncomputable section
open Glennie AlbertGeometry.NativeOperatorTrace
open scoped BigOperators Matrix
set_option autoImplicit false

def productCoeff_20_20 : Fin 27 → ℝ := ![6, 0, 0, 0, (-33/4), 0, 0, 0, 0, (-11/4), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (13/2), 0, 0, 0, 0, 0, 0]
def productColumn_20_20 : Fin 27 → ℝ := ![(21/4), (1/2), (21/4), 0, 0, 0, 0, 0, 0, 0, (1/2), 0, 0, 0, 0, 0, (15/4), 0, 0, 0, 0, (-1/2), 0, 0, 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_20_20 :
    jordan value20 value20 = decode productColumn_20_20 := by
  simp only [value20_decode, value20_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_20_20, column20, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_20_20 :
    productColumn_20_20 = ∑ k : Fin 27, productCoeff_20_20 k • columns k := by
  funext r
  change productColumn_20_20 r = ∑ k : Fin 27, productCoeff_20_20 k * columns k r
  fin_cases r <;> norm_num [productColumn_20_20, productCoeff_20_20, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_20_20 :
    jordan (nativeWords 20) (nativeWords 20) =
      ∑ k : Fin 27, productCoeff_20_20 k • nativeWords k := by
  change jordan value20 value20 = _
  rw [native_product_decode_20_20, productColumn_sum_20_20, decode_sum_columns]

def productCoeff_20_21 : Fin 27 → ℝ := ![0, 0, (-3/16), 0, 0, 0, (5/16), 0, 0, 0, (3/8), 0, 0, 0, 0, 0, 0, (1/16), 0, 0, 0, (7/4), 0, 0, 0, 0, 0]
def productColumn_20_21 : Fin 27 → ℝ := ![0, 0, 0, (1/32), 0, 0, (-3/16), 0, (1/32), (1/16), 0, 0, (-1/16), (-1/4), 0, 0, 0, 0, (1/4), (1/32), 0, 0, (1/16), 0, (1/32), (-3/16), 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_20_21 :
    jordan value20 value21 = decode productColumn_20_21 := by
  simp only [value20_decode, value21_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_20_21, column20, column21, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_20_21 :
    productColumn_20_21 = ∑ k : Fin 27, productCoeff_20_21 k • columns k := by
  funext r
  change productColumn_20_21 r = ∑ k : Fin 27, productCoeff_20_21 k * columns k r
  fin_cases r <;> norm_num [productColumn_20_21, productCoeff_20_21, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_20_21 :
    jordan (nativeWords 20) (nativeWords 21) =
      ∑ k : Fin 27, productCoeff_20_21 k • nativeWords k := by
  change jordan value20 value21 = _
  rw [native_product_decode_20_21, productColumn_sum_20_21, decode_sum_columns]

def productCoeff_20_22 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, (-33/8), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (13/4), 0, 0, 0, 0]
def productColumn_20_22 : Fin 27 → ℝ := ![0, 0, 0, (-19/16), 0, 0, 0, 0, (13/16), 0, 0, 0, 0, (13/16), 0, 0, 0, 0, (13/16), (19/16), 0, 0, 0, 0, (-13/16), 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_20_22 :
    jordan value20 value22 = decode productColumn_20_22 := by
  simp only [value20_decode, value22_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_20_22, column20, column22, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_20_22 :
    productColumn_20_22 = ∑ k : Fin 27, productCoeff_20_22 k • columns k := by
  funext r
  change productColumn_20_22 r = ∑ k : Fin 27, productCoeff_20_22 k * columns k r
  fin_cases r <;> norm_num [productColumn_20_22, productCoeff_20_22, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_20_22 :
    jordan (nativeWords 20) (nativeWords 22) =
      ∑ k : Fin 27, productCoeff_20_22 k • nativeWords k := by
  change jordan value20 value22 = _
  rw [native_product_decode_20_22, productColumn_sum_20_22, decode_sum_columns]

def productCoeff_20_23 : Fin 27 → ℝ := ![17, 0, 0, 0, (-33/2), 0, 0, (-11/2), 0, -8, 0, 0, 0, (-1/2), 0, (1/2), 0, 0, (15/4), 0, 9, 0, 0, 3, 0, 0, 0]
def productColumn_20_23 : Fin 27 → ℝ := ![11, 2, 11, 0, (19/8), (5/4), 0, (-13/8), 0, 0, (5/2), (17/4), 0, 0, (-13/8), 0, 7, (-13/8), 0, 0, (19/8), (-5/2), 0, (13/8), 0, 0, (-5/4)]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_20_23 :
    jordan value20 value23 = decode productColumn_20_23 := by
  simp only [value20_decode, value23_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_20_23, column20, column23, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_20_23 :
    productColumn_20_23 = ∑ k : Fin 27, productCoeff_20_23 k • columns k := by
  funext r
  change productColumn_20_23 r = ∑ k : Fin 27, productCoeff_20_23 k * columns k r
  fin_cases r <;> norm_num [productColumn_20_23, productCoeff_20_23, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_20_23 :
    jordan (nativeWords 20) (nativeWords 23) =
      ∑ k : Fin 27, productCoeff_20_23 k • nativeWords k := by
  change jordan value20 value23 = _
  rw [native_product_decode_20_23, productColumn_sum_20_23, decode_sum_columns]

def productCoeff_20_24 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (1/2), 0, 0]
def productColumn_20_24 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, (1/16), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (1/16)]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_20_24 :
    jordan value20 value24 = decode productColumn_20_24 := by
  simp only [value20_decode, value24_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_20_24, column20, column24, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_20_24 :
    productColumn_20_24 = ∑ k : Fin 27, productCoeff_20_24 k • columns k := by
  funext r
  change productColumn_20_24 r = ∑ k : Fin 27, productCoeff_20_24 k * columns k r
  fin_cases r <;> norm_num [productColumn_20_24, productCoeff_20_24, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_20_24 :
    jordan (nativeWords 20) (nativeWords 24) =
      ∑ k : Fin 27, productCoeff_20_24 k • nativeWords k := by
  change jordan value20 value24 = _
  rw [native_product_decode_20_24, productColumn_sum_20_24, decode_sum_columns]

def productCoeff_20_25 : Fin 27 → ℝ := ![0, 0, (1/48), 0, 0, 0, (-3/8), 0, 0, 0, (-1/2), 0, 0, 0, 0, 0, 0, (1/48), 0, 0, 0, (-1/3), 0, 0, 0, (13/12), 0]
def productColumn_20_25 : Fin 27 → ℝ := ![0, 0, 0, (-1/16), 0, 0, (3/16), 0, (-1/8), (-1/8), 0, 0, (1/16), (1/32), 0, 0, 0, 0, (-1/32), (-1/16), 0, 0, (-1/8), 0, (-1/8), (3/16), 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_20_25 :
    jordan value20 value25 = decode productColumn_20_25 := by
  simp only [value20_decode, value25_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_20_25, column20, column25, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_20_25 :
    productColumn_20_25 = ∑ k : Fin 27, productCoeff_20_25 k • columns k := by
  funext r
  change productColumn_20_25 r = ∑ k : Fin 27, productCoeff_20_25 k * columns k r
  fin_cases r <;> norm_num [productColumn_20_25, productCoeff_20_25, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_20_25 :
    jordan (nativeWords 20) (nativeWords 25) =
      ∑ k : Fin 27, productCoeff_20_25 k • nativeWords k := by
  change jordan value20 value25 = _
  rw [native_product_decode_20_25, productColumn_sum_20_25, decode_sum_columns]

def productCoeff_20_26 : Fin 27 → ℝ := ![0, 0, 0, (-1/8), 0, (-3/4), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (1/4), 0, 0, 0, 0, 0, 1, 0, 0, 0, (1/4)]
def productColumn_20_26 : Fin 27 → ℝ := ![0, 0, 0, (-7/8), 0, 0, (-1/8), 0, (1/4), 0, 0, 0, 0, (3/16), 0, 0, 0, 0, (3/16), (7/8), 0, 0, 0, 0, (-1/4), (1/8), 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_20_26 :
    jordan value20 value26 = decode productColumn_20_26 := by
  simp only [value20_decode, value26_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_20_26, column20, column26, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_20_26 :
    productColumn_20_26 = ∑ k : Fin 27, productCoeff_20_26 k • columns k := by
  funext r
  change productColumn_20_26 r = ∑ k : Fin 27, productCoeff_20_26 k * columns k r
  fin_cases r <;> norm_num [productColumn_20_26, productCoeff_20_26, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_20_26 :
    jordan (nativeWords 20) (nativeWords 26) =
      ∑ k : Fin 27, productCoeff_20_26 k • nativeWords k := by
  change jordan value20 value26 = _
  rw [native_product_decode_20_26, productColumn_sum_20_26, decode_sum_columns]

end
end Glennie.Compact.NativeWordTableR01
