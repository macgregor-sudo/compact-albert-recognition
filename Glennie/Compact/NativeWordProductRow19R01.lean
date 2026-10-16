/- Concrete native Jordan product certificate for word row 19. -/
module
public import Glennie.Compact.NativeWordProductCommonR01

@[expose] public section
namespace Glennie.Compact.NativeWordTableR01
noncomputable section
open Glennie AlbertGeometry.NativeOperatorTrace
open scoped BigOperators Matrix
set_option autoImplicit false

def productCoeff_19_19 : Fin 27 → ℝ := ![(1/6), 0, 0, 0, (-1/8), 0, 0, (11/48), 0, (11/48), 0, 0, 0, (1/12), 0, (1/6), 0, 0, (1/8), 0, (1/8), 0, 0, (-5/24), 0, 0, 0]
def productColumn_19_19 : Fin 27 → ℝ := ![(5/8), (1/4), (5/8), 0, (-1/8), (-1/8), 0, (1/8), 0, 0, (-1/8), (-1/16), 0, 0, (1/16), 0, (-1/16), (1/16), 0, 0, (-1/8), (1/8), 0, (-1/8), 0, 0, (1/8)]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_19_19 :
    jordan value19 value19 = decode productColumn_19_19 := by
  simp only [value19_decode, value19_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_19_19, column19, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_19_19 :
    productColumn_19_19 = ∑ k : Fin 27, productCoeff_19_19 k • columns k := by
  funext r
  change productColumn_19_19 r = ∑ k : Fin 27, productCoeff_19_19 k * columns k r
  fin_cases r <;> norm_num [productColumn_19_19, productCoeff_19_19, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_19_19 :
    jordan (nativeWords 19) (nativeWords 19) =
      ∑ k : Fin 27, productCoeff_19_19 k • nativeWords k := by
  change jordan value19 value19 = _
  rw [native_product_decode_19_19, productColumn_sum_19_19, decode_sum_columns]

def productCoeff_19_20 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, 0, 0, (-11/8), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (13/4), 0, 0, 0, 0, 0, 0, 0]
def productColumn_19_20 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, (-1/8), 0, (-1/8), 0, 0, 0, 0, 0, 0, (-15/16), 0, 0, (15/16), 0, 0, 0, 0, 0, (-1/8), 0, 0, (-1/8)]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_19_20 :
    jordan value19 value20 = decode productColumn_19_20 := by
  simp only [value19_decode, value20_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_19_20, column19, column20, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_19_20 :
    productColumn_19_20 = ∑ k : Fin 27, productCoeff_19_20 k • columns k := by
  funext r
  change productColumn_19_20 r = ∑ k : Fin 27, productCoeff_19_20 k * columns k r
  fin_cases r <;> norm_num [productColumn_19_20, productCoeff_19_20, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_19_20 :
    jordan (nativeWords 19) (nativeWords 20) =
      ∑ k : Fin 27, productCoeff_19_20 k • nativeWords k := by
  change jordan value19 value20 = _
  rw [native_product_decode_19_20, productColumn_sum_19_20, decode_sum_columns]

def productCoeff_19_21 : Fin 27 → ℝ := ![0, 0, 0, (1/32), 0, (-7/32), 0, 0, 0, 0, 0, (-3/16), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (1/8), 0, 0, 0, (1/16)]
def productColumn_19_21 : Fin 27 → ℝ := ![0, 0, 0, (-5/64), 0, 0, (-1/64), 0, (1/64), (-1/64), 0, 0, 0, (1/32), 0, (-1/32), 0, 0, (1/32), (5/64), 0, 0, (1/64), 0, (-1/64), (1/64), 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_19_21 :
    jordan value19 value21 = decode productColumn_19_21 := by
  simp only [value19_decode, value21_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_19_21, column19, column21, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_19_21 :
    productColumn_19_21 = ∑ k : Fin 27, productCoeff_19_21 k • columns k := by
  funext r
  change productColumn_19_21 r = ∑ k : Fin 27, productCoeff_19_21 k * columns k r
  fin_cases r <;> norm_num [productColumn_19_21, productCoeff_19_21, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_19_21 :
    jordan (nativeWords 19) (nativeWords 21) =
      ∑ k : Fin 27, productCoeff_19_21 k • nativeWords k := by
  change jordan value19 value21 = _
  rw [native_product_decode_19_21, productColumn_sum_19_21, decode_sum_columns]

def productCoeff_19_22 : Fin 27 → ℝ := ![0, 0, (3/16), 0, 0, 0, (-5/16), 0, 0, 0, (-3/8), 0, 0, 0, 0, 0, 0, (-1/16), 0, 0, 0, (3/2), 0, 0, 0, 0, 0]
def productColumn_19_22 : Fin 27 → ℝ := ![0, 0, 0, (-1/32), 0, 0, (-7/32), 0, (-1/32), (11/32), 0, 0, (1/16), (-5/32), 0, 0, 0, 0, (5/32), (-1/32), 0, 0, (11/32), 0, (-1/32), (-7/32), 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_19_22 :
    jordan value19 value22 = decode productColumn_19_22 := by
  simp only [value19_decode, value22_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_19_22, column19, column22, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_19_22 :
    productColumn_19_22 = ∑ k : Fin 27, productCoeff_19_22 k • columns k := by
  funext r
  change productColumn_19_22 r = ∑ k : Fin 27, productCoeff_19_22 k * columns k r
  fin_cases r <;> norm_num [productColumn_19_22, productCoeff_19_22, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_19_22 :
    jordan (nativeWords 19) (nativeWords 22) =
      ∑ k : Fin 27, productCoeff_19_22 k • nativeWords k := by
  change jordan value19 value22 = _
  rw [native_product_decode_19_22, productColumn_sum_19_22, decode_sum_columns]

def productCoeff_19_23 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, 0, 0, (-5/2), 0, 0, 0, (-3/8), 0, (3/8), 0, 0, 0, 0, (21/4), 0, 0, 0, 0, 0, 0, 0]
def productColumn_19_23 : Fin 27 → ℝ := ![0, 0, 0, 0, (3/16), (-1/16), 0, (-1/16), 0, 0, (-3/16), 0, 0, 0, (-11/8), 0, 0, (11/8), 0, 0, (-3/16), (-3/16), 0, (-1/16), 0, 0, (-1/16)]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_19_23 :
    jordan value19 value23 = decode productColumn_19_23 := by
  simp only [value19_decode, value23_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_19_23, column19, column23, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_19_23 :
    productColumn_19_23 = ∑ k : Fin 27, productCoeff_19_23 k • columns k := by
  funext r
  change productColumn_19_23 r = ∑ k : Fin 27, productCoeff_19_23 k * columns k r
  fin_cases r <;> norm_num [productColumn_19_23, productCoeff_19_23, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_19_23 :
    jordan (nativeWords 19) (nativeWords 23) =
      ∑ k : Fin 27, productCoeff_19_23 k • nativeWords k := by
  change jordan value19 value23 = _
  rw [native_product_decode_19_23, productColumn_sum_19_23, decode_sum_columns]

def productCoeff_19_24 : Fin 27 → ℝ := ![0, 0, 0, 0, (1/32), 0, 0, 0, 0, (-3/32), 0, 0, 0, (-1/16), 0, 0, 0, 0, (-1/16), 0, (1/16), 0, 0, (1/32), 0, 0, 0]
def productColumn_19_24 : Fin 27 → ℝ := ![(-1/32), (-1/16), (-1/32), 0, (1/32), 0, 0, (-1/32), 0, 0, 0, 0, 0, 0, (-1/64), 0, (1/32), (-1/64), 0, 0, (1/32), 0, 0, (1/32), 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_19_24 :
    jordan value19 value24 = decode productColumn_19_24 := by
  simp only [value19_decode, value24_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_19_24, column19, column24, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_19_24 :
    productColumn_19_24 = ∑ k : Fin 27, productCoeff_19_24 k • columns k := by
  funext r
  change productColumn_19_24 r = ∑ k : Fin 27, productCoeff_19_24 k * columns k r
  fin_cases r <;> norm_num [productColumn_19_24, productCoeff_19_24, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_19_24 :
    jordan (nativeWords 19) (nativeWords 24) =
      ∑ k : Fin 27, productCoeff_19_24 k • nativeWords k := by
  change jordan value19 value24 = _
  rw [native_product_decode_19_24, productColumn_sum_19_24, decode_sum_columns]

def productCoeff_19_25 : Fin 27 → ℝ := ![0, 0, 0, (-1/96), 0, (5/16), 0, 0, 0, 0, 0, (1/4), 0, 0, 0, 0, (-1/24), 0, 0, 0, 0, 0, (-1/6), 0, 0, 0, (-1/12)]
def productColumn_19_25 : Fin 27 → ℝ := ![0, 0, 0, (3/32), 0, 0, (1/32), 0, (-1/32), (1/32), 0, 0, 0, (-1/32), 0, (1/32), 0, 0, (-1/32), (-3/32), 0, 0, (-1/32), 0, (1/32), (-1/32), 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_19_25 :
    jordan value19 value25 = decode productColumn_19_25 := by
  simp only [value19_decode, value25_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_19_25, column19, column25, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_19_25 :
    productColumn_19_25 = ∑ k : Fin 27, productCoeff_19_25 k • columns k := by
  funext r
  change productColumn_19_25 r = ∑ k : Fin 27, productCoeff_19_25 k * columns k r
  fin_cases r <;> norm_num [productColumn_19_25, productCoeff_19_25, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_19_25 :
    jordan (nativeWords 19) (nativeWords 25) =
      ∑ k : Fin 27, productCoeff_19_25 k • nativeWords k := by
  change jordan value19 value25 = _
  rw [native_product_decode_19_25, productColumn_sum_19_25, decode_sum_columns]

def productCoeff_19_26 : Fin 27 → ℝ := ![0, 0, (5/48), 0, 0, 0, (3/8), 0, 0, 0, (1/2), 0, 0, 0, 0, 0, 0, (-1/12), 0, 0, 0, (4/3), 0, 0, 0, (-5/6), 0]
def productColumn_19_26 : Fin 27 → ℝ := ![0, 0, 0, (1/16), 0, 0, (-5/16), 0, (1/16), (3/16), 0, 0, (-1/16), (-1/8), 0, 0, 0, 0, (1/8), (1/16), 0, 0, (3/16), 0, (1/16), (-5/16), 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_19_26 :
    jordan value19 value26 = decode productColumn_19_26 := by
  simp only [value19_decode, value26_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_19_26, column19, column26, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_19_26 :
    productColumn_19_26 = ∑ k : Fin 27, productCoeff_19_26 k • columns k := by
  funext r
  change productColumn_19_26 r = ∑ k : Fin 27, productCoeff_19_26 k * columns k r
  fin_cases r <;> norm_num [productColumn_19_26, productCoeff_19_26, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_19_26 :
    jordan (nativeWords 19) (nativeWords 26) =
      ∑ k : Fin 27, productCoeff_19_26 k • nativeWords k := by
  change jordan value19 value26 = _
  rw [native_product_decode_19_26, productColumn_sum_19_26, decode_sum_columns]

end
end Glennie.Compact.NativeWordTableR01
