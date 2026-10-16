/- Concrete native Jordan product certificate for word row 22. -/
module
public import Glennie.Compact.NativeWordProductCommonR01

@[expose] public section
namespace Glennie.Compact.NativeWordTableR01
noncomputable section
open Glennie AlbertGeometry.NativeOperatorTrace
open scoped BigOperators Matrix
set_option autoImplicit false

def productCoeff_22_22 : Fin 27 → ℝ := ![(1/2), 0, 0, 0, (33/16), 0, 0, (11/16), 0, (-1/8), 0, 0, 0, (1/4), 0, (-1/4), 0, 0, (-15/8), 0, (3/8), 0, 0, (1/8), 0, 0, 0]
def productColumn_22_22 : Fin 27 → ℝ := ![(19/16), (17/8), (19/16), 0, 0, (3/16), 0, 0, 0, 0, (5/16), (-15/16), 0, 0, 0, 0, (1/2), 0, 0, 0, 0, (-5/16), 0, 0, 0, 0, (-3/16)]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_22_22 :
    jordan value22 value22 = decode productColumn_22_22 := by
  simp only [value22_decode, value22_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_22_22, column22, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_22_22 :
    productColumn_22_22 = ∑ k : Fin 27, productCoeff_22_22 k • columns k := by
  funext r
  change productColumn_22_22 r = ∑ k : Fin 27, productCoeff_22_22 k * columns k r
  fin_cases r <;> norm_num [productColumn_22_22, productCoeff_22_22, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_22_22 :
    jordan (nativeWords 22) (nativeWords 22) =
      ∑ k : Fin 27, productCoeff_22_22 k • nativeWords k := by
  change jordan value22 value22 = _
  rw [native_product_decode_22_22, productColumn_sum_22_22, decode_sum_columns]

def productCoeff_22_23 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, (-99/8), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (39/4), 0, 0, 0, 0]
def productColumn_22_23 : Fin 27 → ℝ := ![0, 0, 0, (-57/16), 0, 0, 0, 0, (39/16), 0, 0, 0, 0, (39/16), 0, 0, 0, 0, (39/16), (57/16), 0, 0, 0, 0, (-39/16), 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_22_23 :
    jordan value22 value23 = decode productColumn_22_23 := by
  simp only [value22_decode, value23_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_22_23, column22, column23, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_22_23 :
    productColumn_22_23 = ∑ k : Fin 27, productCoeff_22_23 k • columns k := by
  funext r
  change productColumn_22_23 r = ∑ k : Fin 27, productCoeff_22_23 k * columns k r
  fin_cases r <;> norm_num [productColumn_22_23, productCoeff_22_23, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_22_23 :
    jordan (nativeWords 22) (nativeWords 23) =
      ∑ k : Fin 27, productCoeff_22_23 k • nativeWords k := by
  change jordan value22 value23 = _
  rw [native_product_decode_22_23, productColumn_sum_22_23, decode_sum_columns]

def productCoeff_22_24 : Fin 27 → ℝ := ![0, 0, (1/12), 0, 0, 0, (1/32), 0, 0, 0, (1/16), 0, 0, 0, 0, 0, 0, (-1/24), 0, 0, 0, (-11/24), 0, 0, 0, (-7/24), 0]
def productColumn_22_24 : Fin 27 → ℝ := ![0, 0, 0, (1/64), 0, 0, 0, 0, (1/64), 0, 0, 0, 0, (5/64), 0, 0, 0, 0, (-5/64), (1/64), 0, 0, 0, 0, (1/64), 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_22_24 :
    jordan value22 value24 = decode productColumn_22_24 := by
  simp only [value22_decode, value24_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_22_24, column22, column24, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_22_24 :
    productColumn_22_24 = ∑ k : Fin 27, productCoeff_22_24 k • columns k := by
  funext r
  change productColumn_22_24 r = ∑ k : Fin 27, productCoeff_22_24 k * columns k r
  fin_cases r <;> norm_num [productColumn_22_24, productCoeff_22_24, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_22_24 :
    jordan (nativeWords 22) (nativeWords 24) =
      ∑ k : Fin 27, productCoeff_22_24 k • nativeWords k := by
  change jordan value22 value24 = _
  rw [native_product_decode_22_24, productColumn_sum_22_24, decode_sum_columns]

def productCoeff_22_25 : Fin 27 → ℝ := ![0, (5/32), 0, 0, 0, 0, 0, 0, (7/32), 0, 0, 0, (-1/32), 0, (-1/32), 0, 0, 0, 0, (-5/8), 0, 0, 0, 0, (-1/2), 0, 0]
def productColumn_22_25 : Fin 27 → ℝ := ![(-1/32), 0, (1/32), 0, (1/64), (-1/64), 0, (3/64), 0, 0, (1/64), 0, 0, 0, (13/64), 0, 0, (-13/64), 0, 0, (-1/64), (1/64), 0, (3/64), 0, 0, (-1/64)]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_22_25 :
    jordan value22 value25 = decode productColumn_22_25 := by
  simp only [value22_decode, value25_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_22_25, column22, column25, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_22_25 :
    productColumn_22_25 = ∑ k : Fin 27, productCoeff_22_25 k • columns k := by
  funext r
  change productColumn_22_25 r = ∑ k : Fin 27, productCoeff_22_25 k * columns k r
  fin_cases r <;> norm_num [productColumn_22_25, productCoeff_22_25, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_22_25 :
    jordan (nativeWords 22) (nativeWords 25) =
      ∑ k : Fin 27, productCoeff_22_25 k • nativeWords k := by
  change jordan value22 value25 = _
  rw [native_product_decode_22_25, productColumn_sum_22_25, decode_sum_columns]

def productCoeff_22_26 : Fin 27 → ℝ := ![(1/4), 0, 0, 0, (57/16), 0, 0, (5/8), 0, (-3/16), 0, 0, 0, (1/2), 0, (1/4), 0, 0, (-33/16), 0, (-3/16), 0, 0, (3/16), 0, 0, 0]
def productColumn_22_26 : Fin 27 → ℝ := ![(15/16), (15/8), (15/16), 0, (-1/32), (5/32), 0, (1/32), 0, 0, (3/32), (-17/16), 0, 0, (-5/32), 0, 0, (-5/32), 0, 0, (-1/32), (-3/32), 0, (-1/32), 0, 0, (-5/32)]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_22_26 :
    jordan value22 value26 = decode productColumn_22_26 := by
  simp only [value22_decode, value26_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_22_26, column22, column26, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_22_26 :
    productColumn_22_26 = ∑ k : Fin 27, productCoeff_22_26 k • columns k := by
  funext r
  change productColumn_22_26 r = ∑ k : Fin 27, productCoeff_22_26 k * columns k r
  fin_cases r <;> norm_num [productColumn_22_26, productCoeff_22_26, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_22_26 :
    jordan (nativeWords 22) (nativeWords 26) =
      ∑ k : Fin 27, productCoeff_22_26 k • nativeWords k := by
  change jordan value22 value26 = _
  rw [native_product_decode_22_26, productColumn_sum_22_26, decode_sum_columns]

end
end Glennie.Compact.NativeWordTableR01
