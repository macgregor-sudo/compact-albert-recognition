/- Concrete native Jordan product certificate for word row 24. -/
module
public import Glennie.Compact.NativeWordProductCommonR01

@[expose] public section
namespace Glennie.Compact.NativeWordTableR01
noncomputable section
open Glennie AlbertGeometry.NativeOperatorTrace
open scoped BigOperators Matrix
set_option autoImplicit false

def productCoeff_24_24 : Fin 27 → ℝ := ![0, 0, 0, 0, (3/64), 0, 0, 0, 0, (1/64), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1/32), 0, 0, 0, 0, 0, 0]
def productColumn_24_24 : Fin 27 → ℝ := ![(1/64), (1/32), (1/64), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1/64), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_24_24 :
    jordan value24 value24 = decode productColumn_24_24 := by
  simp only [value24_decode, value24_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_24_24, column24, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_24_24 :
    productColumn_24_24 = ∑ k : Fin 27, productCoeff_24_24 k • columns k := by
  funext r
  change productColumn_24_24 r = ∑ k : Fin 27, productCoeff_24_24 k * columns k r
  fin_cases r <;> norm_num [productColumn_24_24, productCoeff_24_24, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_24_24 :
    jordan (nativeWords 24) (nativeWords 24) =
      ∑ k : Fin 27, productCoeff_24_24 k • nativeWords k := by
  change jordan value24 value24 = _
  rw [native_product_decode_24_24, productColumn_sum_24_24, decode_sum_columns]

def productCoeff_24_25 : Fin 27 → ℝ := ![0, 0, 0, (1/96), 0, (1/16), 0, 0, 0, 0, 0, (-1/16), 0, 0, 0, 0, (1/96), 0, 0, 0, 0, 0, (-1/48), 0, 0, 0, (-1/96)]
def productColumn_24_25 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1/128), 0, (-1/64), 0, 0, (-1/128), 0, 0, 0, 0, 0, 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_24_25 :
    jordan value24 value25 = decode productColumn_24_25 := by
  simp only [value24_decode, value25_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_24_25, column24, column25, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_24_25 :
    productColumn_24_25 = ∑ k : Fin 27, productCoeff_24_25 k • columns k := by
  funext r
  change productColumn_24_25 r = ∑ k : Fin 27, productCoeff_24_25 k * columns k r
  fin_cases r <;> norm_num [productColumn_24_25, productCoeff_24_25, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_24_25 :
    jordan (nativeWords 24) (nativeWords 25) =
      ∑ k : Fin 27, productCoeff_24_25 k • nativeWords k := by
  change jordan value24 value25 = _
  rw [native_product_decode_24_25, productColumn_sum_24_25, decode_sum_columns]

def productCoeff_24_26 : Fin 27 → ℝ := ![0, 0, (1/16), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1/32), 0, 0, 0, (-1/4), 0, 0, 0, (-1/8), 0]
def productColumn_24_26 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (3/64), 0, 0, 0, 0, (-3/64), 0, 0, 0, 0, 0, 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_24_26 :
    jordan value24 value26 = decode productColumn_24_26 := by
  simp only [value24_decode, value26_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_24_26, column24, column26, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_24_26 :
    productColumn_24_26 = ∑ k : Fin 27, productCoeff_24_26 k • columns k := by
  funext r
  change productColumn_24_26 r = ∑ k : Fin 27, productCoeff_24_26 k * columns k r
  fin_cases r <;> norm_num [productColumn_24_26, productCoeff_24_26, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_24_26 :
    jordan (nativeWords 24) (nativeWords 26) =
      ∑ k : Fin 27, productCoeff_24_26 k • nativeWords k := by
  change jordan value24 value26 = _
  rw [native_product_decode_24_26, productColumn_sum_24_26, decode_sum_columns]

end
end Glennie.Compact.NativeWordTableR01
