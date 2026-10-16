/- Native word row 0 product certificate, part 3. -/
module
public import Glennie.Compact.NativeWordProductCommonR01

@[expose] public section
namespace Glennie.Compact.NativeWordTableR01
noncomputable section
open Glennie AlbertGeometry.NativeOperatorTrace
open scoped BigOperators Matrix
set_option autoImplicit false

def productCoeff_00_24 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0]
def productColumn_00_24 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, (1/8), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (1/8)]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_00_24 :
    jordan value0 value24 = decode productColumn_00_24 := by
  simp only [value0_decode, value24_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_00_24, column0, column24, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_00_24 :
    productColumn_00_24 = ∑ k : Fin 27, productCoeff_00_24 k • columns k := by
  funext r
  change productColumn_00_24 r = ∑ k : Fin 27, productCoeff_00_24 k * columns k r
  fin_cases r <;> norm_num [productColumn_00_24, productCoeff_00_24, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_00_24 :
    jordan (nativeWords 0) (nativeWords 24) =
      ∑ k : Fin 27, productCoeff_00_24 k • nativeWords k := by
  change jordan value0 value24 = _
  rw [native_product_decode_00_24, productColumn_sum_00_24, decode_sum_columns]

def productCoeff_00_25 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0]
def productColumn_00_25 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, (1/8), 0, (-1/8), (-1/4), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1/4), 0, (-1/8), (1/8), 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_00_25 :
    jordan value0 value25 = decode productColumn_00_25 := by
  simp only [value0_decode, value25_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_00_25, column0, column25, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_00_25 :
    productColumn_00_25 = ∑ k : Fin 27, productCoeff_00_25 k • columns k := by
  funext r
  change productColumn_00_25 r = ∑ k : Fin 27, productCoeff_00_25 k * columns k r
  fin_cases r <;> norm_num [productColumn_00_25, productCoeff_00_25, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_00_25 :
    jordan (nativeWords 0) (nativeWords 25) =
      ∑ k : Fin 27, productCoeff_00_25 k • nativeWords k := by
  change jordan value0 value25 = _
  rw [native_product_decode_00_25, productColumn_sum_00_25, decode_sum_columns]

def productCoeff_00_26 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
def productColumn_00_26 : Fin 27 → ℝ := ![0, 0, 0, -1, 0, 0, (-1/4), 0, (-1/4), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, (1/4), (1/4), 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_00_26 :
    jordan value0 value26 = decode productColumn_00_26 := by
  simp only [value0_decode, value26_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_00_26, column0, column26, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_00_26 :
    productColumn_00_26 = ∑ k : Fin 27, productCoeff_00_26 k • columns k := by
  funext r
  change productColumn_00_26 r = ∑ k : Fin 27, productCoeff_00_26 k * columns k r
  fin_cases r <;> norm_num [productColumn_00_26, productCoeff_00_26, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_00_26 :
    jordan (nativeWords 0) (nativeWords 26) =
      ∑ k : Fin 27, productCoeff_00_26 k • nativeWords k := by
  change jordan value0 value26 = _
  rw [native_product_decode_00_26, productColumn_sum_00_26, decode_sum_columns]

end
end Glennie.Compact.NativeWordTableR01
