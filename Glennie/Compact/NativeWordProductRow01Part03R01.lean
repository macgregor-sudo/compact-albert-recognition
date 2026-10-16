/- Native word row 1 product certificate, part 3. -/
module
public import Glennie.Compact.NativeWordProductCommonR01

@[expose] public section
namespace Glennie.Compact.NativeWordTableR01
noncomputable section
open Glennie AlbertGeometry.NativeOperatorTrace
open scoped BigOperators Matrix
set_option autoImplicit false

def productCoeff_01_25 : Fin 27 → ℝ := ![0, 0, 0, (-1/12), 0, (-1/2), 0, 0, 0, 0, 0, (1/2), 0, 0, 0, 0, (1/6), 0, 0, 0, 0, 0, (1/6), 0, 0, 0, (1/12)]
def productColumn_01_25 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, (-1/16), 0, (1/16), (1/8), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1/8), 0, (-1/16), (1/16), 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_01_25 :
    jordan value1 value25 = decode productColumn_01_25 := by
  simp only [value1_decode, value25_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_01_25, column1, column25, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_01_25 :
    productColumn_01_25 = ∑ k : Fin 27, productCoeff_01_25 k • columns k := by
  funext r
  change productColumn_01_25 r = ∑ k : Fin 27, productCoeff_01_25 k * columns k r
  fin_cases r <;> norm_num [productColumn_01_25, productCoeff_01_25, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_01_25 :
    jordan (nativeWords 1) (nativeWords 25) =
      ∑ k : Fin 27, productCoeff_01_25 k • nativeWords k := by
  change jordan value1 value25 = _
  rw [native_product_decode_01_25, productColumn_sum_01_25, decode_sum_columns]

def productCoeff_01_26 : Fin 27 → ℝ := ![0, 0, (-1/3), 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, (1/6), 0, 0, 0, (-2/3), 0, 0, 0, (-1/3), 0]
def productColumn_01_26 : Fin 27 → ℝ := ![0, 0, 0, (1/2), 0, 0, (1/8), 0, (1/8), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (1/2), 0, 0, 0, 0, (1/8), (1/8), 0]

set_option maxHeartbeats 2000000 in
theorem native_product_decode_01_26 :
    jordan value1 value26 = decode productColumn_01_26 := by
  simp only [value1_decode, value26_decode]
  ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, productColumn_01_26, column1, column26, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq, Quaternion.normSq_def']
  all_goals norm_num [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  all_goals ring

set_option maxHeartbeats 2000000 in
theorem productColumn_sum_01_26 :
    productColumn_01_26 = ∑ k : Fin 27, productCoeff_01_26 k • columns k := by
  funext r
  change productColumn_01_26 r = ∑ k : Fin 27, productCoeff_01_26 k * columns k r
  fin_cases r <;> norm_num [productColumn_01_26, productCoeff_01_26, columns, column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26, Fin.sum_univ_succ]

theorem native_product_01_26 :
    jordan (nativeWords 1) (nativeWords 26) =
      ∑ k : Fin 27, productCoeff_01_26 k • nativeWords k := by
  change jordan value1 value26 = _
  rw [native_product_decode_01_26, productColumn_sum_01_26, decode_sum_columns]

end
end Glennie.Compact.NativeWordTableR01
