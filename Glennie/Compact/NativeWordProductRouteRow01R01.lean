/- Finite 27-branch product routing for this row. -/
module
public import Glennie.Compact.NativeWordProductRow00R01
public import Glennie.Compact.NativeWordProductRow01R01

@[expose] public section
namespace Glennie.Compact.NativeWordTableR01
noncomputable section
open Glennie AlbertGeometry.NativeOperatorTrace
open scoped BigOperators Matrix
set_option autoImplicit false

def productCoeffRow1 : Fin 27 → Fin 27 → ℝ := ![productCoeff_00_01, productCoeff_01_01, productCoeff_01_02, productCoeff_01_03, productCoeff_01_04, productCoeff_01_05, productCoeff_01_06, productCoeff_01_07, productCoeff_01_08, productCoeff_01_09, productCoeff_01_10, productCoeff_01_11, productCoeff_01_12, productCoeff_01_13, productCoeff_01_14, productCoeff_01_15, productCoeff_01_16, productCoeff_01_17, productCoeff_01_18, productCoeff_01_19, productCoeff_01_20, productCoeff_01_21, productCoeff_01_22, productCoeff_01_23, productCoeff_01_24, productCoeff_01_25, productCoeff_01_26]

theorem native_product_row1 (j : Fin 27) :
    jordan (nativeWords 1) (nativeWords j) =
      ∑ k : Fin 27, productCoeffRow1 j k • nativeWords k := by
  fin_cases j
  · exact (jordan_comm (nativeWords 1) (nativeWords 0)).trans native_product_00_01
  · exact native_product_01_01
  · exact native_product_01_02
  · exact native_product_01_03
  · exact native_product_01_04
  · exact native_product_01_05
  · exact native_product_01_06
  · exact native_product_01_07
  · exact native_product_01_08
  · exact native_product_01_09
  · exact native_product_01_10
  · exact native_product_01_11
  · exact native_product_01_12
  · exact native_product_01_13
  · exact native_product_01_14
  · exact native_product_01_15
  · exact native_product_01_16
  · exact native_product_01_17
  · exact native_product_01_18
  · exact native_product_01_19
  · exact native_product_01_20
  · exact native_product_01_21
  · exact native_product_01_22
  · exact native_product_01_23
  · exact native_product_01_24
  · exact native_product_01_25
  · exact native_product_01_26

end
end Glennie.Compact.NativeWordTableR01
