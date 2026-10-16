/- Finite 27-branch product routing for this row. -/
module
public import Glennie.Compact.NativeWordProductRow00R01
public import Glennie.Compact.NativeWordProductRow01R01
public import Glennie.Compact.NativeWordProductRow02R01

@[expose] public section
namespace Glennie.Compact.NativeWordTableR01
noncomputable section
open Glennie AlbertGeometry.NativeOperatorTrace
open scoped BigOperators Matrix
set_option autoImplicit false

def productCoeffRow2 : Fin 27 → Fin 27 → ℝ := ![productCoeff_00_02, productCoeff_01_02, productCoeff_02_02, productCoeff_02_03, productCoeff_02_04, productCoeff_02_05, productCoeff_02_06, productCoeff_02_07, productCoeff_02_08, productCoeff_02_09, productCoeff_02_10, productCoeff_02_11, productCoeff_02_12, productCoeff_02_13, productCoeff_02_14, productCoeff_02_15, productCoeff_02_16, productCoeff_02_17, productCoeff_02_18, productCoeff_02_19, productCoeff_02_20, productCoeff_02_21, productCoeff_02_22, productCoeff_02_23, productCoeff_02_24, productCoeff_02_25, productCoeff_02_26]

theorem native_product_row2 (j : Fin 27) :
    jordan (nativeWords 2) (nativeWords j) =
      ∑ k : Fin 27, productCoeffRow2 j k • nativeWords k := by
  fin_cases j
  · exact (jordan_comm (nativeWords 2) (nativeWords 0)).trans native_product_00_02
  · exact (jordan_comm (nativeWords 2) (nativeWords 1)).trans native_product_01_02
  · exact native_product_02_02
  · exact native_product_02_03
  · exact native_product_02_04
  · exact native_product_02_05
  · exact native_product_02_06
  · exact native_product_02_07
  · exact native_product_02_08
  · exact native_product_02_09
  · exact native_product_02_10
  · exact native_product_02_11
  · exact native_product_02_12
  · exact native_product_02_13
  · exact native_product_02_14
  · exact native_product_02_15
  · exact native_product_02_16
  · exact native_product_02_17
  · exact native_product_02_18
  · exact native_product_02_19
  · exact native_product_02_20
  · exact native_product_02_21
  · exact native_product_02_22
  · exact native_product_02_23
  · exact native_product_02_24
  · exact native_product_02_25
  · exact native_product_02_26

end
end Glennie.Compact.NativeWordTableR01
