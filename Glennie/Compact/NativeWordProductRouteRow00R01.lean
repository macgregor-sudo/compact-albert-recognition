/- Finite 27-branch product routing for this row. -/
module
public import Glennie.Compact.NativeWordProductRow00R01

@[expose] public section
namespace Glennie.Compact.NativeWordTableR01
noncomputable section
open Glennie AlbertGeometry.NativeOperatorTrace
open scoped BigOperators Matrix
set_option autoImplicit false

def productCoeffRow0 : Fin 27 → Fin 27 → ℝ := ![productCoeff_00_00, productCoeff_00_01, productCoeff_00_02, productCoeff_00_03, productCoeff_00_04, productCoeff_00_05, productCoeff_00_06, productCoeff_00_07, productCoeff_00_08, productCoeff_00_09, productCoeff_00_10, productCoeff_00_11, productCoeff_00_12, productCoeff_00_13, productCoeff_00_14, productCoeff_00_15, productCoeff_00_16, productCoeff_00_17, productCoeff_00_18, productCoeff_00_19, productCoeff_00_20, productCoeff_00_21, productCoeff_00_22, productCoeff_00_23, productCoeff_00_24, productCoeff_00_25, productCoeff_00_26]

theorem native_product_row0 (j : Fin 27) :
    jordan (nativeWords 0) (nativeWords j) =
      ∑ k : Fin 27, productCoeffRow0 j k • nativeWords k := by
  fin_cases j
  · exact native_product_00_00
  · exact native_product_00_01
  · exact native_product_00_02
  · exact native_product_00_03
  · exact native_product_00_04
  · exact native_product_00_05
  · exact native_product_00_06
  · exact native_product_00_07
  · exact native_product_00_08
  · exact native_product_00_09
  · exact native_product_00_10
  · exact native_product_00_11
  · exact native_product_00_12
  · exact native_product_00_13
  · exact native_product_00_14
  · exact native_product_00_15
  · exact native_product_00_16
  · exact native_product_00_17
  · exact native_product_00_18
  · exact native_product_00_19
  · exact native_product_00_20
  · exact native_product_00_21
  · exact native_product_00_22
  · exact native_product_00_23
  · exact native_product_00_24
  · exact native_product_00_25
  · exact native_product_00_26

end
end Glennie.Compact.NativeWordTableR01
