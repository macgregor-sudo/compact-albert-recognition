/- Finite 27-branch product routing for this row. -/
module
public import Glennie.Compact.NativeWordProductRow00R01
public import Glennie.Compact.NativeWordProductRow01R01
public import Glennie.Compact.NativeWordProductRow02R01
public import Glennie.Compact.NativeWordProductRow03R01

@[expose] public section
namespace Glennie.Compact.NativeWordTableR01
noncomputable section
open Glennie AlbertGeometry.NativeOperatorTrace
open scoped BigOperators Matrix
set_option autoImplicit false

def productCoeffRow3 : Fin 27 → Fin 27 → ℝ := ![productCoeff_00_03, productCoeff_01_03, productCoeff_02_03, productCoeff_03_03, productCoeff_03_04, productCoeff_03_05, productCoeff_03_06, productCoeff_03_07, productCoeff_03_08, productCoeff_03_09, productCoeff_03_10, productCoeff_03_11, productCoeff_03_12, productCoeff_03_13, productCoeff_03_14, productCoeff_03_15, productCoeff_03_16, productCoeff_03_17, productCoeff_03_18, productCoeff_03_19, productCoeff_03_20, productCoeff_03_21, productCoeff_03_22, productCoeff_03_23, productCoeff_03_24, productCoeff_03_25, productCoeff_03_26]

theorem native_product_row3 (j : Fin 27) :
    jordan (nativeWords 3) (nativeWords j) =
      ∑ k : Fin 27, productCoeffRow3 j k • nativeWords k := by
  fin_cases j
  · exact (jordan_comm (nativeWords 3) (nativeWords 0)).trans native_product_00_03
  · exact (jordan_comm (nativeWords 3) (nativeWords 1)).trans native_product_01_03
  · exact (jordan_comm (nativeWords 3) (nativeWords 2)).trans native_product_02_03
  · exact native_product_03_03
  · exact native_product_03_04
  · exact native_product_03_05
  · exact native_product_03_06
  · exact native_product_03_07
  · exact native_product_03_08
  · exact native_product_03_09
  · exact native_product_03_10
  · exact native_product_03_11
  · exact native_product_03_12
  · exact native_product_03_13
  · exact native_product_03_14
  · exact native_product_03_15
  · exact native_product_03_16
  · exact native_product_03_17
  · exact native_product_03_18
  · exact native_product_03_19
  · exact native_product_03_20
  · exact native_product_03_21
  · exact native_product_03_22
  · exact native_product_03_23
  · exact native_product_03_24
  · exact native_product_03_25
  · exact native_product_03_26

end
end Glennie.Compact.NativeWordTableR01
