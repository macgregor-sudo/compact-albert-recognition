/- Finite 27-branch product routing for this row. -/
module
public import Glennie.Compact.NativeWordProductRow00R01
public import Glennie.Compact.NativeWordProductRow01R01
public import Glennie.Compact.NativeWordProductRow02R01
public import Glennie.Compact.NativeWordProductRow03R01
public import Glennie.Compact.NativeWordProductRow04R01

@[expose] public section
namespace Glennie.Compact.NativeWordTableR01
noncomputable section
open Glennie AlbertGeometry.NativeOperatorTrace
open scoped BigOperators Matrix
set_option autoImplicit false

def productCoeffRow4 : Fin 27 → Fin 27 → ℝ := ![productCoeff_00_04, productCoeff_01_04, productCoeff_02_04, productCoeff_03_04, productCoeff_04_04, productCoeff_04_05, productCoeff_04_06, productCoeff_04_07, productCoeff_04_08, productCoeff_04_09, productCoeff_04_10, productCoeff_04_11, productCoeff_04_12, productCoeff_04_13, productCoeff_04_14, productCoeff_04_15, productCoeff_04_16, productCoeff_04_17, productCoeff_04_18, productCoeff_04_19, productCoeff_04_20, productCoeff_04_21, productCoeff_04_22, productCoeff_04_23, productCoeff_04_24, productCoeff_04_25, productCoeff_04_26]

theorem native_product_row4 (j : Fin 27) :
    jordan (nativeWords 4) (nativeWords j) =
      ∑ k : Fin 27, productCoeffRow4 j k • nativeWords k := by
  fin_cases j
  · exact (jordan_comm (nativeWords 4) (nativeWords 0)).trans native_product_00_04
  · exact (jordan_comm (nativeWords 4) (nativeWords 1)).trans native_product_01_04
  · exact (jordan_comm (nativeWords 4) (nativeWords 2)).trans native_product_02_04
  · exact (jordan_comm (nativeWords 4) (nativeWords 3)).trans native_product_03_04
  · exact native_product_04_04
  · exact native_product_04_05
  · exact native_product_04_06
  · exact native_product_04_07
  · exact native_product_04_08
  · exact native_product_04_09
  · exact native_product_04_10
  · exact native_product_04_11
  · exact native_product_04_12
  · exact native_product_04_13
  · exact native_product_04_14
  · exact native_product_04_15
  · exact native_product_04_16
  · exact native_product_04_17
  · exact native_product_04_18
  · exact native_product_04_19
  · exact native_product_04_20
  · exact native_product_04_21
  · exact native_product_04_22
  · exact native_product_04_23
  · exact native_product_04_24
  · exact native_product_04_25
  · exact native_product_04_26

end
end Glennie.Compact.NativeWordTableR01
