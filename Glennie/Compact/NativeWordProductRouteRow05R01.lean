/- Finite 27-branch product routing for this row. -/
module
public import Glennie.Compact.NativeWordProductRow00R01
public import Glennie.Compact.NativeWordProductRow01R01
public import Glennie.Compact.NativeWordProductRow02R01
public import Glennie.Compact.NativeWordProductRow03R01
public import Glennie.Compact.NativeWordProductRow04R01
public import Glennie.Compact.NativeWordProductRow05R01

@[expose] public section
namespace Glennie.Compact.NativeWordTableR01
noncomputable section
open Glennie AlbertGeometry.NativeOperatorTrace
open scoped BigOperators Matrix
set_option autoImplicit false

def productCoeffRow5 : Fin 27 → Fin 27 → ℝ := ![productCoeff_00_05, productCoeff_01_05, productCoeff_02_05, productCoeff_03_05, productCoeff_04_05, productCoeff_05_05, productCoeff_05_06, productCoeff_05_07, productCoeff_05_08, productCoeff_05_09, productCoeff_05_10, productCoeff_05_11, productCoeff_05_12, productCoeff_05_13, productCoeff_05_14, productCoeff_05_15, productCoeff_05_16, productCoeff_05_17, productCoeff_05_18, productCoeff_05_19, productCoeff_05_20, productCoeff_05_21, productCoeff_05_22, productCoeff_05_23, productCoeff_05_24, productCoeff_05_25, productCoeff_05_26]

theorem native_product_row5 (j : Fin 27) :
    jordan (nativeWords 5) (nativeWords j) =
      ∑ k : Fin 27, productCoeffRow5 j k • nativeWords k := by
  fin_cases j
  · exact (jordan_comm (nativeWords 5) (nativeWords 0)).trans native_product_00_05
  · exact (jordan_comm (nativeWords 5) (nativeWords 1)).trans native_product_01_05
  · exact (jordan_comm (nativeWords 5) (nativeWords 2)).trans native_product_02_05
  · exact (jordan_comm (nativeWords 5) (nativeWords 3)).trans native_product_03_05
  · exact (jordan_comm (nativeWords 5) (nativeWords 4)).trans native_product_04_05
  · exact native_product_05_05
  · exact native_product_05_06
  · exact native_product_05_07
  · exact native_product_05_08
  · exact native_product_05_09
  · exact native_product_05_10
  · exact native_product_05_11
  · exact native_product_05_12
  · exact native_product_05_13
  · exact native_product_05_14
  · exact native_product_05_15
  · exact native_product_05_16
  · exact native_product_05_17
  · exact native_product_05_18
  · exact native_product_05_19
  · exact native_product_05_20
  · exact native_product_05_21
  · exact native_product_05_22
  · exact native_product_05_23
  · exact native_product_05_24
  · exact native_product_05_25
  · exact native_product_05_26

end
end Glennie.Compact.NativeWordTableR01
