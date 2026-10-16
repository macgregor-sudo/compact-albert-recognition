/- Finite 27-branch product routing for this row. -/
module
public import Glennie.Compact.NativeWordProductRow00R01
public import Glennie.Compact.NativeWordProductRow01R01
public import Glennie.Compact.NativeWordProductRow02R01
public import Glennie.Compact.NativeWordProductRow03R01
public import Glennie.Compact.NativeWordProductRow04R01
public import Glennie.Compact.NativeWordProductRow05R01
public import Glennie.Compact.NativeWordProductRow06R01
public import Glennie.Compact.NativeWordProductRow07R01
public import Glennie.Compact.NativeWordProductRow08R01

@[expose] public section
namespace Glennie.Compact.NativeWordTableR01
noncomputable section
open Glennie AlbertGeometry.NativeOperatorTrace
open scoped BigOperators Matrix
set_option autoImplicit false

def productCoeffRow8 : Fin 27 → Fin 27 → ℝ := ![productCoeff_00_08, productCoeff_01_08, productCoeff_02_08, productCoeff_03_08, productCoeff_04_08, productCoeff_05_08, productCoeff_06_08, productCoeff_07_08, productCoeff_08_08, productCoeff_08_09, productCoeff_08_10, productCoeff_08_11, productCoeff_08_12, productCoeff_08_13, productCoeff_08_14, productCoeff_08_15, productCoeff_08_16, productCoeff_08_17, productCoeff_08_18, productCoeff_08_19, productCoeff_08_20, productCoeff_08_21, productCoeff_08_22, productCoeff_08_23, productCoeff_08_24, productCoeff_08_25, productCoeff_08_26]

theorem native_product_row8 (j : Fin 27) :
    jordan (nativeWords 8) (nativeWords j) =
      ∑ k : Fin 27, productCoeffRow8 j k • nativeWords k := by
  fin_cases j
  · exact (jordan_comm (nativeWords 8) (nativeWords 0)).trans native_product_00_08
  · exact (jordan_comm (nativeWords 8) (nativeWords 1)).trans native_product_01_08
  · exact (jordan_comm (nativeWords 8) (nativeWords 2)).trans native_product_02_08
  · exact (jordan_comm (nativeWords 8) (nativeWords 3)).trans native_product_03_08
  · exact (jordan_comm (nativeWords 8) (nativeWords 4)).trans native_product_04_08
  · exact (jordan_comm (nativeWords 8) (nativeWords 5)).trans native_product_05_08
  · exact (jordan_comm (nativeWords 8) (nativeWords 6)).trans native_product_06_08
  · exact (jordan_comm (nativeWords 8) (nativeWords 7)).trans native_product_07_08
  · exact native_product_08_08
  · exact native_product_08_09
  · exact native_product_08_10
  · exact native_product_08_11
  · exact native_product_08_12
  · exact native_product_08_13
  · exact native_product_08_14
  · exact native_product_08_15
  · exact native_product_08_16
  · exact native_product_08_17
  · exact native_product_08_18
  · exact native_product_08_19
  · exact native_product_08_20
  · exact native_product_08_21
  · exact native_product_08_22
  · exact native_product_08_23
  · exact native_product_08_24
  · exact native_product_08_25
  · exact native_product_08_26

end
end Glennie.Compact.NativeWordTableR01
