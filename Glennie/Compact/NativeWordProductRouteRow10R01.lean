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
public import Glennie.Compact.NativeWordProductRow09R01
public import Glennie.Compact.NativeWordProductRow10R01

@[expose] public section
namespace Glennie.Compact.NativeWordTableR01
noncomputable section
open Glennie AlbertGeometry.NativeOperatorTrace
open scoped BigOperators Matrix
set_option autoImplicit false

def productCoeffRow10 : Fin 27 → Fin 27 → ℝ := ![productCoeff_00_10, productCoeff_01_10, productCoeff_02_10, productCoeff_03_10, productCoeff_04_10, productCoeff_05_10, productCoeff_06_10, productCoeff_07_10, productCoeff_08_10, productCoeff_09_10, productCoeff_10_10, productCoeff_10_11, productCoeff_10_12, productCoeff_10_13, productCoeff_10_14, productCoeff_10_15, productCoeff_10_16, productCoeff_10_17, productCoeff_10_18, productCoeff_10_19, productCoeff_10_20, productCoeff_10_21, productCoeff_10_22, productCoeff_10_23, productCoeff_10_24, productCoeff_10_25, productCoeff_10_26]

theorem native_product_row10 (j : Fin 27) :
    jordan (nativeWords 10) (nativeWords j) =
      ∑ k : Fin 27, productCoeffRow10 j k • nativeWords k := by
  fin_cases j
  · exact (jordan_comm (nativeWords 10) (nativeWords 0)).trans native_product_00_10
  · exact (jordan_comm (nativeWords 10) (nativeWords 1)).trans native_product_01_10
  · exact (jordan_comm (nativeWords 10) (nativeWords 2)).trans native_product_02_10
  · exact (jordan_comm (nativeWords 10) (nativeWords 3)).trans native_product_03_10
  · exact (jordan_comm (nativeWords 10) (nativeWords 4)).trans native_product_04_10
  · exact (jordan_comm (nativeWords 10) (nativeWords 5)).trans native_product_05_10
  · exact (jordan_comm (nativeWords 10) (nativeWords 6)).trans native_product_06_10
  · exact (jordan_comm (nativeWords 10) (nativeWords 7)).trans native_product_07_10
  · exact (jordan_comm (nativeWords 10) (nativeWords 8)).trans native_product_08_10
  · exact (jordan_comm (nativeWords 10) (nativeWords 9)).trans native_product_09_10
  · exact native_product_10_10
  · exact native_product_10_11
  · exact native_product_10_12
  · exact native_product_10_13
  · exact native_product_10_14
  · exact native_product_10_15
  · exact native_product_10_16
  · exact native_product_10_17
  · exact native_product_10_18
  · exact native_product_10_19
  · exact native_product_10_20
  · exact native_product_10_21
  · exact native_product_10_22
  · exact native_product_10_23
  · exact native_product_10_24
  · exact native_product_10_25
  · exact native_product_10_26

end
end Glennie.Compact.NativeWordTableR01
