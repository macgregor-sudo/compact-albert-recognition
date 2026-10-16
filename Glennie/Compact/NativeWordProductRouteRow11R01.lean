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
public import Glennie.Compact.NativeWordProductRow11R01

@[expose] public section
namespace Glennie.Compact.NativeWordTableR01
noncomputable section
open Glennie AlbertGeometry.NativeOperatorTrace
open scoped BigOperators Matrix
set_option autoImplicit false

def productCoeffRow11 : Fin 27 → Fin 27 → ℝ := ![productCoeff_00_11, productCoeff_01_11, productCoeff_02_11, productCoeff_03_11, productCoeff_04_11, productCoeff_05_11, productCoeff_06_11, productCoeff_07_11, productCoeff_08_11, productCoeff_09_11, productCoeff_10_11, productCoeff_11_11, productCoeff_11_12, productCoeff_11_13, productCoeff_11_14, productCoeff_11_15, productCoeff_11_16, productCoeff_11_17, productCoeff_11_18, productCoeff_11_19, productCoeff_11_20, productCoeff_11_21, productCoeff_11_22, productCoeff_11_23, productCoeff_11_24, productCoeff_11_25, productCoeff_11_26]

theorem native_product_row11 (j : Fin 27) :
    jordan (nativeWords 11) (nativeWords j) =
      ∑ k : Fin 27, productCoeffRow11 j k • nativeWords k := by
  fin_cases j
  · exact (jordan_comm (nativeWords 11) (nativeWords 0)).trans native_product_00_11
  · exact (jordan_comm (nativeWords 11) (nativeWords 1)).trans native_product_01_11
  · exact (jordan_comm (nativeWords 11) (nativeWords 2)).trans native_product_02_11
  · exact (jordan_comm (nativeWords 11) (nativeWords 3)).trans native_product_03_11
  · exact (jordan_comm (nativeWords 11) (nativeWords 4)).trans native_product_04_11
  · exact (jordan_comm (nativeWords 11) (nativeWords 5)).trans native_product_05_11
  · exact (jordan_comm (nativeWords 11) (nativeWords 6)).trans native_product_06_11
  · exact (jordan_comm (nativeWords 11) (nativeWords 7)).trans native_product_07_11
  · exact (jordan_comm (nativeWords 11) (nativeWords 8)).trans native_product_08_11
  · exact (jordan_comm (nativeWords 11) (nativeWords 9)).trans native_product_09_11
  · exact (jordan_comm (nativeWords 11) (nativeWords 10)).trans native_product_10_11
  · exact native_product_11_11
  · exact native_product_11_12
  · exact native_product_11_13
  · exact native_product_11_14
  · exact native_product_11_15
  · exact native_product_11_16
  · exact native_product_11_17
  · exact native_product_11_18
  · exact native_product_11_19
  · exact native_product_11_20
  · exact native_product_11_21
  · exact native_product_11_22
  · exact native_product_11_23
  · exact native_product_11_24
  · exact native_product_11_25
  · exact native_product_11_26

end
end Glennie.Compact.NativeWordTableR01
