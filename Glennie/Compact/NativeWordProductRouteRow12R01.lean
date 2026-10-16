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
public import Glennie.Compact.NativeWordProductRow12R01

@[expose] public section
namespace Glennie.Compact.NativeWordTableR01
noncomputable section
open Glennie AlbertGeometry.NativeOperatorTrace
open scoped BigOperators Matrix
set_option autoImplicit false

def productCoeffRow12 : Fin 27 → Fin 27 → ℝ := ![productCoeff_00_12, productCoeff_01_12, productCoeff_02_12, productCoeff_03_12, productCoeff_04_12, productCoeff_05_12, productCoeff_06_12, productCoeff_07_12, productCoeff_08_12, productCoeff_09_12, productCoeff_10_12, productCoeff_11_12, productCoeff_12_12, productCoeff_12_13, productCoeff_12_14, productCoeff_12_15, productCoeff_12_16, productCoeff_12_17, productCoeff_12_18, productCoeff_12_19, productCoeff_12_20, productCoeff_12_21, productCoeff_12_22, productCoeff_12_23, productCoeff_12_24, productCoeff_12_25, productCoeff_12_26]

theorem native_product_row12 (j : Fin 27) :
    jordan (nativeWords 12) (nativeWords j) =
      ∑ k : Fin 27, productCoeffRow12 j k • nativeWords k := by
  fin_cases j
  · exact (jordan_comm (nativeWords 12) (nativeWords 0)).trans native_product_00_12
  · exact (jordan_comm (nativeWords 12) (nativeWords 1)).trans native_product_01_12
  · exact (jordan_comm (nativeWords 12) (nativeWords 2)).trans native_product_02_12
  · exact (jordan_comm (nativeWords 12) (nativeWords 3)).trans native_product_03_12
  · exact (jordan_comm (nativeWords 12) (nativeWords 4)).trans native_product_04_12
  · exact (jordan_comm (nativeWords 12) (nativeWords 5)).trans native_product_05_12
  · exact (jordan_comm (nativeWords 12) (nativeWords 6)).trans native_product_06_12
  · exact (jordan_comm (nativeWords 12) (nativeWords 7)).trans native_product_07_12
  · exact (jordan_comm (nativeWords 12) (nativeWords 8)).trans native_product_08_12
  · exact (jordan_comm (nativeWords 12) (nativeWords 9)).trans native_product_09_12
  · exact (jordan_comm (nativeWords 12) (nativeWords 10)).trans native_product_10_12
  · exact (jordan_comm (nativeWords 12) (nativeWords 11)).trans native_product_11_12
  · exact native_product_12_12
  · exact native_product_12_13
  · exact native_product_12_14
  · exact native_product_12_15
  · exact native_product_12_16
  · exact native_product_12_17
  · exact native_product_12_18
  · exact native_product_12_19
  · exact native_product_12_20
  · exact native_product_12_21
  · exact native_product_12_22
  · exact native_product_12_23
  · exact native_product_12_24
  · exact native_product_12_25
  · exact native_product_12_26

end
end Glennie.Compact.NativeWordTableR01
