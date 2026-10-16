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
public import Glennie.Compact.NativeWordProductRow13R01
public import Glennie.Compact.NativeWordProductRow14R01
public import Glennie.Compact.NativeWordProductRow15R01
public import Glennie.Compact.NativeWordProductRow16R01
public import Glennie.Compact.NativeWordProductRow17R01
public import Glennie.Compact.NativeWordProductRow18R01
public import Glennie.Compact.NativeWordProductRow19R01

@[expose] public section
namespace Glennie.Compact.NativeWordTableR01
noncomputable section
open Glennie AlbertGeometry.NativeOperatorTrace
open scoped BigOperators Matrix
set_option autoImplicit false

def productCoeffRow19 : Fin 27 → Fin 27 → ℝ := ![productCoeff_00_19, productCoeff_01_19, productCoeff_02_19, productCoeff_03_19, productCoeff_04_19, productCoeff_05_19, productCoeff_06_19, productCoeff_07_19, productCoeff_08_19, productCoeff_09_19, productCoeff_10_19, productCoeff_11_19, productCoeff_12_19, productCoeff_13_19, productCoeff_14_19, productCoeff_15_19, productCoeff_16_19, productCoeff_17_19, productCoeff_18_19, productCoeff_19_19, productCoeff_19_20, productCoeff_19_21, productCoeff_19_22, productCoeff_19_23, productCoeff_19_24, productCoeff_19_25, productCoeff_19_26]

theorem native_product_row19 (j : Fin 27) :
    jordan (nativeWords 19) (nativeWords j) =
      ∑ k : Fin 27, productCoeffRow19 j k • nativeWords k := by
  fin_cases j
  · exact (jordan_comm (nativeWords 19) (nativeWords 0)).trans native_product_00_19
  · exact (jordan_comm (nativeWords 19) (nativeWords 1)).trans native_product_01_19
  · exact (jordan_comm (nativeWords 19) (nativeWords 2)).trans native_product_02_19
  · exact (jordan_comm (nativeWords 19) (nativeWords 3)).trans native_product_03_19
  · exact (jordan_comm (nativeWords 19) (nativeWords 4)).trans native_product_04_19
  · exact (jordan_comm (nativeWords 19) (nativeWords 5)).trans native_product_05_19
  · exact (jordan_comm (nativeWords 19) (nativeWords 6)).trans native_product_06_19
  · exact (jordan_comm (nativeWords 19) (nativeWords 7)).trans native_product_07_19
  · exact (jordan_comm (nativeWords 19) (nativeWords 8)).trans native_product_08_19
  · exact (jordan_comm (nativeWords 19) (nativeWords 9)).trans native_product_09_19
  · exact (jordan_comm (nativeWords 19) (nativeWords 10)).trans native_product_10_19
  · exact (jordan_comm (nativeWords 19) (nativeWords 11)).trans native_product_11_19
  · exact (jordan_comm (nativeWords 19) (nativeWords 12)).trans native_product_12_19
  · exact (jordan_comm (nativeWords 19) (nativeWords 13)).trans native_product_13_19
  · exact (jordan_comm (nativeWords 19) (nativeWords 14)).trans native_product_14_19
  · exact (jordan_comm (nativeWords 19) (nativeWords 15)).trans native_product_15_19
  · exact (jordan_comm (nativeWords 19) (nativeWords 16)).trans native_product_16_19
  · exact (jordan_comm (nativeWords 19) (nativeWords 17)).trans native_product_17_19
  · exact (jordan_comm (nativeWords 19) (nativeWords 18)).trans native_product_18_19
  · exact native_product_19_19
  · exact native_product_19_20
  · exact native_product_19_21
  · exact native_product_19_22
  · exact native_product_19_23
  · exact native_product_19_24
  · exact native_product_19_25
  · exact native_product_19_26

end
end Glennie.Compact.NativeWordTableR01
