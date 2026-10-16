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
public import Glennie.Compact.NativeWordProductRow20R01
public import Glennie.Compact.NativeWordProductRow21R01
public import Glennie.Compact.NativeWordProductRow22R01
public import Glennie.Compact.NativeWordProductRow23R01

@[expose] public section
namespace Glennie.Compact.NativeWordTableR01
noncomputable section
open Glennie AlbertGeometry.NativeOperatorTrace
open scoped BigOperators Matrix
set_option autoImplicit false

def productCoeffRow23 : Fin 27 → Fin 27 → ℝ := ![productCoeff_00_23, productCoeff_01_23, productCoeff_02_23, productCoeff_03_23, productCoeff_04_23, productCoeff_05_23, productCoeff_06_23, productCoeff_07_23, productCoeff_08_23, productCoeff_09_23, productCoeff_10_23, productCoeff_11_23, productCoeff_12_23, productCoeff_13_23, productCoeff_14_23, productCoeff_15_23, productCoeff_16_23, productCoeff_17_23, productCoeff_18_23, productCoeff_19_23, productCoeff_20_23, productCoeff_21_23, productCoeff_22_23, productCoeff_23_23, productCoeff_23_24, productCoeff_23_25, productCoeff_23_26]

theorem native_product_row23 (j : Fin 27) :
    jordan (nativeWords 23) (nativeWords j) =
      ∑ k : Fin 27, productCoeffRow23 j k • nativeWords k := by
  fin_cases j
  · exact (jordan_comm (nativeWords 23) (nativeWords 0)).trans native_product_00_23
  · exact (jordan_comm (nativeWords 23) (nativeWords 1)).trans native_product_01_23
  · exact (jordan_comm (nativeWords 23) (nativeWords 2)).trans native_product_02_23
  · exact (jordan_comm (nativeWords 23) (nativeWords 3)).trans native_product_03_23
  · exact (jordan_comm (nativeWords 23) (nativeWords 4)).trans native_product_04_23
  · exact (jordan_comm (nativeWords 23) (nativeWords 5)).trans native_product_05_23
  · exact (jordan_comm (nativeWords 23) (nativeWords 6)).trans native_product_06_23
  · exact (jordan_comm (nativeWords 23) (nativeWords 7)).trans native_product_07_23
  · exact (jordan_comm (nativeWords 23) (nativeWords 8)).trans native_product_08_23
  · exact (jordan_comm (nativeWords 23) (nativeWords 9)).trans native_product_09_23
  · exact (jordan_comm (nativeWords 23) (nativeWords 10)).trans native_product_10_23
  · exact (jordan_comm (nativeWords 23) (nativeWords 11)).trans native_product_11_23
  · exact (jordan_comm (nativeWords 23) (nativeWords 12)).trans native_product_12_23
  · exact (jordan_comm (nativeWords 23) (nativeWords 13)).trans native_product_13_23
  · exact (jordan_comm (nativeWords 23) (nativeWords 14)).trans native_product_14_23
  · exact (jordan_comm (nativeWords 23) (nativeWords 15)).trans native_product_15_23
  · exact (jordan_comm (nativeWords 23) (nativeWords 16)).trans native_product_16_23
  · exact (jordan_comm (nativeWords 23) (nativeWords 17)).trans native_product_17_23
  · exact (jordan_comm (nativeWords 23) (nativeWords 18)).trans native_product_18_23
  · exact (jordan_comm (nativeWords 23) (nativeWords 19)).trans native_product_19_23
  · exact (jordan_comm (nativeWords 23) (nativeWords 20)).trans native_product_20_23
  · exact (jordan_comm (nativeWords 23) (nativeWords 21)).trans native_product_21_23
  · exact (jordan_comm (nativeWords 23) (nativeWords 22)).trans native_product_22_23
  · exact native_product_23_23
  · exact native_product_23_24
  · exact native_product_23_25
  · exact native_product_23_26

end
end Glennie.Compact.NativeWordTableR01
