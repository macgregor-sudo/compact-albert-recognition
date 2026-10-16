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

@[expose] public section
namespace Glennie.Compact.NativeWordTableR01
noncomputable section
open Glennie AlbertGeometry.NativeOperatorTrace
open scoped BigOperators Matrix
set_option autoImplicit false

def productCoeffRow20 : Fin 27 → Fin 27 → ℝ := ![productCoeff_00_20, productCoeff_01_20, productCoeff_02_20, productCoeff_03_20, productCoeff_04_20, productCoeff_05_20, productCoeff_06_20, productCoeff_07_20, productCoeff_08_20, productCoeff_09_20, productCoeff_10_20, productCoeff_11_20, productCoeff_12_20, productCoeff_13_20, productCoeff_14_20, productCoeff_15_20, productCoeff_16_20, productCoeff_17_20, productCoeff_18_20, productCoeff_19_20, productCoeff_20_20, productCoeff_20_21, productCoeff_20_22, productCoeff_20_23, productCoeff_20_24, productCoeff_20_25, productCoeff_20_26]

theorem native_product_row20 (j : Fin 27) :
    jordan (nativeWords 20) (nativeWords j) =
      ∑ k : Fin 27, productCoeffRow20 j k • nativeWords k := by
  fin_cases j
  · exact (jordan_comm (nativeWords 20) (nativeWords 0)).trans native_product_00_20
  · exact (jordan_comm (nativeWords 20) (nativeWords 1)).trans native_product_01_20
  · exact (jordan_comm (nativeWords 20) (nativeWords 2)).trans native_product_02_20
  · exact (jordan_comm (nativeWords 20) (nativeWords 3)).trans native_product_03_20
  · exact (jordan_comm (nativeWords 20) (nativeWords 4)).trans native_product_04_20
  · exact (jordan_comm (nativeWords 20) (nativeWords 5)).trans native_product_05_20
  · exact (jordan_comm (nativeWords 20) (nativeWords 6)).trans native_product_06_20
  · exact (jordan_comm (nativeWords 20) (nativeWords 7)).trans native_product_07_20
  · exact (jordan_comm (nativeWords 20) (nativeWords 8)).trans native_product_08_20
  · exact (jordan_comm (nativeWords 20) (nativeWords 9)).trans native_product_09_20
  · exact (jordan_comm (nativeWords 20) (nativeWords 10)).trans native_product_10_20
  · exact (jordan_comm (nativeWords 20) (nativeWords 11)).trans native_product_11_20
  · exact (jordan_comm (nativeWords 20) (nativeWords 12)).trans native_product_12_20
  · exact (jordan_comm (nativeWords 20) (nativeWords 13)).trans native_product_13_20
  · exact (jordan_comm (nativeWords 20) (nativeWords 14)).trans native_product_14_20
  · exact (jordan_comm (nativeWords 20) (nativeWords 15)).trans native_product_15_20
  · exact (jordan_comm (nativeWords 20) (nativeWords 16)).trans native_product_16_20
  · exact (jordan_comm (nativeWords 20) (nativeWords 17)).trans native_product_17_20
  · exact (jordan_comm (nativeWords 20) (nativeWords 18)).trans native_product_18_20
  · exact (jordan_comm (nativeWords 20) (nativeWords 19)).trans native_product_19_20
  · exact native_product_20_20
  · exact native_product_20_21
  · exact native_product_20_22
  · exact native_product_20_23
  · exact native_product_20_24
  · exact native_product_20_25
  · exact native_product_20_26

end
end Glennie.Compact.NativeWordTableR01
