/- Full native 27-word product table, assembled from checked finite rows. -/
module
public import Glennie.Compact.NativeWordProductRouteRow00R01
public import Glennie.Compact.NativeWordProductRouteRow01R01
public import Glennie.Compact.NativeWordProductRouteRow02R01
public import Glennie.Compact.NativeWordProductRouteRow03R01
public import Glennie.Compact.NativeWordProductRouteRow04R01
public import Glennie.Compact.NativeWordProductRouteRow05R01
public import Glennie.Compact.NativeWordProductRouteRow06R01
public import Glennie.Compact.NativeWordProductRouteRow07R01
public import Glennie.Compact.NativeWordProductRouteRow08R01
public import Glennie.Compact.NativeWordProductRouteRow09R01
public import Glennie.Compact.NativeWordProductRouteRow10R01
public import Glennie.Compact.NativeWordProductRouteRow11R01
public import Glennie.Compact.NativeWordProductRouteRow12R01
public import Glennie.Compact.NativeWordProductRouteRow13R01
public import Glennie.Compact.NativeWordProductRouteRow14R01
public import Glennie.Compact.NativeWordProductRouteRow15R01
public import Glennie.Compact.NativeWordProductRouteRow16R01
public import Glennie.Compact.NativeWordProductRouteRow17R01
public import Glennie.Compact.NativeWordProductRouteRow18R01
public import Glennie.Compact.NativeWordProductRouteRow19R01
public import Glennie.Compact.NativeWordProductRouteRow20R01
public import Glennie.Compact.NativeWordProductRouteRow21R01
public import Glennie.Compact.NativeWordProductRouteRow22R01
public import Glennie.Compact.NativeWordProductRouteRow23R01
public import Glennie.Compact.NativeWordProductRouteRow24R01
public import Glennie.Compact.NativeWordProductRouteRow25R01
public import Glennie.Compact.NativeWordProductRouteRow26R01

@[expose] public section
namespace Glennie.Compact.NativeWordTableR01
noncomputable section
open Glennie AlbertGeometry.NativeOperatorTrace
open scoped BigOperators Matrix
set_option autoImplicit false

def productCoefficients : Fin 27 → Fin 27 → Fin 27 → ℝ := ![productCoeffRow0, productCoeffRow1, productCoeffRow2, productCoeffRow3, productCoeffRow4, productCoeffRow5, productCoeffRow6, productCoeffRow7, productCoeffRow8, productCoeffRow9, productCoeffRow10, productCoeffRow11, productCoeffRow12, productCoeffRow13, productCoeffRow14, productCoeffRow15, productCoeffRow16, productCoeffRow17, productCoeffRow18, productCoeffRow19, productCoeffRow20, productCoeffRow21, productCoeffRow22, productCoeffRow23, productCoeffRow24, productCoeffRow25, productCoeffRow26]

theorem native_product_table (i j : Fin 27) :
    jordan (nativeWords i) (nativeWords j) =
      ∑ k : Fin 27, productCoefficients i j k • nativeWords k := by
  fin_cases i
  · exact native_product_row0 j
  · exact native_product_row1 j
  · exact native_product_row2 j
  · exact native_product_row3 j
  · exact native_product_row4 j
  · exact native_product_row5 j
  · exact native_product_row6 j
  · exact native_product_row7 j
  · exact native_product_row8 j
  · exact native_product_row9 j
  · exact native_product_row10 j
  · exact native_product_row11 j
  · exact native_product_row12 j
  · exact native_product_row13 j
  · exact native_product_row14 j
  · exact native_product_row15 j
  · exact native_product_row16 j
  · exact native_product_row17 j
  · exact native_product_row18 j
  · exact native_product_row19 j
  · exact native_product_row20 j
  · exact native_product_row21 j
  · exact native_product_row22 j
  · exact native_product_row23 j
  · exact native_product_row24 j
  · exact native_product_row25 j
  · exact native_product_row26 j

end
end Glennie.Compact.NativeWordTableR01
