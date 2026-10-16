module

public import Glennie.Compact.PositiveWordBookkeepingR01

/- Small, opaque operator layers for the 192-label expansion.
   No positivity or complete word-sum identity is claimed. -/
@[expose] public section
namespace Glennie.Compact.PositiveWordLayersR01
open Glennie Glennie.Compact.PositiveFilterAlgebraR01
open Glennie.Compact.PositiveWordBookkeepingR01
noncomputable section
set_option autoImplicit false

def filterLinear (w : Albert) (s : Bool) : Albert →ₗ[ℝ] Albert where
  toFun := filter w s
  map_add' := by
    intro v t
    exact U_add_argument (amplitude w s) v t
  map_smul' := by
    intro r v
    exact U_smul_argument r (amplitude w s) v

def middle (z v : Albert) (i : Fin 3) : Albert :=
  if i = 0 then filter z false v else if i = 1 then filter z true v else v

theorem signed_filter_apply (x v : Albert) :
    (∑ l : Bool, sign l • filter x l v) = jordan x v := by
  rw [Fintype.sum_bool]
  simp [sign]
  rw [jordan_filter_difference]
  module

theorem middle_sum (z v : Albert) :
    (∑ i : Fin 3, middleCoeff i • middle z v i) = U z v := by
  simp only [Fin.sum_univ_three]
  have h := U_filter_decomposition z v
  simp [middle, middleCoeff] 
  rw [h]
  module

end
end Glennie.Compact.PositiveWordLayersR01
