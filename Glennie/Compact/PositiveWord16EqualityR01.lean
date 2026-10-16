module

public import Glennie.Compact.PositiveWord16DefinitionR01

/- Pure 16-label Phi equality for the broader native-U word alphabet.
   It asserts no positivity, trace bound, or operational realization. -/
@[expose] public section
namespace Glennie.Compact.PositiveWord16EqualityR01
open Glennie Glennie.Compact.OperationalPhi
open Glennie.Compact.PositiveFilterAlgebraR01
open Glennie.Compact.PositiveWordBookkeepingR01 (sign)
open Glennie.Compact.PositiveWordLayersR01
open Glennie.Compact.PositiveWordEndpointR01
open Glennie.Compact.PositiveWord16DefinitionR01
noncomputable section
set_option autoImplicit false

theorem word_factor (x y z v : Albert) (o l : Bool) :
    word x y z v o l =
      ((outerLinear x y o).comp (uLinear z)) (filter x l v) := by
  simp [word, wordLinear, filterLinear]

theorem collapse_endpoints (p q r : Fin 3 → Albert) (o l : Bool) :
    (∑ k : Bool, ∑ j : Bool,
      coefficient o l k j * inner (endpoint r k)
        (word (encoder p) (encoder q) (encoder r) (endpoint q j) o l)) =
    (sign o * sign l) * inner (encoder r)
      (word (encoder p) (encoder q) (encoder r) (encoder q) o l) := by
  let C := sign o * sign l
  calc
    _ = C * (∑ k : Bool, ∑ j : Bool,
        sign k * sign j * inner (endpoint r k)
          (wordLinear (encoder p) (encoder q) (encoder r) o l (endpoint q j))) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      apply Finset.sum_congr rfl
      intro j hj
      dsimp only [C, coefficient, word]
      ring
    _ = _ := by
      rw [signed_endpoint_pairing]
      rfl

theorem collapse_filter (x y z t v : Albert) (o : Bool) :
    (∑ l : Bool, (sign o * sign l) * inner t (word x y z v o l)) =
    sign o * inner t (outerLinear x y o (U z (jordan x v))) := by
  simp only [word_factor]
  rw [Fintype.sum_bool, jordan_filter_difference]
  cases o <;> simp [sign, outerLinear, uLinear, U_sub_argument, inner_sub_right] <;> ring

theorem collapse_order (x y t v : Albert) :
    (∑ o : Bool, sign o * inner t (outerLinear x y o v)) =
    inner t (U y (U x v) - U x (U y v)) := by
  rw [Fintype.sum_bool, inner_sub_right]
  simp [sign, outerLinear, uLinear]
  ring

theorem expanded_endpoint_collapsed (p q r : Fin 3 → Albert) :
    expanded p q r =
      ∑ o : Bool, ∑ l : Bool,
        (sign o * sign l) * inner (encoder r)
          (word (encoder p) (encoder q) (encoder r) (encoder q) o l) := by
  simp only [expanded, Fintype.sum_prod_type, labelCoefficient, evaluation]
  simp_rw [collapse_endpoints]

theorem expanded_eq_phi (p q r : Fin 3 → Albert) :
    expanded p q r = phi (encoder p) (encoder q) (encoder r) := by
  rw [expanded_endpoint_collapsed]
  simp_rw [collapse_filter]
  rw [collapse_order]
  exact (phi_eq_contrast (encoder p) (encoder q) (encoder r)).symm

end
end Glennie.Compact.PositiveWord16EqualityR01
