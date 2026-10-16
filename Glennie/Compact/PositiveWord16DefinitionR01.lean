module

public import Glennie.Compact.PositiveWordEndpointR01

/- A distinct 16-label algebraic expansion using native U_x, U_y, U_z
   directly and only expanding the Jordan L_x input. It uses a broader
   map alphabet than the 192-label positive-amplitude expression.
   No positivity or operational claim is made here. -/
@[expose] public section
namespace Glennie.Compact.PositiveWord16DefinitionR01
open Glennie
open Glennie.Compact.PositiveFilterAlgebraR01
open Glennie.Compact.PositiveWordBookkeepingR01
open Glennie.Compact.PositiveWordLayersR01
open Glennie.Compact.PositiveWordEndpointR01
noncomputable section
set_option autoImplicit false

def uLinear (w : Albert) : Albert →ₗ[ℝ] Albert where
  toFun := U w
  map_add' := by
    intro v t
    exact U_add_argument w v t
  map_smul' := by
    intro a v
    exact U_smul_argument a w v

def outerLinear (x y : Albert) (o : Bool) : Albert →ₗ[ℝ] Albert :=
  if o then (uLinear x).comp (uLinear y)
  else (uLinear y).comp (uLinear x)

def wordLinear (x y z : Albert) (o l : Bool) : Albert →ₗ[ℝ] Albert :=
  (outerLinear x y o).comp ((uLinear z).comp (filterLinear x l))

def word (x y z v : Albert) (o l : Bool) : Albert :=
  wordLinear x y z o l v

/-- o: native commutator order; l: signed L_x filter; k,j: endpoints. -/
abbrev Label16 := Bool × Bool × Bool × Bool

def coefficient (o l k j : Bool) : ℝ :=
  sign o * sign l * sign k * sign j

def labelCoefficient (a : Label16) : ℝ :=
  coefficient a.1 a.2.1 a.2.2.1 a.2.2.2

def evaluation (p q r : Fin 3 → Albert) (a : Label16) : ℝ :=
  inner (endpoint r a.2.2.1)
    (word (encoder p) (encoder q) (encoder r)
      (endpoint q a.2.2.2) a.1 a.2.1)

def expanded (p q r : Fin 3 → Albert) : ℝ :=
  ∑ a : Label16, labelCoefficient a * evaluation p q r a

theorem label16_card : Fintype.card Label16 = 16 := by
  norm_num [Label16, Fintype.card_prod]

theorem abs_coefficient (o l k j : Bool) : |coefficient o l k j| = 1 := by
  simp [coefficient, abs_mul, abs_sign]

theorem coefficient_mass :
    (∑ a : Label16, |labelCoefficient a|) = (16 : ℝ) := by
  simp only [labelCoefficient, abs_coefficient]
  norm_num [Label16, Fintype.sum_prod_type]

end
end Glennie.Compact.PositiveWord16DefinitionR01
