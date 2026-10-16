module

public import Glennie.Compact.PositiveFilterAlgebraR01

/- Exact finite bookkeeping for the 192-word expansion.
   This module proves no equality between a word sum and Phi and no cone claim. -/
@[expose] public section
namespace Glennie.Compact.PositiveWordBookkeepingR01
open Glennie Glennie.Compact.PositiveFilterAlgebraR01
noncomputable section
set_option autoImplicit false

def sign (s : Bool) : ℝ := if s then -1 else 1

def middleCoeff (i : Fin 3) : ℝ := if i = 2 then -1 else 2

def coefficient (o : Bool) (i : Fin 3) (l k j : Bool) : ℝ :=
  4 * sign o * middleCoeff i * sign l * sign k * sign j

/-- Three commutator flags, one middle choice, and three endpoint/filter flags. -/
abbrev Label := Bool × Bool × Bool × Fin 3 × Bool × Bool × Bool

def labelCoefficient (a : Label) : ℝ :=
  coefficient a.1 a.2.2.2.1 a.2.2.2.2.1 a.2.2.2.2.2.1 a.2.2.2.2.2.2

theorem abs_sign (s : Bool) : |sign s| = 1 := by
  cases s <;> norm_num [sign]

theorem middleCoeff_abs_sum : (∑ i : Fin 3, |middleCoeff i|) = 5 := by
  norm_num [Fin.sum_univ_three, middleCoeff]

theorem abs_coefficient (o : Bool) (i : Fin 3) (l k j : Bool) :
    |coefficient o i l k j| = 4 * |middleCoeff i| := by
  simp [coefficient, abs_mul, abs_sign]

theorem label_card : Fintype.card Label = 192 := by
  norm_num [Label, Fintype.card_prod]

theorem coefficient_mass :
    (∑ a : Label, |labelCoefficient a|) = (1280 : ℝ) := by
  simp only [labelCoefficient, abs_coefficient]
  simp [Label, Fintype.sum_prod_type,
    Fin.sum_univ_three, middleCoeff] <;> norm_num

end
end Glennie.Compact.PositiveWordBookkeepingR01
