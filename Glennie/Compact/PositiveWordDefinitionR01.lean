module

public import Glennie.Compact.PositiveWordEndpointR01

/- The native 192-label word expression. This file defines the expansion,
   but does not assert its equality to Phi or physical positivity. -/
@[expose] public section
namespace Glennie.Compact.PositiveWordDefinitionR01
open Glennie
open Glennie.Compact.PositiveFilterAlgebraR01
open Glennie.Compact.PositiveWordBookkeepingR01
open Glennie.Compact.PositiveWordLayersR01
open Glennie.Compact.PositiveWordEndpointR01
noncomputable section
set_option autoImplicit false

def middleLinear (z : Albert) (i : Fin 3) : Albert →ₗ[ℝ] Albert :=
  if i = 0 then filterLinear z false
  else if i = 1 then filterLinear z true
  else LinearMap.id

def wordLinear (x y z : Albert) (o sy sx : Bool) (i : Fin 3) (l : Bool) :
    Albert →ₗ[ℝ] Albert :=
  let base := (middleLinear z i).comp (filterLinear x l)
  if o then (filterLinear x sx).comp ((filterLinear y sy).comp base)
  else (filterLinear y sy).comp ((filterLinear x sx).comp base)

def word (x y z v : Albert) (o sy sx : Bool) (i : Fin 3) (l : Bool) : Albert :=
  wordLinear x y z o sy sx i l v

def evaluation (p q r : Fin 3 → Albert) (a : Label) : ℝ :=
  inner (endpoint r a.2.2.2.2.2.1)
    (word (encoder p) (encoder q) (encoder r)
      (endpoint q a.2.2.2.2.2.2)
      a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2.1)

def expanded (p q r : Fin 3 → Albert) : ℝ :=
  ∑ a : Label, labelCoefficient a * evaluation p q r a

theorem middleLinear_apply (z v : Albert) (i : Fin 3) :
    middleLinear z i v = middle z v i := by
  by_cases h0 : i = 0
  · simp [middleLinear, middle, h0, filterLinear]
  · by_cases h1 : i = 1
    · simp [middleLinear, middle, h0, h1, filterLinear]
    · simp [middleLinear, middle, h0, h1]

end
end Glennie.Compact.PositiveWordDefinitionR01
