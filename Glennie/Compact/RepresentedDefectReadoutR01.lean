module
public import Glennie.Compact.CompatibleDefectReadoutR01

/- Norm hypotheses here are produced
from an actual isometric associative representation, with exact cyclic-trace metric. -/
@[expose] public section
namespace Glennie.Compact.RepresentedDefectReadoutR01
open Glennie Glennie.Compact.MultiplicationDefectR01
open Glennie.Compact.CompatibleDefectReadoutR01
open Glennie.Compact.CyclicTraceNullR01
open Glennie.Compact.NormCompatibleNullTargetR01
open Glennie.Compact.ReadoutRobustnessR01
noncomputable section
set_option autoImplicit false

variable {E N : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedRing N] [NormedAlgebra ℝ N]

 theorem frame_noisy_represented_defect_lower
    (jE : Product E) (f : Albert →ₗᵢ[ℝ] E)
    (ρ : E →ₗᵢ[ℝ] N) (τ : N →ₗ[ℝ] ℝ)
    (hj : ∀ a b, ρ (jE a b) = symmProd (ρ a) (ρ b))
    (hB : ∀ a b, Inner.inner ℝ a b = τ (ρ a*ρ b))
    (hcyclic : ∀ a b : N, τ (a*b) = τ (b*a))
    (T : Glennie.Compact.Affine20.Triple) (hT : ∀ a : Fin 3, Frame (T a))
    (noisy : Readouts) (ε μ : ℝ) (hμ : 0 ≤ μ)
    (hreadout : ErrorsAtMost noisy (exactReadouts T) ε)
    (hdef : ∀ a b : Albert, ‖f (jordan a b)-jE (f a) (f b)‖ ≤ μ*‖a‖*‖b‖) :
    (|weightedScore noisy|-12*ε)/(1216*Real.sqrt 2) ≤ μ := by
  have hE : ∀ a b : E, ‖jE a b‖ ≤ ‖a‖*‖b‖ :=
    fun a b => represented_product_norm (fun u v => jE u v) ρ hj a b
  have hUE : ∀ a b : E, ‖Q jE a b‖ ≤ ‖a‖^2*‖b‖ := by
    intro a b
    exact represented_quadratic_norm (fun u v => jE u v) ρ hj a b
  exact frame_noisy_compatible_defect_lower jE f hE hUE ρ.toLinearMap τ hj hB hcyclic
    T hT noisy ε μ hμ hreadout hdef

end
end Glennie.Compact.RepresentedDefectReadoutR01
