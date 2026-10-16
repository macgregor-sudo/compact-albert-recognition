module
public import Glennie.Compact.NativeDefectReadoutR01

/- Composed generic cyclic-trace compatible target, with concrete specializations.
Source norm and response bindings use existing proved native producers.
No unit preservation, surjectivity or small-defect assumption is imposed on f. -/
@[expose] public section
namespace Glennie.Compact.CompatibleDefectReadoutR01
open Glennie Glennie.Compact.MultiplicationDefectR01
open Glennie.Compact.CyclicTraceNullR01
open Glennie.Compact.NativeNormKernel
open Glennie.Compact.NativeDefectReadoutR01
open Glennie.Compact.NormCompatibleNullTargetR01
open Glennie.Compact.ReadoutRobustnessR01
open Glennie.Compact.MeasuredMarginR01
noncomputable section
set_option autoImplicit false

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Ring M] [Algebra ℝ M]

 theorem native_compatible_defect_response
    (jE : Product E) (f : Albert →ₗᵢ[ℝ] E)
    (hE : ∀ a b, ‖jE a b‖ ≤ ‖a‖*‖b‖)
    (hUE : ∀ a b, ‖Q jE a b‖ ≤ ‖a‖^2*‖b‖)
    (ρ : E →ₗ[ℝ] M) (τ : M →ₗ[ℝ] ℝ)
    (hj : ∀ a b, ρ (jE a b) = symmProd (ρ a) (ρ b))
    (hB : ∀ a b, Inner.inner ℝ a b = τ (ρ a*ρ b))
    (hcyclic : ∀ a b : M, τ (a*b) = τ (b*a))
    (μ R : ℝ) (hμ : 0 ≤ μ) (hR : 0 ≤ R)
    (hdef : ∀ a b : Albert, ‖f (jordan a b)-jE (f a) (f b)‖ ≤ μ*‖a‖*‖b‖)
    (x y z : Albert) (hx : ‖x‖ ≤ R) (hy : ‖y‖ ≤ R) (hz : ‖z‖ ≤ R) :
    |phi x y z| ≤ 38*μ*R^9 := by
  have hA : ∀ a b : Albert, ‖jordanLinear a b‖ ≤ ‖a‖*‖b‖ := by
    intro a b
    simpa only [jordanLinear_apply] using jordan_norm a b
  have hUA : ∀ a b : Albert, ‖Q jordanLinear a b‖ ≤ ‖a‖^2*‖b‖ := by
    intro a b
    simpa only [native_Q_eq] using U_norm a b
  have hd : ∀ a b : Albert,
      ‖f (jordanLinear a b)-jE (f a) (f b)‖ ≤ μ*‖a‖*‖b‖ := by
    simpa only [jordanLinear_apply] using hdef
  have h := response_bound_of_compatible_trace jordanLinear jE f hA hE hUA hUE
    ρ τ hj hB hcyclic μ hμ hd R hR x y z hx hy hz
  simpa only [native_response_eq] using h

 theorem native_compatible_measured_defect
    (jE : Product E) (f : Albert →ₗᵢ[ℝ] E)
    (hE : ∀ a b, ‖jE a b‖ ≤ ‖a‖*‖b‖)
    (hUE : ∀ a b, ‖Q jE a b‖ ≤ ‖a‖^2*‖b‖)
    (ρ : E →ₗ[ℝ] M) (τ : M →ₗ[ℝ] ℝ)
    (hj : ∀ a b, ρ (jE a b) = symmProd (ρ a) (ρ b))
    (hB : ∀ a b, Inner.inner ℝ a b = τ (ρ a*ρ b))
    (hcyclic : ∀ a b : M, τ (a*b) = τ (b*a))
    (μ R observed ξ : ℝ) (hμ : 0 ≤ μ) (hR : 0 ≤ R)
    (hdef : ∀ a b : Albert, ‖f (jordan a b)-jE (f a) (f b)‖ ≤ μ*‖a‖*‖b‖)
    (x y z : Albert) (hx : ‖x‖ ≤ R) (hy : ‖y‖ ≤ R) (hz : ‖z‖ ≤ R)
    (herr : |observed-phi x y z| ≤ ξ) :
    |observed|-ξ ≤ 38*μ*R^9 :=
  (scalar_margin_lower observed (phi x y z) ξ herr).trans
    (native_compatible_defect_response jE f hE hUE ρ τ hj hB hcyclic
      μ R hμ hR hdef x y z hx hy hz)

private theorem frame_radius (p : Fin 3 → Albert) (hp : Frame p) :
    ‖encoder p‖ ≤ Real.sqrt 2 := by
  have hs : ‖encoder p‖^2 = 2 := (native_norm_sq _).trans (frame_encoder_norm p hp)
  have hr : (Real.sqrt (2:ℝ))^2 = 2 := Real.sq_sqrt (by norm_num)
  nlinarith [norm_nonneg (encoder p), Real.sqrt_nonneg (2:ℝ)]

private theorem sqrt_two_pow_nine : (Real.sqrt (2:ℝ))^9 = 16*Real.sqrt 2 := by
  calc
    (Real.sqrt (2:ℝ))^9 = ((Real.sqrt (2:ℝ))^2)^4*Real.sqrt 2 := by ring
    _ = 16*Real.sqrt 2 := by rw [Real.sq_sqrt (by norm_num)]; norm_num

 /-- Actual-frame six-readout measured margin for every compatible target and isometry.
The uniform defect premise ranges over ALL native inputs, not only observed marks. -/
 theorem frame_noisy_compatible_defect_lower
    (jE : Product E) (f : Albert →ₗᵢ[ℝ] E)
    (hE : ∀ a b, ‖jE a b‖ ≤ ‖a‖*‖b‖)
    (hUE : ∀ a b, ‖Q jE a b‖ ≤ ‖a‖^2*‖b‖)
    (ρ : E →ₗ[ℝ] M) (τ : M →ₗ[ℝ] ℝ)
    (hj : ∀ a b, ρ (jE a b) = symmProd (ρ a) (ρ b))
    (hB : ∀ a b, Inner.inner ℝ a b = τ (ρ a*ρ b))
    (hcyclic : ∀ a b : M, τ (a*b) = τ (b*a))
    (T : Glennie.Compact.Affine20.Triple) (hT : ∀ a : Fin 3, Frame (T a))
    (noisy : Readouts) (ε μ : ℝ) (hμ : 0 ≤ μ)
    (hreadout : ErrorsAtMost noisy (exactReadouts T) ε)
    (hdef : ∀ a b : Albert, ‖f (jordan a b)-jE (f a) (f b)‖ ≤ μ*‖a‖*‖b‖) :
    (|weightedScore noisy|-12*ε)/(1216*Real.sqrt 2) ≤ μ := by
  have herr := six_readout_scalar_error T noisy ε (6*ε) hreadout le_rfl
  have h := native_compatible_measured_defect jE f hE hUE ρ τ hj hB hcyclic
    μ (Real.sqrt 2) (noisyPhi noisy) (6*ε) hμ (Real.sqrt_nonneg 2) hdef
    (encoder (T 0)) (encoder (T 1)) (encoder (T 2))
    (frame_radius _ (hT 0)) (frame_radius _ (hT 1)) (frame_radius _ (hT 2)) herr
  have hscore : |noisyPhi noisy| = |weightedScore noisy|/2 := by
    simp [noisyPhi, abs_div]
  rw [hscore, sqrt_two_pow_nine] at h
  have hr : 0 < Real.sqrt (2:ℝ) := Real.sqrt_pos.2 (by norm_num)
  apply (div_le_iff₀ (by positivity : 0 < 1216*Real.sqrt (2:ℝ))).2
  nlinarith

end
end Glennie.Compact.CompatibleDefectReadoutR01
