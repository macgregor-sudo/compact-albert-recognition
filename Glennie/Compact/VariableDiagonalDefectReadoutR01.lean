/- A composed noisy-readout obstruction for every isometric map into a
   dimension-parametric coordinatewise Euclidean special target. -/
module
public import Glennie.Compact.VariableDiagonalNullTargetR01
public import Glennie.Compact.NativeDefectReadoutR01

@[expose] public section
namespace Glennie.Compact.VariableDiagonalDefectReadoutR01
open Glennie
open Glennie.Compact.CyclicTraceNullR01
open Glennie.Compact.MultiplicationDefectR01
open Glennie.Compact.NativeDefectReadoutR01
open Glennie.Compact.MeasuredMarginR01
open Glennie.Compact.VariableDiagonalNullTargetR01
open Glennie.Compact.NativeNormKernel
open Glennie.Compact.ReadoutRobustnessR01
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000

def diagonalNProductLinear (n : ℕ) : Product (DiagonalN n) where
  toFun a := {
    toFun := diagonalNProduct a
    map_add' b c := by ext i; exact mul_add (a i) (b i) (c i)
    map_smul' r b := by ext i; exact mul_left_comm (a i) r (b i)
  }
  map_add' a b := by
    apply LinearMap.ext
    intro c
    ext i
    exact add_mul (a i) (b i) (c i)
  map_smul' r a := by
    apply LinearMap.ext
    intro c
    ext i
    exact mul_assoc r (a i) (c i)

@[simp] theorem diagonalNProductLinear_apply {n : ℕ} (a b : DiagonalN n) :
    diagonalNProductLinear n a b = diagonalNProduct a b := rfl

theorem diagonalN_response_zero {n : ℕ} (x y z : DiagonalN n) :
    response (diagonalNProductLinear n) x y z = 0 := by
  simpa only [response, diagonalNProductLinear_apply] using
    diagonalN_phi_zero x y z

/-- Uniform all-input product defect for any linear isometry into the
coordinatewise target, without a unitality or surjectivity premise. -/
theorem native_diagonalN_defect_response {n : ℕ}
    (f : Albert →ₗᵢ[ℝ] DiagonalN n) (μ R : ℝ) (hμ : 0 ≤ μ) (hR : 0 ≤ R)
    (hdef : ∀ a b : Albert,
      ‖f (jordan a b) - diagonalNProduct (f a) (f b)‖ ≤ μ * ‖a‖ * ‖b‖)
    (x y z : Albert) (hx : ‖x‖ ≤ R) (hy : ‖y‖ ≤ R) (hz : ‖z‖ ≤ R) :
    |phi x y z| ≤ 38 * μ * R^9 := by
  have hA : ∀ a b : Albert,
      ‖jordanLinear a b‖ ≤ ‖a‖ * ‖b‖ := by
    intro a b
    simpa only [jordanLinear_apply] using jordan_norm a b
  have hE : ∀ a b : DiagonalN n,
      ‖diagonalNProductLinear n a b‖ ≤ ‖a‖ * ‖b‖ := by
    intro a b
    simpa only [diagonalNProductLinear_apply] using diagonalN_product_norm a b
  have hUA : ∀ a b : Albert,
      ‖Q jordanLinear a b‖ ≤ ‖a‖^2 * ‖b‖ := by
    intro a b
    simpa only [native_Q_eq] using U_norm a b
  have hUE : ∀ a b : DiagonalN n,
      ‖Q (diagonalNProductLinear n) a b‖ ≤ ‖a‖^2 * ‖b‖ := by
    intro a b
    change ‖quadraticWith diagonalNProduct a b‖ ≤ _
    exact diagonalN_quadratic_norm a b
  have hdef' : ∀ a b : Albert,
      ‖f (jordanLinear a b) -
        diagonalNProductLinear n (f a) (f b)‖ ≤ μ * ‖a‖ * ‖b‖ := by
    intro a b
    simpa only [jordanLinear_apply, diagonalNProductLinear_apply] using hdef a b
  have h := response_discrepancy_radius jordanLinear (diagonalNProductLinear n)
    f hA hE hUA hUE μ hμ hdef' R hR x y z hx hy hz
  rw [native_response_eq, diagonalN_response_zero, sub_zero] at h
  exact h

private theorem frame_encoder_radius (p : Fin 3 → Albert) (hp : Frame p) :
    ‖encoder p‖ ≤ Real.sqrt 2 := by
  have hs : ‖encoder p‖^2 = 2 := (native_norm_sq _).trans (frame_encoder_norm p hp)
  have hroot : (Real.sqrt (2:ℝ))^2 = 2 := Real.sq_sqrt (by norm_num)
  nlinarith [norm_nonneg (encoder p), Real.sqrt_nonneg (2:ℝ)]

private theorem sqrt_two_pow_nine : (Real.sqrt (2:ℝ))^9 = 16 * Real.sqrt 2 := by
  calc
    (Real.sqrt (2:ℝ))^9 = ((Real.sqrt (2:ℝ))^2)^4 * Real.sqrt 2 := by ring
    _ = 16 * Real.sqrt 2 := by rw [Real.sq_sqrt (by norm_num)]; norm_num

/-- For actual ordered frames, six errors and any isometry to a concrete
coordinatewise null target give a lower bound on its uniform product defect. -/
theorem frame_noisy_diagonalN_defect_lower {n : ℕ}
    (f : Albert →ₗᵢ[ℝ] DiagonalN n)
    (T : Glennie.Compact.Affine20.Triple)
    (hT : ∀ a : Fin 3, Frame (T a))
    (noisy : Readouts) (ε μ : ℝ) (hμ : 0 ≤ μ)
    (hreadout : ErrorsAtMost noisy (exactReadouts T) ε)
    (hdef : ∀ a b : Albert,
      ‖f (jordan a b) - diagonalNProduct (f a) (f b)‖ ≤
        μ * ‖a‖ * ‖b‖) :
    (|weightedScore noisy|-12*ε)/(1216*Real.sqrt 2) ≤ μ := by
  have herr := six_readout_scalar_error T noisy ε (6*ε) hreadout le_rfl
  have h := native_diagonalN_defect_response f μ (Real.sqrt 2) hμ
    (Real.sqrt_nonneg 2) hdef
    (encoder (T 0)) (encoder (T 1)) (encoder (T 2))
    (frame_encoder_radius _ (hT 0)) (frame_encoder_radius _ (hT 1))
    (frame_encoder_radius _ (hT 2))
  have hm := Glennie.Compact.MeasuredMarginR01.scalar_margin_lower
    (noisyPhi noisy) (phi (encoder (T 0)) (encoder (T 1)) (encoder (T 2)))
    (6*ε) herr
  have h' := hm.trans h
  have hscore : |noisyPhi noisy| = |weightedScore noisy|/2 := by
    simp [noisyPhi, abs_div]
  rw [hscore, sqrt_two_pow_nine] at h'
  have hroot : 0 < Real.sqrt (2:ℝ) := Real.sqrt_pos.2 (by norm_num)
  apply (div_le_iff₀ (by positivity : 0 < 1216*Real.sqrt (2:ℝ))).2
  nlinarith

end
end Glennie.Compact.VariableDiagonalDefectReadoutR01
