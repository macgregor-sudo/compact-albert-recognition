module
public import Glennie.Compact.MultiplicationDefectR01
public import Glennie.Compact.NormCompatibleNullTargetR01
public import Glennie.Compact.MeasuredMarginR01
public import Glennie.Theorems.Frames

@[expose] public section
namespace Glennie.Compact.NativeDefectReadoutR01
open Glennie
open Glennie.Compact.MultiplicationDefectR01
open Glennie.Compact.CyclicTraceNullR01
open Glennie.Compact.NormCompatibleNullTargetR01
open Glennie.Compact.MeasuredMarginR01
open Glennie.Compact.NativeNormKernel
open Glennie.Compact.ReadoutRobustnessR01
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000

def diagonalProductLinear : Product Diagonal27 where
  toFun a := {
    toFun := diagonalProduct a
    map_add' b c := by
      rw [diagonal_product_comm a (b+c), diagonal_product_add_left,
        diagonal_product_comm b a, diagonal_product_comm c a]
    map_smul' r b := by
      simp only [RingHom.id_apply]
      rw [diagonal_product_comm a (r • b), diagonal_product_smul_left,
        diagonal_product_comm b a]
  }
  map_add' a b := LinearMap.ext fun c => diagonal_product_add_left a b c
  map_smul' r a := LinearMap.ext fun c => diagonal_product_smul_left r a c

@[simp] theorem diagonalProductLinear_apply (a b : Diagonal27) :
    diagonalProductLinear a b = diagonalProduct a b := rfl

@[simp] theorem native_Q_eq (a b : Albert) : Q jordanLinear a b = U a b := rfl
@[simp] theorem native_quadraticWith_eq (a b : Albert) :
    quadraticWith (fun u v => jordanLinear u v) a b = U a b := by
  simp only [quadraticWith, jordanLinear_apply, U]

@[simp] theorem native_response_eq (x y z : Albert) :
    response jordanLinear x y z = phi x y z := by
  rw [response, phiWith, phi]
  simp only [jordanLinear_apply, hilbert_inner_eq_native, quadraticWith, U]

/-- The target is cyclic trace compatible, with a proved zero response. -/
theorem diagonal_response_zero (x y z : Diagonal27) :
    response diagonalProductLinear x y z = 0 := by
  simpa only [response, diagonalProductLinear_apply] using diagonal_phi_zero x y z

/-- Actual source and concrete target norms instantiate all generic hypotheses. -/
theorem native_diagonal_defect_response (μ R : ℝ) (hμ : 0 ≤ μ) (hR : 0 ≤ R)
    (hdef : ∀ a b : Albert,
      ‖nativeToDiagonal (jordan a b) -
        diagonalProduct (nativeToDiagonal a) (nativeToDiagonal b)‖ ≤
        μ * ‖a‖ * ‖b‖)
    (x y z : Albert) (hx : ‖x‖ ≤ R) (hy : ‖y‖ ≤ R) (hz : ‖z‖ ≤ R) :
    |phi x y z| ≤ 38 * μ * R^9 := by
  have hA : ∀ a b : Albert,
      ‖jordanLinear a b‖ ≤ ‖a‖ * ‖b‖ := by
    intro a b
    simpa only [jordanLinear_apply] using jordan_norm a b
  have hE : ∀ a b : Diagonal27,
      ‖diagonalProductLinear a b‖ ≤ ‖a‖ * ‖b‖ := by
    intro a b
    simpa only [diagonalProductLinear_apply] using diagonal_product_norm a b
  have hUA : ∀ a b : Albert,
      ‖Q jordanLinear a b‖ ≤ ‖a‖^2 * ‖b‖ := by
    intro a b
    simpa only [native_Q_eq] using U_norm a b
  have hUE : ∀ a b : Diagonal27,
      ‖Q diagonalProductLinear a b‖ ≤ ‖a‖^2 * ‖b‖ := by
    intro a b
    change ‖quadraticWith diagonalProduct a b‖ ≤ _
    exact diagonal_quadratic_norm a b
  have hdef' : ∀ a b : Albert,
      ‖nativeToDiagonal (jordanLinear a b) -
        diagonalProductLinear (nativeToDiagonal a) (nativeToDiagonal b)‖ ≤
        μ * ‖a‖ * ‖b‖ := by
    intro a b
    simpa only [jordanLinear_apply, diagonalProductLinear_apply] using hdef a b
  have h := response_discrepancy_radius jordanLinear diagonalProductLinear
    nativeToDiagonal.toLinearIsometry hA hE hUA hUE μ hμ hdef' R hR x y z hx hy hz
  rw [native_response_eq, diagonal_response_zero, sub_zero] at h
  exact h

/-- A measured scalar margin obstructs an approximate map to the concrete null target. -/
theorem native_measured_defect_lower (μ R observed ξ : ℝ) (hμ : 0 ≤ μ) (hR : 0 ≤ R)
    (hdef : ∀ a b : Albert,
      ‖nativeToDiagonal (jordan a b) -
        diagonalProduct (nativeToDiagonal a) (nativeToDiagonal b)‖ ≤
        μ * ‖a‖ * ‖b‖)
    (x y z : Albert) (hx : ‖x‖ ≤ R) (hy : ‖y‖ ≤ R) (hz : ‖z‖ ≤ R)
    (herr : |observed-phi x y z| ≤ ξ) :
    |observed|-ξ ≤ 38*μ*R^9 :=
  (scalar_margin_lower observed (phi x y z) ξ herr).trans
    (native_diagonal_defect_response μ R hμ hR hdef x y z hx hy hz)

private theorem frame_encoder_radius (p : Fin 3 → Albert) (hp : Frame p) :
    ‖encoder p‖ ≤ Real.sqrt 2 := by
  have hs : ‖encoder p‖^2 = 2 := (native_norm_sq _).trans (frame_encoder_norm p hp)
  have hroot : (Real.sqrt (2:ℝ))^2 = 2 := Real.sq_sqrt (by norm_num)
  nlinarith [norm_nonneg (encoder p), Real.sqrt_nonneg (2:ℝ)]

private theorem sqrt_two_pow_nine : (Real.sqrt (2:ℝ))^9 = 16 * Real.sqrt 2 := by
  calc
    (Real.sqrt (2:ℝ))^9 = ((Real.sqrt (2:ℝ))^2)^4 * Real.sqrt 2 := by ring
    _ = 16 * Real.sqrt 2 := by rw [Real.sq_sqrt (by norm_num)]; norm_num

/-- Six raw readings on actual frames force a quantitative product defect. -/
theorem frame_noisy_defect_lower
    (T : Glennie.Compact.Affine20.Triple)
    (hT : ∀ a : Fin 3, Frame (T a))
    (noisy : Readouts) (ε μ : ℝ) (hμ : 0 ≤ μ)
    (hreadout : ErrorsAtMost noisy (exactReadouts T) ε)
    (hdef : ∀ a b : Albert,
      ‖nativeToDiagonal (jordan a b) -
        diagonalProduct (nativeToDiagonal a) (nativeToDiagonal b)‖ ≤
        μ * ‖a‖ * ‖b‖) :
    (|weightedScore noisy|-12*ε)/(1216*Real.sqrt 2) ≤ μ := by
  have herr := six_readout_scalar_error T noisy ε (6*ε) hreadout le_rfl
  have h := native_measured_defect_lower μ (Real.sqrt 2) (noisyPhi noisy)
    (6*ε) hμ (Real.sqrt_nonneg 2) hdef
    (encoder (T 0)) (encoder (T 1)) (encoder (T 2))
    (frame_encoder_radius _ (hT 0)) (frame_encoder_radius _ (hT 1))
    (frame_encoder_radius _ (hT 2)) herr
  have hscore : |noisyPhi noisy| = |weightedScore noisy|/2 := by
    simp [noisyPhi, abs_div]
  rw [hscore, sqrt_two_pow_nine] at h
  have hroot : 0 < Real.sqrt (2:ℝ) := Real.sqrt_pos.2 (by norm_num)
  apply (div_le_iff₀ (by positivity : 0 < 1216*Real.sqrt (2:ℝ))).2
  nlinarith

end
end Glennie.Compact.NativeDefectReadoutR01
