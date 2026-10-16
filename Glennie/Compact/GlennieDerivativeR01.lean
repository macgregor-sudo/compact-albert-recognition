/- Actual native differential of Phi in its third Albert argument.
All exposition and Lean code are AI-generated under Robert MacGregor's direction.
No novelty is asserted. No derivative or differentiability premise for Phi
is assumed. The native Hilbert norm and pairing are the existing raw trace ones.
-/
module

public import Glennie.Compact.GlennieScalarPotentialR01
public import Glennie.Compactness
public import Mathlib.Analysis.Calculus.FDeriv.Bilinear
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.Ring

@[expose] public section
namespace Glennie.Compact.GlennieDerivativeR01

open Glennie
open Glennie.Compact.GlennieScalarPotentialR01

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
-- Match Compactness at the native/Hilbert inherited-instance boundary.
-- This changes elaboration transparency, not the heartbeat limit or proof rules.
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

/-! ## Existing native operations as continuous linear maps -/

@[simp] theorem pairingContinuous_apply (a b : Albert) :
    nativeInnerContinuous a b = inner a b := rfl

/-- The existing native U operator, linear and continuous in its argument. -/
def UContinuous (x : Albert) : Albert →L[ℝ] Albert :=
  (2 : ℝ) • (jordanContinuous x).comp (jordanContinuous x) -
    jordanContinuous (jordan x x)

@[simp] theorem UContinuous_apply (x z : Albert) :
    UContinuous x z = U x z := rfl

/-- The actual commutator, using the scalar-potential module's definition. -/
def commUContinuous (x y : Albert) : Albert →L[ℝ] Albert :=
  (UContinuous x).comp (UContinuous y) -
    (UContinuous y).comp (UContinuous x)

@[simp] theorem commUContinuous_apply (x y z : Albert) :
    commUContinuous x y z = commU x y z := by
  simp only [commUContinuous, sub_apply, ContinuousLinearMap.comp_apply,
    UContinuous_apply, commU]

/-- A continuous linear expression for the base-variable derivative of U.
Its equality with the actual derivative is proved below. -/
def UBaseDerivative (z p : Albert) : Albert →L[ℝ] Albert :=
  (2 : ℝ) • (jordanContinuous (jordan z p) +
    (jordanContinuous z).comp (jordanContinuous p) -
    (jordanContinuous p).comp (jordanContinuous z))

@[simp] theorem UBaseDerivative_apply (z p h : Albert) :
    UBaseDerivative z p h =
      (2 : ℝ) • (jordan (jordan z p) h +
        jordan z (jordan p h) - jordan p (jordan z h)) := rfl

theorem UBaseDerivative_eq_triple (z p h : Albert) :
    UBaseDerivative z p h = doubledTriple h p z := by
  simp only [UBaseDerivative_apply, doubledTriple,
    jordan_comm z p, jordan_comm p h, jordan_comm (jordan p z) h,
    jordan_comm z (jordan h p), jordan_comm z h,
    jordan_comm p (jordan h z)]

/-! ## Actual Frechet differentiation of the native quadratic map -/

/-- Product rule for the existing native continuous bilinear Jordan product. -/
theorem hasFDerivAt_jordan
    {f g : Albert → Albert} {f' g' : Albert →L[ℝ] Albert} {z : Albert}
    (hf : HasFDerivAt f f' z) (hg : HasFDerivAt g g' z) :
    HasFDerivAt (fun w => jordan (f w) (g w))
      ((jordanContinuous (f z)).comp g' +
        (jordanContinuous (g z)).comp f') z := by
  have hp := jordanContinuous.hasFDerivAt_of_bilinear hf hg
  change HasFDerivAt (fun w => jordan (f w) (g w)) _ z at hp
  refine hp.congr_fderiv ?_
  apply ContinuousLinearMap.ext
  intro h
  change jordan (f z) (g' h) + jordan (f' h) (g z) =
    jordan (f z) (g' h) + jordan (g z) (f' h)
  rw [jordan_comm (f' h) (g z)]

/-- This differentiates w |-> U w p on the full native Albert space.
No frame, nonzero, generation, or spectral assumption occurs. -/
theorem hasFDerivAt_U_base (z p : Albert) :
    HasFDerivAt (fun w : Albert => U w p) (UBaseDerivative z p) z := by
  have hid : HasFDerivAt (fun w : Albert => w)
      (ContinuousLinearMap.id ℝ Albert) z := hasFDerivAt_id z
  have hp : HasFDerivAt (fun w : Albert => jordan w p)
      (jordanContinuous p) z := by
    have hfun : (fun w : Albert => jordan w p) =
        (jordanContinuous p : Albert → Albert) := by
      funext w
      rw [jordanContinuous_apply, jordan_comm]
    rw [hfun]
    exact (jordanContinuous p).hasFDerivAt (x := z)
  have hfirst := hasFDerivAt_jordan hid hp
  have hsquare := hasFDerivAt_jordan hid hid
  have hsecond : HasFDerivAt (fun w : Albert => jordan (jordan w w) p)
      ((jordanContinuous p).comp
        ((jordanContinuous z).comp (ContinuousLinearMap.id ℝ Albert) +
          (jordanContinuous z).comp (ContinuousLinearMap.id ℝ Albert))) z := by
    simpa only [Function.comp_def, jordanContinuous_apply, jordan_comm p] using
      (jordanContinuous p).hasFDerivAt.comp z hsquare
  have hU := (hfirst.const_smul (2 : ℝ)).sub hsecond
  have hfun :
      ((2 : ℝ) • (fun w : Albert => jordan w (jordan w p)) -
        (fun w : Albert => jordan (jordan w w) p)) =
      (fun w : Albert => U w p) := by
    funext w
    simp only [Pi.sub_apply, Pi.smul_apply, U]
  rw [hfun] at hU
  refine hU.congr_fderiv ?_
  apply ContinuousLinearMap.ext
  intro h
  simp only [sub_apply, smul_apply, add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, jordanContinuous_apply, UBaseDerivative_apply]
  rw [jordan_add_right]
  have halgebra (a b c : Albert) :
      (2 : ℝ) • (a + b) - (c + c) = (2 : ℝ) • (b + a - c) := by
    rw [smul_sub, add_comm b a, two_smul ℝ c]
  exact halgebra (jordan z (jordan p h)) (jordan (jordan z p) h)
    (jordan p (jordan z h))

theorem fderiv_U_base_apply (z p h : Albert) :
    fderiv ℝ (fun w : Albert => U w p) z h = doubledTriple h p z := by
  rw [(hasFDerivAt_U_base z p).fderiv, UBaseDerivative_eq_triple]

/-! ## Trace adjunction identifies the derivative with native G8 -/

/-- The precise adjunction needed for the variable-base U derivative. -/
theorem doubledTriple_adjoint (a h p z : Albert) :
    inner a (doubledTriple h p z) = inner h (doubledTriple a z p) := by
  have h1 : inner a (jordan h (jordan p z)) =
      inner h (jordan a (jordan z p)) := by
    rw [← inner_jordan_associative, jordan_comm a h,
      inner_jordan_associative, jordan_comm p z]
  have h2 : inner a (jordan (jordan h p) z) =
      inner h (jordan (jordan a z) p) := by
    calc
      inner a (jordan (jordan h p) z) =
          inner (jordan h p) (jordan z a) := by
        rw [inner_comm a, inner_jordan_associative]
      _ = inner h (jordan (jordan a z) p) := by
        rw [inner_jordan_associative, jordan_comm z a,
          jordan_comm p (jordan a z)]
  have h3 : inner a (jordan (jordan h z) p) =
      inner h (jordan (jordan a p) z) := by
    calc
      inner a (jordan (jordan h z) p) =
          inner (jordan h z) (jordan p a) := by
        rw [inner_comm a, inner_jordan_associative]
      _ = inner h (jordan (jordan a p) z) := by
        rw [inner_jordan_associative, jordan_comm p a,
          jordan_comm z (jordan a p)]
  simp only [doubledTriple, inner_smul_right, inner_sub_right,
    inner_add_right, h1, h2, h3]

/-- Actual native Frechet derivative of Phi in its third argument.
The derivative is proved from the bilinear product rule, not supplied as a field. -/
theorem hasFDerivAt_phi_third (x y z : Albert) :
    HasFDerivAt (fun w : Albert => phi x y w)
      (nativeInnerContinuous (glennieVector x y z)) z := by
  have hp := nativeInnerContinuous.hasFDerivAt_of_bilinear
    ((commUContinuous x y).hasFDerivAt (x := z))
    (hasFDerivAt_U_base z (jordan x y))
  have hfun : (fun w : Albert =>
      nativeInnerContinuous (commUContinuous x y w) (U w (jordan x y))) =
      (fun w : Albert => phi x y w) := by
    funext w
    simp only [pairingContinuous_apply, commUContinuous_apply, phi, commU]
  rw [hfun] at hp
  refine hp.congr_fderiv ?_
  apply ContinuousLinearMap.ext
  intro h
  simp only [add_apply, ContinuousLinearMap.precompL_apply,
    ContinuousLinearMap.precompR, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.compL_apply, pairingContinuous_apply, commUContinuous_apply]
  rw [UBaseDerivative_eq_triple, doubledTriple_adjoint,
    commU_pairing x y h (U z (jordan x y)),
    inner_comm (glennieVector x y z) h,
    glennieVector, inner_sub_right]
  ring

theorem differentiable_phi_third (x y : Albert) :
    Differentiable ℝ (fun z : Albert => phi x y z) :=
  fun z => (hasFDerivAt_phi_third x y z).differentiableAt

theorem fderiv_phi_third (x y z : Albert) :
    fderiv ℝ (fun w : Albert => phi x y w) z =
      nativeInnerContinuous (glennieVector x y z) :=
  (hasFDerivAt_phi_third x y z).fderiv

/-- d_z Phi[h] = B(h,G8), with B the actual raw native trace pairing. -/
theorem fderiv_phi_third_apply (x y z h : Albert) :
    fderiv ℝ (fun w : Albert => phi x y w) z h =
      inner h (glennieVector x y z) := by
  rw [fderiv_phi_third, pairingContinuous_apply, inner_comm]

/-- Mathlib's actual Hilbert-space gradient is the native G8 vector. -/
theorem hasGradientAt_phi_third (x y z : Albert) :
    HasGradientAt (fun w : Albert => phi x y w) (glennieVector x y z) z := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have hd : nativeInnerContinuous (glennieVector x y z) =
      InnerProductSpace.toDual ℝ Albert (glennieVector x y z) := by
    ext h
    rfl
  rw [← hd]
  exact hasFDerivAt_phi_third x y z

theorem gradient_phi_third (x y z : Albert) :
    gradient (fun w : Albert => phi x y w) z = glennieVector x y z :=
  (hasGradientAt_phi_third x y z).gradient

/-! ## Metric scaling and useful derivative consequences -/

/-- For g=B/3, the same actual derivative is represented by 3 G8.
This statement does not install a competing norm or inner-product instance. -/
theorem fderiv_phi_third_apply_scaled (x y z h : Albert) :
    fderiv ℝ (fun w : Albert => phi x y w) z h =
      (1 / 3 : ℝ) * inner h ((3 : ℝ) • glennieVector x y z) := by
  rw [fderiv_phi_third_apply, inner_smul_right]
  ring

/-- The squared g-length of its scaled representative is 3 times raw B-length. -/
theorem scaled_gradient_squared (x y z : Albert) :
    (1 / 3 : ℝ) *
        inner ((3 : ℝ) • glennieVector x y z) ((3 : ℝ) • glennieVector x y z) =
      3 * inner (glennieVector x y z) (glennieVector x y z) := by
  rw [inner_smul_left, inner_smul_right]
  ring

/-- Radial differentiation agrees with the separately proved scalar contraction. -/
theorem fderiv_phi_third_radial (x y z : Albert) :
    fderiv ℝ (fun w : Albert => phi x y w) z z = 3 * phi x y z := by
  rw [fderiv_phi_third_apply, inner_comm z, glennieVector_pairing]

/-- Third-slot criticality only; this does not assert full ambient criticality
or either direction of a generation theorem. -/
theorem fderiv_phi_third_eq_zero_iff (x y z : Albert) :
    fderiv ℝ (fun w : Albert => phi x y w) z = 0 ↔ glennieVector x y z = 0 := by
  constructor
  · intro hd
    apply (inner_self_eq_zero (glennieVector x y z)).mp
    have h := fderiv_phi_third_apply x y z (glennieVector x y z)
    rw [hd, zero_apply] at h
    exact h.symm
  · intro hg
    ext h
    rw [fderiv_phi_third_apply, hg, inner_zero_right,
      zero_apply]

/-- Chain rule for an actual differentiable curve in the third argument. -/
theorem hasDerivAt_phi_third_comp (x y : Albert)
    {c : ℝ → Albert} {c' : Albert} {t : ℝ} (hc : HasDerivAt c c' t) :
    HasDerivAt (fun s : ℝ => phi x y (c s))
      (inner c' (glennieVector x y (c t))) t := by
  simpa only [Function.comp_def, pairingContinuous_apply,
    inner_comm (glennieVector x y (c t)) c'] using
    (hasFDerivAt_phi_third x y (c t)).comp_hasDerivAt t hc

/-- The directional derivative is the derivative of the literal affine curve. -/
theorem hasDerivAt_phi_third_affine (x y z h : Albert) :
    HasDerivAt (fun t : ℝ => phi x y (z + t • h))
      (inner h (glennieVector x y z)) 0 := by
  have hlinear : HasDerivAt (fun t : ℝ => t • h) h 0 := by
    simpa only [id_eq, one_smul] using (hasDerivAt_id (0 : ℝ)).smul_const h
  have hc : HasDerivAt (fun t : ℝ => z + t • h) h 0 :=
    HasDerivAt.const_add z hlinear
  simpa only [zero_smul, add_zero] using hasDerivAt_phi_third_comp x y hc

end
end Glennie.Compact.GlennieDerivativeR01
