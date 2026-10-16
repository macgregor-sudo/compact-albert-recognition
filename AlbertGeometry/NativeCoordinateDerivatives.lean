/-
Every derivative is the actual Frechet
or scalar derivative of the coordinate Newton function. Affine-line identities
from native algebra are differentiated using real derivative rules and
uniqueness; they are not derivative fields or named coefficient definitions.
No normed native Albert instance or unknown/native equivalence is introduced.
-/
module

public import AlbertGeometry.NativeEuclideanNormBinding
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Tactic.Linarith

@[expose] public section
namespace AlbertGeometry.NativeCoordinateDerivatives
noncomputable section
open Glennie
open AlbertGeometry.Cubic AlbertGeometry.CubicPolynomialRepresentation
open AlbertGeometry.NativeNormAlgebra AlbertGeometry.NativeEuclideanNormBinding
open scoped ContDiff Topology

/-- Actual literal native Newton scalar function on the Euclidean carrier. -/
def coordinateNewton (x : Coordinates) : ℝ := nativeNewtonNorm (delta x)

theorem coordinateNewton_eq_diagonal :
    coordinateNewton = diagonalCubic nativeEuclideanRepresentation.form :=
  funext (fun x => (diagonal_nativeEuclideanRepresentation x).symm)

theorem coordinateNewton_at_unit : coordinateNewton nativeCoordinateUnit = 1 := by
  simp only [coordinateNewton, delta_nativeCoordinateUnit, nativeNewtonNorm_one]

/-- Literal actual second Frechet derivative of the literal Newton function. -/
def coordinateNewtonHessian (x : Coordinates) : Coordinates →L[ℝ] Coordinates →L[ℝ] ℝ :=
  fderiv ℝ (fderiv ℝ coordinateNewton) x

theorem coordinateNewtonHessian_eq_cubicHessian (x : Coordinates) :
    coordinateNewtonHessian x = cubicHessian nativeEuclideanRepresentation x := by
  have key := congrArg (fun f : Coordinates → ℝ => fderiv ℝ (fderiv ℝ f) x)
    coordinateNewton_eq_diagonal
  exact key

theorem hasFDerivAt_coordinateNewton (x : Coordinates) :
    HasFDerivAt coordinateNewton (fderiv ℝ coordinateNewton x) x := by
  rw [coordinateNewton_eq_diagonal]
  exact (hasFDerivAt_diagonalCubic nativeEuclideanRepresentation.form x).congr_fderiv
    (fderiv_diagonalCubic nativeEuclideanRepresentation.form x).symm

theorem hasFDerivAt_fderiv_coordinateNewton (x : Coordinates) :
    HasFDerivAt (fderiv ℝ coordinateNewton) (coordinateNewtonHessian x) x := by
  simp only [coordinateNewtonHessian, coordinateNewton_eq_diagonal]
  exact hasFDerivAt_fderiv_diagonalCubic_actual nativeEuclideanRepresentation x

private def cubicLine (a b c d t : ℝ) : ℝ := a + t*b + t^2*c + t^3*d
private def cubicLineSlope (b c d t : ℝ) : ℝ := b + (2*t)*c + (3*t^2)*d

private theorem hasDerivAt_cubicLine (a b c d t : ℝ) :
    HasDerivAt (cubicLine a b c d) (cubicLineSlope b c d t) t := by
  have h := (((hasDerivAt_const t a).add ((hasDerivAt_id t).mul_const b)).add
    ((hasDerivAt_pow 2 t).mul_const c)).add ((hasDerivAt_pow 3 t).mul_const d)
  exact h.congr_deriv (by unfold cubicLineSlope; ring)

private theorem hasDerivAt_cubicLineSlope (b c d t : ℝ) :
    HasDerivAt (cubicLineSlope b c d) (2*c + (6*t)*d) t := by
  have h := ((hasDerivAt_const t b).add
    (((hasDerivAt_id t).const_mul 2).mul_const c)).add
    (((hasDerivAt_pow 2 t).const_mul 3).mul_const d)
  exact h.congr_deriv (by ring)

/-- The genuine chain rule along an actual affine Euclidean curve. -/
theorem hasDerivAt_coordinateNewton_affine (x y : Coordinates) (t : ℝ) :
    HasDerivAt (fun s : ℝ => coordinateNewton (x + s • y))
      (fderiv ℝ coordinateNewton (x + t • y) y) t := by
  have ha : HasDerivAt (fun s : ℝ => x + s • y) y t :=
    (((hasDerivAt_id t).smul_const y).const_add x).congr_deriv (by simp)
  simpa only [Function.comp_def] using
    (hasFDerivAt_coordinateNewton (x + t • y)).comp_hasDerivAt t ha

/-- The SAME affine scalar function is globally the literal native line polynomial. -/
theorem coordinateNewton_affine_eq (x y : Coordinates) (t : ℝ) :
    coordinateNewton (x + t • y) =
      nativeNewtonNorm (delta x) + t * Glennie.inner (nativeAdjoint (delta x)) (delta y) +
        t^2 * Glennie.inner (nativeAdjoint (delta y)) (delta x) +
        t^3 * nativeNewtonNorm (delta y) := by
  simp only [coordinateNewton, map_add, map_smul]
  exact nativeNewtonNorm_line (delta x) (delta y) t

/-- Differentiate the global native line identity, then use actual derivative
uniqueness against the Frechet chain rule; no gradient is defined by this formula. -/
theorem fderiv_coordinateNewton_apply (x y : Coordinates) :
    fderiv ℝ coordinateNewton x y =
      Glennie.inner (nativeAdjoint (delta x)) (delta y) := by
  have hactual : HasDerivAt (fun t : ℝ => coordinateNewton (x + t • y))
      (fderiv ℝ coordinateNewton x y) 0 :=
    (hasDerivAt_coordinateNewton_affine x y 0).congr_deriv (by simp)
  have hpoly := hasDerivAt_cubicLine (nativeNewtonNorm (delta x))
    (Glennie.inner (nativeAdjoint (delta x)) (delta y))
    (Glennie.inner (nativeAdjoint (delta y)) (delta x))
    (nativeNewtonNorm (delta y)) 0
  have hline := hpoly.congr_of_eventuallyEq
    (Filter.Eventually.of_forall (fun t : ℝ => coordinateNewton_affine_eq x y t))
  have hcoef : HasDerivAt (fun t : ℝ => coordinateNewton (x + t • y))
      (Glennie.inner (nativeAdjoint (delta x)) (delta y)) 0 :=
    hline.congr_deriv (by unfold cubicLineSlope; ring)
  exact hactual.unique hcoef

theorem fderiv_coordinateNewton_at_unit (y : Coordinates) :
    fderiv ℝ coordinateNewton nativeCoordinateUnit y = Glennie.trace (delta y) := by
  rw [fderiv_coordinateNewton_apply, delta_nativeCoordinateUnit,
    nativeAdjoint_one, inner_unit_left]

/-- Exact unit-line identity used on a whole scalar neighborhood before
identifying the derivative-map function and taking its next derivative. -/
theorem coordinateNewton_unit_line (u : Coordinates) (t : ℝ) :
    coordinateNewton (nativeCoordinateUnit + t • u) =
      1 + t * Glennie.trace (delta u) +
        t^2 * ((Glennie.trace (delta u)^2 - Glennie.inner (delta u) (delta u)) / 2) +
        t^3 * nativeNewtonNorm (delta u) := by
  simp only [coordinateNewton, map_add, map_smul, delta_nativeCoordinateUnit]
  exact nativeNewtonNorm_unit_line (delta u) t

/-- Equality of the entire ACTUAL first derivative along the unit line. -/
theorem fderiv_coordinateNewton_unit_line (u : Coordinates) (t : ℝ) :
    fderiv ℝ coordinateNewton (nativeCoordinateUnit + t • u) u =
      Glennie.trace (delta u) +
        (2*t) * ((Glennie.trace (delta u)^2 - Glennie.inner (delta u) (delta u)) / 2) +
        (3*t^2) * nativeNewtonNorm (delta u) := by
  have hactual := hasDerivAt_coordinateNewton_affine nativeCoordinateUnit u t
  have hpoly := hasDerivAt_cubicLine 1 (Glennie.trace (delta u))
    ((Glennie.trace (delta u)^2 - Glennie.inner (delta u) (delta u)) / 2)
    (nativeNewtonNorm (delta u)) t
  have hline := hpoly.congr_of_eventuallyEq
    (Filter.Eventually.of_forall (fun s : ℝ => coordinateNewton_unit_line u s))
  exact hactual.unique hline

/-- Genuine derivative of the ACTUAL DN map, restricted along the affine line
and evaluated at a constant vector. This is the true Hessian diagonal. -/
theorem hasDerivAt_fderiv_coordinateNewton_unit_line (u : Coordinates) :
    HasDerivAt (fun t : ℝ => fderiv ℝ coordinateNewton (nativeCoordinateUnit + t • u) u)
      (coordinateNewtonHessian nativeCoordinateUnit u u) 0 := by
  have ha : HasDerivAt (fun t : ℝ => nativeCoordinateUnit + t • u) u 0 :=
    (((hasDerivAt_id (0 : ℝ)).smul_const u).const_add nativeCoordinateUnit).congr_deriv
      (by simp)
  have hDN : HasDerivAt
      (fun t : ℝ => fderiv ℝ coordinateNewton (nativeCoordinateUnit + t • u))
      (coordinateNewtonHessian nativeCoordinateUnit u) 0 := by
    simpa only [Function.comp_def] using
      (hasFDerivAt_fderiv_coordinateNewton nativeCoordinateUnit).comp_hasDerivAt_of_eq
        0 ha (by simp)
  exact (hDN.clm_apply (hasDerivAt_const (0 : ℝ) u)).congr_deriv (by simp)

/-- Twice differentiating the SAME unit-line polynomial and uniqueness yields
D²N(e)[u,u]=T(u)²-B(u,u), not an assumed Hessian coefficient. -/
theorem coordinateNewtonHessian_unit_diagonal (u : Coordinates) :
    coordinateNewtonHessian nativeCoordinateUnit u u =
      Glennie.trace (delta u)^2 - Glennie.inner (delta u) (delta u) := by
  have hpoly := hasDerivAt_cubicLineSlope (Glennie.trace (delta u))
    ((Glennie.trace (delta u)^2 - Glennie.inner (delta u) (delta u)) / 2)
    (nativeNewtonNorm (delta u)) 0
  have hline := hpoly.congr_of_eventuallyEq
    (Filter.Eventually.of_forall (fun t : ℝ => fderiv_coordinateNewton_unit_line u t))
  have hcoef : HasDerivAt
      (fun t : ℝ => fderiv ℝ coordinateNewton (nativeCoordinateUnit + t • u) u)
      (Glennie.trace (delta u)^2 - Glennie.inner (delta u) (delta u)) 0 :=
    hline.congr_deriv (by ring)
  exact (hasDerivAt_fderiv_coordinateNewton_unit_line u).unique hcoef

theorem coordinateNewtonHessian_symm (x u v : Coordinates) :
    coordinateNewtonHessian x u v = coordinateNewtonHessian x v u := by
  simp only [coordinateNewtonHessian_eq_cubicHessian]
  exact cubicHessian_symm nativeEuclideanRepresentation x u v

/-- Genuine bilinear polarization recovers the full unit Hessian from its
proved diagonal; raw B is the actual native inner pairing. -/
theorem coordinateNewtonHessian_at_unit (u v : Coordinates) :
    coordinateNewtonHessian nativeCoordinateUnit u v =
      Glennie.trace (delta u) * Glennie.trace (delta v) - Glennie.inner (delta u) (delta v) := by
  have hcross : coordinateNewtonHessian nativeCoordinateUnit (u + v) (u + v) =
      coordinateNewtonHessian nativeCoordinateUnit u u +
        coordinateNewtonHessian nativeCoordinateUnit u v +
        coordinateNewtonHessian nativeCoordinateUnit v u +
        coordinateNewtonHessian nativeCoordinateUnit v v := by
    simp only [map_add, add_apply]
    ring
  have hsum := coordinateNewtonHessian_unit_diagonal (u + v)
  rw [hcross] at hsum
  simp only [map_add, trace_add, inner_add_left, inner_add_right] at hsum
  rw [inner_comm (delta v) (delta u)] at hsum
  nlinarith [coordinateNewtonHessian_unit_diagonal u, coordinateNewtonHessian_unit_diagonal v,
    coordinateNewtonHessian_symm nativeCoordinateUnit u v]

/-- Literal actual twice-differentiated logarithm on the coordinate carrier. -/
def coordinateLogHessian (x : Coordinates) : Coordinates →L[ℝ] Coordinates →L[ℝ] ℝ :=
  fderiv ℝ (fderiv ℝ (fun y : Coordinates => Real.log (coordinateNewton y))) x

def coordinateLogMetric (x : Coordinates) : Coordinates →L[ℝ] Coordinates →L[ℝ] ℝ :=
  (-1 / 3 : ℝ) • coordinateLogHessian x

theorem coordinateLogMetric_eq_logHessianForm (x : Coordinates) :
    coordinateLogMetric x = logHessianForm nativeEuclideanRepresentation x := by
  have hlog : (fun y : Coordinates => Real.log (coordinateNewton y)) =
      logCubic nativeEuclideanRepresentation :=
    funext (fun y => congrArg Real.log (congrFun coordinateNewton_eq_diagonal y))
  have key := congrArg
    (fun f : Coordinates → ℝ => (-1 / 3 : ℝ) • fderiv ℝ (fderiv ℝ f) x) hlog
  exact key

/-- Actual log-Hessian calibration uses proved positivity N(e)=1 and genuine
log differentiation from0af. No positive-neighborhood or metric jet is assumed. -/
theorem coordinateLogMetric_at_unit (u v : Coordinates) :
    coordinateLogMetric nativeCoordinateUnit u v = Glennie.inner (delta u) (delta v) / 3 := by
  have hpos : 0 < diagonalCubic nativeEuclideanRepresentation.form nativeCoordinateUnit := by
    rw [← coordinateNewton_eq_diagonal, coordinateNewton_at_unit]
    norm_num
  rw [coordinateLogMetric_eq_logHessianForm,
    logHessianForm_apply nativeEuclideanRepresentation hpos]
  simp only [← coordinateNewtonHessian_eq_cubicHessian, ← coordinateNewton_eq_diagonal,
    coordinateNewton_at_unit, coordinateNewtonHessian_at_unit, fderiv_coordinateNewton_at_unit]
  ring

end
end AlbertGeometry.NativeCoordinateDerivatives
