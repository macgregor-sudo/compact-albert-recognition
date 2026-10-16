/-
Native polynomial representation. All normed/continuous objects
live on actual Euclidean27 coordinates; delta into native Albert is algebraic.
The continuous symmetric form is a genuine finite coordinate tensor sum and
its diagonal equality with literal native Newton is proved by bilinearity.
No native norm instance, native CLEquiv, assumed representation, trace law,
primitive predicate or recognition conclusion is introduced.
-/
module

public import AlbertGeometry.NativeOperatorTrace
public import AlbertGeometry.NativeNormAlgebra
public import AlbertGeometry.CubicPolynomialReconstruction
public import Mathlib.Data.Fintype.EquivFin

@[expose] public section
namespace AlbertGeometry.NativeEuclideanNormBinding
noncomputable section
open Glennie
open AlbertGeometry.Cubic AlbertGeometry.CubicPolynomialRepresentation
open AlbertGeometry.CubicPolynomialReconstruction
open AlbertGeometry.NativeOperatorTrace AlbertGeometry.NativeNormAlgebra
open scoped BigOperators ContDiff

/-- Only the order of actual full27 coordinates is chosen. -/
def fullIndexEquiv : FullIndex ≃ Fin 27 :=
  Fintype.equivFinOfCardEq fullIndex_card

/-- Reindexing is an algebraic linear equivalence with proved inverse laws. -/
def coordinateReindex : (FullIndex → ℝ) ≃ₗ[ℝ] (Fin 27 → ℝ) where
  toFun c i := c (fullIndexEquiv.symm i)
  invFun c i := c (fullIndexEquiv i)
  left_inv c := by
    ext i
    simp
  right_inv c := by
    ext i
    simp
  map_add' c d := by
    ext i
    rfl
  map_smul' r c := by
    ext i
    rfl

/-- Actual algebraic coordinates into Albert. No topology on Albert is asserted. -/
def delta : Coordinates ≃ₗ[ℝ] Albert :=
  LinearEquiv.trans
    ((EuclideanSpace.equiv (Fin 27) ℝ).toLinearEquiv.trans coordinateReindex.symm)
    fullCoordinates.symm

/-- Literal trilinear Newton polarization before supplying continuity. -/
def rawNewtonPolarization (x y z : Albert) : ℝ :=
  (Glennie.trace x * Glennie.trace y * Glennie.trace z -
    Glennie.trace x * Glennie.inner y z -
    Glennie.trace y * Glennie.inner x z -
    Glennie.trace z * Glennie.inner x y +
    2 * Glennie.inner x (jordan y z)) / 6

theorem rawNewtonPolarization_add_left (x x' y z : Albert) :
    rawNewtonPolarization (x + x') y z =
      rawNewtonPolarization x y z + rawNewtonPolarization x' y z := by
  simp only [rawNewtonPolarization, trace_add, inner_add_left]
  ring

theorem rawNewtonPolarization_smul_left (r : ℝ) (x y z : Albert) :
    rawNewtonPolarization (r • x) y z = r * rawNewtonPolarization x y z := by
  simp only [rawNewtonPolarization, trace_smul, inner_smul_left]
  ring

theorem rawNewtonPolarization_add_middle (x y y' z : Albert) :
    rawNewtonPolarization x (y + y') z =
      rawNewtonPolarization x y z + rawNewtonPolarization x y' z := by
  simp only [rawNewtonPolarization, trace_add, inner_add_left, inner_add_right,
    jordan_add_left]
  ring

theorem rawNewtonPolarization_smul_middle (r : ℝ) (x y z : Albert) :
    rawNewtonPolarization x (r • y) z = r * rawNewtonPolarization x y z := by
  simp only [rawNewtonPolarization, trace_smul, inner_smul_left, inner_smul_right,
    jordan_smul_left]
  ring

theorem rawNewtonPolarization_add_right (x y z z' : Albert) :
    rawNewtonPolarization x y (z + z') =
      rawNewtonPolarization x y z + rawNewtonPolarization x y z' := by
  simp only [rawNewtonPolarization, trace_add, inner_add_right, jordan_add_right]
  ring

theorem rawNewtonPolarization_smul_right (r : ℝ) (x y z : Albert) :
    rawNewtonPolarization x y (r • z) = r * rawNewtonPolarization x y z := by
  simp only [rawNewtonPolarization, trace_smul, inner_smul_right, jordan_smul_right]
  ring

/-- All three separately linear maps are constructed from the preceding proofs. -/
def rawPolarizationLinear : Albert →ₗ[ℝ] Albert →ₗ[ℝ] Albert →ₗ[ℝ] ℝ where
  toFun x :=
    { toFun := fun y =>
        { toFun := rawNewtonPolarization x y
          map_add' := rawNewtonPolarization_add_right x y
          map_smul' := by
            intro r z
            change rawNewtonPolarization x y (r • z) = r * rawNewtonPolarization x y z
            exact rawNewtonPolarization_smul_right r x y z }
      map_add' := by
        intro y y'
        apply LinearMap.ext
        intro z
        exact rawNewtonPolarization_add_middle x y y' z
      map_smul' := by
        intro r y
        apply LinearMap.ext
        intro z
        change rawNewtonPolarization x (r • y) z = r * rawNewtonPolarization x y z
        exact rawNewtonPolarization_smul_middle r x y z }
  map_add' := by
    intro x x'
    apply LinearMap.ext
    intro y
    apply LinearMap.ext
    intro z
    exact rawNewtonPolarization_add_left x x' y z
  map_smul' := by
    intro r x
    apply LinearMap.ext
    intro y
    apply LinearMap.ext
    intro z
    change rawNewtonPolarization (r • x) y z = r * rawNewtonPolarization x y z
    exact rawNewtonPolarization_smul_left r x y z

@[simp] theorem rawPolarizationLinear_apply (x y z : Albert) :
    rawPolarizationLinear x y z = rawNewtonPolarization x y z := rfl

theorem rawNewtonPolarization_diagonal (x : Albert) :
    rawNewtonPolarization x x x = nativeNewtonNorm x := by
  unfold rawNewtonPolarization nativeNewtonNorm
  ring

/-- Native coordinate expansion uses only the algebraic linear equivalence. -/
theorem delta_coordinate_sum (x : Coordinates) :
    ∑ i : Fin 27, x i • delta (coordinateVector i) = delta x := by
  have h := congrArg (fun y : Coordinates => delta y) (coordinate_sum x)
  simpa only [map_sum, map_smul] using h

def tensorCoefficient (i j k : Fin 27) : ℝ :=
  rawNewtonPolarization (delta (coordinateVector i)) (delta (coordinateVector j))
    (delta (coordinateVector k))

theorem rawPolarizationLinear_coordinate_expansion (x y z : Coordinates) :
    rawPolarizationLinear (delta x) (delta y) (delta z) =
      ∑ i : Fin 27, ∑ j : Fin 27, ∑ k : Fin 27,
        (x i * y j * z k) * rawPolarizationLinear (delta (coordinateVector i))
          (delta (coordinateVector j)) (delta (coordinateVector k)) := by
  have h1 : ∀ Y Z : Albert,
      rawPolarizationLinear (∑ i : Fin 27, x i • delta (coordinateVector i)) Y Z =
        ∑ i : Fin 27, x i * rawPolarizationLinear (delta (coordinateVector i)) Y Z := by
    intro Y Z
    rw [map_sum, LinearMap.sum_apply, LinearMap.sum_apply]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_smul, LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul]
  have h2 : ∀ X Z : Albert,
      rawPolarizationLinear X (∑ j : Fin 27, y j • delta (coordinateVector j)) Z =
        ∑ j : Fin 27, y j * rawPolarizationLinear X (delta (coordinateVector j)) Z := by
    intro X Z
    rw [map_sum, LinearMap.sum_apply]
    apply Finset.sum_congr rfl
    intro j _
    rw [map_smul, LinearMap.smul_apply, smul_eq_mul]
  have h3 : ∀ X Y : Albert,
      rawPolarizationLinear X Y (∑ k : Fin 27, z k • delta (coordinateVector k)) =
        ∑ k : Fin 27, z k * rawPolarizationLinear X Y (delta (coordinateVector k)) := by
    intro X Y
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [map_smul, smul_eq_mul]
  rw [← delta_coordinate_sum x, ← delta_coordinate_sum y, ← delta_coordinate_sum z, h1]
  apply Finset.sum_congr rfl
  intro i _
  rw [h2, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [h3]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem rawNewtonPolarization_coordinate_expansion (x y z : Coordinates) :
    rawNewtonPolarization (delta x) (delta y) (delta z) =
      ∑ i : Fin 27, ∑ j : Fin 27, ∑ k : Fin 27,
        (x i * y j * z k) * tensorCoefficient i j k := by
  simpa only [rawPolarizationLinear_apply, tensorCoefficient] using
    rawPolarizationLinear_coordinate_expansion x y z

/-- A real continuous trilinear map exists because it is this finite sum of
actual continuous symmetric coordinate products. -/
def nativeEuclideanForm : TrilinearForm Coordinates :=
  ∑ i : Fin 27, ∑ j : Fin 27, ∑ k : Fin 27,
    tensorCoefficient i j k • symmetricCoordinateForm i j k

theorem nativeEuclideanForm_apply (m : Fin 3 → Coordinates) :
    nativeEuclideanForm m = ∑ i : Fin 27, ∑ j : Fin 27, ∑ k : Fin 27,
      tensorCoefficient i j k * symmetricCoordinateForm i j k m := by
  simp only [nativeEuclideanForm, sum_apply, smul_apply, smul_eq_mul]

theorem nativeEuclideanForm_swap12 (x y z : Coordinates) :
    nativeEuclideanForm ![x, y, z] = nativeEuclideanForm ![y, x, z] := by
  rw [nativeEuclideanForm_apply, nativeEuclideanForm_apply]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  rw [symmetricCoordinateForm_swap12]

theorem nativeEuclideanForm_swap23 (x y z : Coordinates) :
    nativeEuclideanForm ![x, y, z] = nativeEuclideanForm ![x, z, y] := by
  rw [nativeEuclideanForm_apply, nativeEuclideanForm_apply]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  rw [symmetricCoordinateForm_swap23]

theorem nativeEuclideanForm_diagonal (x : Coordinates) :
    nativeEuclideanForm (fun _ : Fin 3 => x) = nativeNewtonNorm (delta x) := by
  rw [nativeEuclideanForm_apply]
  simp_rw [symmetricCoordinateForm_diagonal]
  calc
    (∑ i : Fin 27, ∑ j : Fin 27, ∑ k : Fin 27,
        tensorCoefficient i j k * (x i * x j * x k)) =
        ∑ i : Fin 27, ∑ j : Fin 27, ∑ k : Fin 27,
          (x i * x j * x k) * tensorCoefficient i j k := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ = rawNewtonPolarization (delta x) (delta x) (delta x) :=
      (rawNewtonPolarization_coordinate_expansion x x x).symm
    _ = nativeNewtonNorm (delta x) := rawNewtonPolarization_diagonal (delta x)

/-- Symmetry certificates are the preceding proved finite-sum identities. -/
def nativeEuclideanRepresentation : SymmetricTrilinearForm Coordinates where
  form := nativeEuclideanForm
  swap12 := nativeEuclideanForm_swap12
  swap23 := nativeEuclideanForm_swap23

/-- Literal continuous diagonal equality, not a supplied native dictionary. -/
theorem diagonal_nativeEuclideanRepresentation (x : Coordinates) :
    diagonalCubic nativeEuclideanRepresentation.form x = nativeNewtonNorm (delta x) :=
  nativeEuclideanForm_diagonal x

def nativeCoordinatePolynomial : MvPolynomial (Fin 27) ℝ :=
  reconstruction nativeEuclideanRepresentation

theorem nativeCoordinatePolynomial_homogeneous : nativeCoordinatePolynomial.IsHomogeneous 3 :=
  reconstruction_homogeneous nativeEuclideanRepresentation

theorem nativeCoordinatePolynomial_eval (x : Coordinates) :
    MvPolynomial.eval (fun i => x i) nativeCoordinatePolynomial = nativeNewtonNorm (delta x) := by
  exact (reconstruction_eval nativeEuclideanRepresentation x).trans
    (diagonal_nativeEuclideanRepresentation x)

theorem nativeCoordinatePolynomial_form_roundtrip :
    polynomialRepresentation nativeCoordinatePolynomial = nativeEuclideanRepresentation :=
  polynomialRepresentation_reconstruction nativeEuclideanRepresentation

/-- The coordinate unit is the actual inverse image of native unit. -/
def nativeCoordinateUnit : Coordinates := delta.symm (1 : Albert)

@[simp] theorem delta_nativeCoordinateUnit : delta nativeCoordinateUnit = (1 : Albert) :=
  delta.apply_symm_apply 1

theorem nativeCoordinatePolynomial_at_unit :
    MvPolynomial.eval (fun i => nativeCoordinateUnit i) nativeCoordinatePolynomial = 1 := by
  rw [nativeCoordinatePolynomial_eval, delta_nativeCoordinateUnit, nativeNewtonNorm_one]

/-- Smoothness belongs to the actual coordinate Newton function via a proved
whole-function identity, never to a postulated normed native Albert carrier. -/
theorem contDiff_nativeNewtonNorm_delta (n : ℕ∞ω) :
    ContDiff ℝ n (fun x : Coordinates => nativeNewtonNorm (delta x)) := by
  have h : (fun x : Coordinates => nativeNewtonNorm (delta x)) =
      diagonalCubic nativeEuclideanRepresentation.form :=
    funext (fun x => (diagonal_nativeEuclideanRepresentation x).symm)
  rw [h]
  exact contDiff_diagonalCubic nativeEuclideanRepresentation.form n

end
end AlbertGeometry.NativeEuclideanNormBinding
