/-
The reference form is a finite continuous tensor
on the existing Euclidean26 carrier, identified with the algebraic
referenceCubic in ALL three slots. Its symmetry is proved from the
native reference symmetries. The full native Euclidean form restriction follows
from whole diagonal equality and genuine third-derivative polarization.
The tangent is the actual DN kernel, with its ambient subspace norm. No norm
instance on native Albert/V, native isometry premise, or curvature is supplied.
-/
module

public import AlbertGeometry.NativeCoordinateDictionary
public import AlbertGeometry.CubicPolarizationUniqueness

@[expose] public section
namespace AlbertGeometry.NativeTracefreeFormBinding
noncomputable section
open Module Glennie AlbertRecognition
open AlbertGeometry.Cubic AlbertGeometry.CubicPolynomialRepresentation
open AlbertGeometry.NativeNormAlgebra AlbertGeometry.NativeEuclideanNormBinding
open AlbertGeometry.NativeCoordinateDerivatives AlbertGeometry.NativeCoordinateDictionary
open scoped BigOperators

/-- Actual coordinate basis of the existing Euclidean26 space. -/
def referenceCoordinateVector (i : Fin 26) : TracefreeCoordinates :=
  EuclideanSpace.basisFun (Fin 26) ℝ i

theorem reference_coordinate_sum (x : TracefreeCoordinates) :
    ∑ i : Fin 26, x i • referenceCoordinateVector i = x := by
  simpa only [referenceCoordinateVector, EuclideanSpace.basisFun_repr] using
    (EuclideanSpace.basisFun (Fin 26) ℝ).sum_repr x

theorem native_reference_coordinate_sum (x : TracefreeCoordinates) :
    ∑ i : Fin 26, x i • tracefreeCoordinates (referenceCoordinateVector i) =
      tracefreeCoordinates x := by
  have h := congrArg (fun y : TracefreeCoordinates => tracefreeCoordinates y)
    (reference_coordinate_sum x)
  simpa only [map_sum, map_smul] using h

/-- Literal coefficient of the reference cubic, already divided by3. -/
def referenceCoefficient (i j k : Fin 26) : ℝ :=
  referenceCubic.form (tracefreeCoordinates (referenceCoordinateVector i))
    (tracefreeCoordinates (referenceCoordinateVector j))
    (tracefreeCoordinates (referenceCoordinateVector k))

/-- All-slot algebraic expansion is proved by the curried linear maps. -/
theorem coordinateReferenceCubic_expansion (x y z : TracefreeCoordinates) :
    coordinateReferenceCubic x y z =
      ∑ i : Fin 26, ∑ j : Fin 26, ∑ k : Fin 26,
        (x i * y j * z k) * referenceCoefficient i j k := by
  change referenceCubic.form (tracefreeCoordinates x) (tracefreeCoordinates y)
    (tracefreeCoordinates z) = _
  have h1 : ∀ Y Z : V,
      referenceCubic.form
        (∑ i : Fin 26, x i • tracefreeCoordinates (referenceCoordinateVector i)) Y Z =
      ∑ i : Fin 26, x i * referenceCubic.form
        (tracefreeCoordinates (referenceCoordinateVector i)) Y Z := by
    intro Y Z
    rw [map_sum, LinearMap.sum_apply, LinearMap.sum_apply]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_smul, LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul]
  have h2 : ∀ X Z : V,
      referenceCubic.form X
        (∑ j : Fin 26, y j • tracefreeCoordinates (referenceCoordinateVector j)) Z =
      ∑ j : Fin 26, y j * referenceCubic.form X
        (tracefreeCoordinates (referenceCoordinateVector j)) Z := by
    intro X Z
    rw [map_sum, LinearMap.sum_apply]
    apply Finset.sum_congr rfl
    intro j _
    rw [map_smul, LinearMap.smul_apply, smul_eq_mul]
  have h3 : ∀ X Y : V,
      referenceCubic.form X Y
        (∑ k : Fin 26, z k • tracefreeCoordinates (referenceCoordinateVector k)) =
      ∑ k : Fin 26, z k * referenceCubic.form X Y
        (tracefreeCoordinates (referenceCoordinateVector k)) := by
    intro X Y
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [map_smul, smul_eq_mul]
  rw [← native_reference_coordinate_sum x, ← native_reference_coordinate_sum y,
    ← native_reference_coordinate_sum z, h1]
  apply Finset.sum_congr rfl
  intro i _
  rw [h2, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [h3]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  simp only [referenceCoefficient]
  ring

/-- A continuous three-slot coordinate product, without topology on native V. -/
def referenceCoordinateProduct (i j k : Fin 26) : TrilinearForm TracefreeCoordinates :=
  (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 3) ℝ).compContinuousLinearMap
    ![EuclideanSpace.proj i, EuclideanSpace.proj j, EuclideanSpace.proj k]

theorem referenceCoordinateProduct_apply (i j k : Fin 26)
    (m : Fin 3 → TracefreeCoordinates) :
    referenceCoordinateProduct i j k m = m 0 i * m 1 j * m 2 k := by
  simp [referenceCoordinateProduct, Fin.prod_univ_three, mul_assoc]

/-- Finite ordered tensor, not an assumed continuous version of referenceCubic. -/
def continuousReferenceForm : TrilinearForm TracefreeCoordinates :=
  ∑ i : Fin 26, ∑ j : Fin 26, ∑ k : Fin 26,
    referenceCoefficient i j k • referenceCoordinateProduct i j k

theorem continuousReferenceForm_apply (x y z : TracefreeCoordinates) :
    continuousReferenceForm ![x,y,z] = coordinateReferenceCubic x y z := by
  calc
    continuousReferenceForm ![x,y,z] =
      ∑ i : Fin 26, ∑ j : Fin 26, ∑ k : Fin 26,
        referenceCoefficient i j k * (x i * y j * z k) := by
      simp only [continuousReferenceForm, _root_.sum_apply,
        smul_apply, smul_eq_mul, referenceCoordinateProduct_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.tail_cons, Matrix.head_cons]
    _ = ∑ i : Fin 26, ∑ j : Fin 26, ∑ k : Fin 26,
        (x i * y j * z k) * referenceCoefficient i j k := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ = coordinateReferenceCubic x y z :=
      (coordinateReferenceCubic_expansion x y z).symm

/-- These symmetry proofs consume actual native proofs, not fields
assumed for a new unknown polynomial. -/
def continuousReferenceRepresentation : SymmetricTrilinearForm TracefreeCoordinates where
  form := continuousReferenceForm
  swap12 := by
    intro x y z
    rw [continuousReferenceForm_apply, continuousReferenceForm_apply]
    exact referenceCubic.swap12 (tracefreeCoordinates x) (tracefreeCoordinates y)
      (tracefreeCoordinates z)
  swap23 := by
    intro x y z
    rw [continuousReferenceForm_apply, continuousReferenceForm_apply]
    exact referenceCubic.swap23 (tracefreeCoordinates x) (tracefreeCoordinates y)
      (tracefreeCoordinates z)

theorem continuousReferenceRepresentation_diagonal (x : TracefreeCoordinates) :
    diagonalCubic continuousReferenceRepresentation.form x =
      nativeNewtonNorm (tracefreeCoordinates x : Albert) := by
  have hm : (fun _ : Fin 3 => x) = ![x,x,x] := by
    ext i
    fin_cases i <;> rfl
  change continuousReferenceForm (fun _ : Fin 3 => x) = _
  rw [hm, continuousReferenceForm_apply, coordinateReferenceCubic_diagonal]

/-- Actual restriction of the genuine Euclidean27 form by the constructed CLM. -/
def restrictedNativeForm : TrilinearForm TracefreeCoordinates :=
  nativeEuclideanRepresentation.form.compContinuousLinearMap
    (fun _ : Fin 3 => tracefreeCoordinateMap)

theorem restrictedNativeForm_apply (x y z : TracefreeCoordinates) :
    restrictedNativeForm ![x,y,z] = nativeEuclideanRepresentation.form
      ![tracefreeCoordinateMap x, tracefreeCoordinateMap y, tracefreeCoordinateMap z] := by
  have hm : (fun i : Fin 3 => tracefreeCoordinateMap (![x,y,z] i)) =
      ![tracefreeCoordinateMap x, tracefreeCoordinateMap y, tracefreeCoordinateMap z] := by
    funext i
    fin_cases i <;> rfl
  have hrestrict (P : TrilinearForm Coordinates) :
      P.compContinuousLinearMap (fun _ : Fin 3 => tracefreeCoordinateMap) ![x,y,z] =
      P ![tracefreeCoordinateMap x, tracefreeCoordinateMap y, tracefreeCoordinateMap z] := by
    rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
    exact congrArg (fun m : Fin 3 → Coordinates => P m) hm
  have hdef : restrictedNativeForm =
      (nativeEuclideanRepresentation.form : TrilinearForm Coordinates).compContinuousLinearMap
        (fun _ : Fin 3 => tracefreeCoordinateMap) := by
    rfl
  calc
    restrictedNativeForm ![x,y,z] =
        (nativeEuclideanRepresentation.form : TrilinearForm Coordinates).compContinuousLinearMap
          (fun _ : Fin 3 => tracefreeCoordinateMap) ![x,y,z] :=
      congrArg (fun Q : TrilinearForm TracefreeCoordinates => Q ![x,y,z]) hdef
    _ = nativeEuclideanRepresentation.form
        ![tracefreeCoordinateMap x, tracefreeCoordinateMap y, tracefreeCoordinateMap z] :=
      hrestrict (nativeEuclideanRepresentation.form : TrilinearForm Coordinates)

def restrictedNativeRepresentation : SymmetricTrilinearForm TracefreeCoordinates where
  form := restrictedNativeForm
  swap12 := by
    intro x y z
    rw [restrictedNativeForm_apply, restrictedNativeForm_apply]
    exact nativeEuclideanRepresentation.swap12 _ _ _
  swap23 := by
    intro x y z
    rw [restrictedNativeForm_apply, restrictedNativeForm_apply]
    exact nativeEuclideanRepresentation.swap23 _ _ _

theorem restrictedNativeRepresentation_diagonal (x : TracefreeCoordinates) :
    diagonalCubic restrictedNativeRepresentation.form x =
      nativeNewtonNorm (tracefreeCoordinates x : Albert) := by
  have hdiag (P : TrilinearForm Coordinates) :
      diagonalCubic
        (P.compContinuousLinearMap (fun _ : Fin 3 => tracefreeCoordinateMap)) x =
      diagonalCubic P (tracefreeCoordinateMap x) := by
    simp only [diagonalCubic, ContinuousMultilinearMap.compContinuousLinearMap_apply]
  calc
    diagonalCubic restrictedNativeRepresentation.form x =
        diagonalCubic nativeEuclideanRepresentation.form (tracefreeCoordinateMap x) :=
      hdiag nativeEuclideanRepresentation.form
    _ = nativeNewtonNorm (tracefreeCoordinates x : Albert) := by
      rw [diagonal_nativeEuclideanRepresentation, tracefreeCoordinateMap_apply,
        delta_normalizedCoordinatePoint]
      simp only [normalizedNativePoint, zero_smul, zero_add]

/-- Whole diagonal equality and actual D3 recovery prove the full CMM equality. -/
theorem restrictedNativeRepresentation_eq_reference :
    restrictedNativeRepresentation = continuousReferenceRepresentation := by
  apply symmetric_diagonalCubic_injective
  funext x
  exact (restrictedNativeRepresentation_diagonal x).trans
    (continuousReferenceRepresentation_diagonal x).symm

/-- The missing FULL three-slot native/reference dictionary, with one division3. -/
theorem nativeEuclideanForm_tracefree (x y z : TracefreeCoordinates) :
    nativeEuclideanRepresentation.form
      ![tracefreeCoordinateMap x, tracefreeCoordinateMap y, tracefreeCoordinateMap z] =
      coordinateReferenceCubic x y z := by
  calc
    nativeEuclideanRepresentation.form
      ![tracefreeCoordinateMap x, tracefreeCoordinateMap y, tracefreeCoordinateMap z] =
      restrictedNativeRepresentation.form ![x,y,z] := (restrictedNativeForm_apply x y z).symm
    _ = continuousReferenceRepresentation.form ![x,y,z] := by
      rw [restrictedNativeRepresentation_eq_reference]
    _ = coordinateReferenceCubic x y z := continuousReferenceForm_apply x y z

/-- Actual kernel of the genuine first Frechet derivative at the native unit. -/
def nativeCoordinateTangentSpace : Submodule ℝ Coordinates :=
  (fderiv ℝ coordinateNewton nativeCoordinateUnit).toLinearMap.ker

abbrev NativeCoordinateTangent := nativeCoordinateTangentSpace

/-- Constructed tangent-valued linear map from Euclidean26. -/
def tangentCoordinateLinear : TracefreeCoordinates →ₗ[ℝ] NativeCoordinateTangent :=
  tracefreeCoordinateMap.toLinearMap.codRestrict nativeCoordinateTangentSpace (by
    intro v
    change fderiv ℝ coordinateNewton nativeCoordinateUnit (tracefreeCoordinateMap v) = 0
    rw [tracefreeCoordinateMap_apply]
    exact normalizedCoordinatePoint_tangent v)

@[simp] theorem tangentCoordinateLinear_coe (v : TracefreeCoordinates) :
    (tangentCoordinateLinear v : Coordinates) = tracefreeCoordinateMap v := rfl

/-- Algebraic inverse constructed through literal native projection and basis
coordinates. Only its Euclidean/subspace endpoints are normed. -/
def tangentCoordinateInverse : NativeCoordinateTangent →ₗ[ℝ] TracefreeCoordinates :=
  (tracefreeCoordinates.symm.toLinearMap.comp (project.comp delta.toLinearMap)).comp
    nativeCoordinateTangentSpace.subtype

theorem tangentCoordinateInverse_left (v : TracefreeCoordinates) :
    tangentCoordinateInverse (tangentCoordinateLinear v) = v := by
  change tracefreeCoordinates.symm (project (delta (tracefreeCoordinateMap v))) = v
  rw [tracefreeCoordinateMap_apply, delta_normalizedCoordinatePoint,
    project_normalizedNativePoint, LinearEquiv.symm_apply_apply]

theorem tangentCoordinateInverse_right (u : NativeCoordinateTangent) :
    tangentCoordinateLinear (tangentCoordinateInverse u) = u := by
  have htrace : Glennie.trace (delta (u : Coordinates)) = 0 := by
    have hu := u.property
    change fderiv ℝ coordinateNewton nativeCoordinateUnit (u : Coordinates) = 0 at hu
    rw [fderiv_coordinateNewton_at_unit] at hu
    exact hu
  apply Subtype.ext
  change tracefreeCoordinateMap
    (tracefreeCoordinates.symm (project (delta (u : Coordinates)))) = (u : Coordinates)
  apply delta.injective
  rw [tracefreeCoordinateMap_apply, delta_normalizedCoordinatePoint]
  simp only [normalizedNativePoint, zero_smul, zero_add,
    LinearEquiv.apply_symm_apply, project_coe, Glennie.traceless, htrace,
    zero_div, zero_smul, sub_zero]

/-- Both inverse laws were proved, not supplied as an equivalence certificate. -/
def tangentCoordinates : TracefreeCoordinates ≃ₗ[ℝ] NativeCoordinateTangent where
  toFun := tangentCoordinateLinear
  invFun := tangentCoordinateInverse
  left_inv := tangentCoordinateInverse_left
  right_inv := tangentCoordinateInverse_right
  map_add' := tangentCoordinateLinear.map_add
  map_smul' := tangentCoordinateLinear.map_smul

/-- Genuine continuity in both directions from existing finite-dimensional
Euclidean and ambient-subspace topologies, not a norm on native V/Albert. -/
def tangentCoordinatesContinuous : TracefreeCoordinates ≃L[ℝ] NativeCoordinateTangent :=
  tangentCoordinates.toContinuousLinearEquiv

@[simp] theorem tangentCoordinatesContinuous_coe (v : TracefreeCoordinates) :
    (tangentCoordinatesContinuous v : Coordinates) = tracefreeCoordinateMap v := rfl

theorem tangentCoordinatesContinuous_metric (u v : TracefreeCoordinates) :
    coordinateLogMetric nativeCoordinateUnit
      (tangentCoordinatesContinuous u : Coordinates) (tangentCoordinatesContinuous v : Coordinates) =
      ∑ i : Fin 26, u i * v i := by
  rw [tangentCoordinatesContinuous_coe, tangentCoordinatesContinuous_coe]
  exact tracefreeCoordinateMap_metric u v

end
end AlbertGeometry.NativeTracefreeFormBinding
