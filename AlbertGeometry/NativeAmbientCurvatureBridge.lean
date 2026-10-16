/-
Actual native ambient Levi-Civita curvature,
including every radial slot. Consumes the actual generic connection/curvature
and the preserved native derivative-defined product producer. The native
log-Hessian metric remains trace/3. No native normed-space instance is added.
-/
module

public import AlbertGeometry.AmbientCurvatureProduct
public import AlbertGeometry.NativeAmbientConnectionBridge

@[expose] public section
namespace AlbertGeometry.NativeAmbientCurvatureBridge
noncomputable section
open Module Glennie
open AlbertGeometry.Cubic
open AlbertGeometry.BasedNormDerivativeTransport
open AlbertGeometry.BasedNormAdjointTransport
open AlbertGeometry.NativeEuclideanNormBinding AlbertGeometry.NativeNormAlgebra
open AlbertGeometry.NativeCoordinateDerivatives AlbertGeometry.NativeIntrinsicProductBinding
open AlbertGeometry.NativeAmbientConnectionBridge
open AlbertGeometry.AmbientCurvatureProduct

local notation "QN" => nativeEuclideanRepresentation
local notation "en" => nativeCoordinateUnit

/-- The actual ambient native curvature, with the geometric trace/3 metric,
is minus the literal native multiplication commutator on all 27 coordinates.
The native product identity is an output of the intrinsic binding. -/
theorem nativeAmbientCurvature_eq_neg_jordan_commutator (u v w : AlbertGeometry.CubicPolynomialRepresentation.Coordinates) :
    delta (ambientCurvature QN en u v w) =
      -(jordan (delta u) (jordan (delta v) (delta w)) -
        jordan (delta v) (jordan (delta u) (delta w))) := by
  rw [ambientCurvature_at_one_eq_neg_product_commutator QN en
    nativeAmbientNormalization native_logMetric_positive, map_neg, map_sub]
  change -(delta (nativeIntrinsicProduct u (nativeIntrinsicProduct v w)) -
    delta (nativeIntrinsicProduct v (nativeIntrinsicProduct u w))) = _
  simp only [delta_nativeIntrinsicProduct]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]
variable (P : SymmetricTrilinearForm E) (e : E)
  (he : diagonalCubic P.form e = 1)
  (hp : ∀ u : E, u ≠ 0 → 0 < logHessianForm P e u u)

include he hp in
/-- A supplied/constructed norm-unit map gives native actual curvature as a
derived output. No curvature-preservation field or unknown Jordan law is input. -/
theorem nativeRecognition_ambientCurvature
    (I : BasedNormIso P e QN en) (u v w : E) :
    delta (I.equiv (ambientCurvature P e u v w)) =
      -(jordan (delta (I.equiv u))
          (jordan (delta (I.equiv v)) (delta (I.equiv w))) -
        jordan (delta (I.equiv v))
          (jordan (delta (I.equiv u)) (delta (I.equiv w)))) := by
  rw [ambientCurvature_at_one_eq_neg_product_commutator P e he hp]
  simp only [map_neg, map_sub, nativeRecognition_product P e he hp I]

/-- Norm/unit transports the actual curvature on the whole original positive
metric locus. Target positivity is derived, as in the generic theorem. -/
theorem nativeRecognition_curvature_field_pull
    (I : BasedNormIso P e QN en) (x : E)
    (hx : 0 < diagonalCubic P.form x)
    (hpx : ∀ u : E, u ≠ 0 → 0 < logHessianForm P x u u) (u v w : E) :
    I.equiv (ambientCurvature P x u v w) =
      ambientCurvature QN (I.equiv x) (I.equiv u) (I.equiv v) (I.equiv w) :=
  ambientCurvature_pull I x hx hpx u v w

end
end AlbertGeometry.NativeAmbientCurvatureBridge
