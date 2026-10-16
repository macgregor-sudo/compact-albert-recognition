/- Exact arbitrary-cubic/operator dictionary for the scaled compact reference.
The dual equivalence is derived from the actual positive metric and dimension.
No Jordan or reference-invariance hypothesis is imposed on the unknown cubic. -/
module

public import AlbertRecognition.ReferenceCoordinates
public import Mathlib.LinearAlgebra.BilinearForm.Properties

@[expose] public section
namespace AlbertRecognition
noncomputable section

/-- The explicit trace/3 metric as a curried bilinear map. -/
def metricBilin : LinearMap.BilinForm ℝ V where
  toFun x :=
    { toFun := gA x
      map_add' y z := gA_add_right x y z
      map_smul' r y := by
        simpa only [RingHom.id_apply, smul_eq_mul] using gA_smul_right r x y }
  map_add' x y := by
    apply LinearMap.ext
    intro z
    exact gA_add_left x y z
  map_smul' r x := by
    simp only [RingHom.id_apply]
    apply LinearMap.ext
    intro y
    change gA (r • x) y = r * gA x y
    exact gA_smul_left r x y

@[simp] theorem metricBilin_apply (x y : V) : metricBilin x y = gA x y := rfl

theorem metric_nondegenerate : metricBilin.Nondegenerate :=
  ⟨fun x hx => (gA_self_eq_zero x).mp (hx x),
    fun x hx => (gA_self_eq_zero x).mp (hx x)⟩

/-- The metric-dual isomorphism uses the actual scaled form, not unscaled Riesz. -/
def metricDual : V ≃ₗ[ℝ] Module.Dual ℝ V := metricBilin.toDual metric_nondegenerate

@[simp] theorem metricDual_apply (x y : V) : metricDual x y = gA x y := rfl

/-- Every arbitrary symmetric trilinear form has its unique actual multiplication
operators obtained by raising one index with the specified scaled metric. -/
def KB (B : SymmetricCubic) : V →ₗ[ℝ] (V →ₗ[ℝ] V) where
  toFun x := metricDual.symm.toLinearMap.comp (B.form x)
  map_add' x y := by
    apply LinearMap.ext
    intro z
    change metricDual.symm (B.form (x + y) z) =
      metricDual.symm (B.form x z) + metricDual.symm (B.form y z)
    rw [map_add, LinearMap.add_apply, map_add]
  map_smul' r x := by
    simp only [RingHom.id_apply]
    apply LinearMap.ext
    intro y
    change metricDual.symm (B.form (r • x) y) = r • metricDual.symm (B.form x y)
    rw [map_smul, LinearMap.smul_apply, map_smul]

@[simp] theorem KB_apply (B : SymmetricCubic) (x y : V) :
    KB B x y = metricDual.symm (B.form x y) := rfl

theorem KB_pairing (B : SymmetricCubic) (x y z : V) :
    gA (KB B x y) z = B.form x y z := by
  change metricBilin
    ((metricBilin.toDual metric_nondegenerate).symm (B.form x y)) z = _
  exact LinearMap.BilinForm.apply_toDual_symm_apply _ _

theorem KB_comm (B : SymmetricCubic) (x y : V) : KB B x y = KB B y x := by
  apply metricDual.injective
  apply LinearMap.ext
  intro z
  change gA (KB B x y) z = gA (KB B y x) z
  rw [KB_pairing, KB_pairing, B.swap12]

theorem KB_selfadjoint (B : SymmetricCubic) (x y z : V) :
    gA (KB B x y) z = gA y (KB B x z) := by
  rw [gA_comm y (KB B x z), KB_pairing, KB_pairing, B.swap23]

/-- Native CA packaged as a genuine symmetric trilinear form. -/
def referenceForm : V →ₗ[ℝ] (V →ₗ[ℝ] (V →ₗ[ℝ] ℝ)) where
  toFun x := LinearMap.comp metricBilin (KA x)
  map_add' x y := by
    apply LinearMap.ext
    intro z
    apply LinearMap.ext
    intro w
    change gA (KA (x + y) z) w = gA (KA x z) w + gA (KA y z) w
    rw [map_add, LinearMap.add_apply, gA_add_left]
  map_smul' r x := by
    simp only [RingHom.id_apply]
    apply LinearMap.ext
    intro y
    apply LinearMap.ext
    intro z
    change gA (KA (r • x) y) z = r * gA (KA x y) z
    rw [map_smul, LinearMap.smul_apply, gA_smul_left]

@[simp] theorem referenceForm_apply (x y z : V) : referenceForm x y z = CA x y z := rfl

def referenceCubic : SymmetricCubic where
  form := referenceForm
  swap12 := CA_swap12
  swap23 := CA_swap23

theorem KB_referenceCubic : KB referenceCubic = KA := by
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  apply metricDual.injective
  apply LinearMap.ext
  intro z
  change gA (KB referenceCubic x y) z = gA (KA x y) z
  exact KB_pairing referenceCubic x y z

/-- Faithfulness: raising an index loses no information about an arbitrary B. -/
theorem KB_injective : Function.Injective KB := by
  intro B C h
  have hform : B.form = C.form := by
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    apply LinearMap.ext
    intro z
    rw [← KB_pairing B x y z, ← KB_pairing C x y z, h]
  cases B
  cases C
  cases hform
  rfl

/-- Native linear-operator commutator, independent of any geometric connection. -/
def operatorComm (P Q : V →ₗ[ℝ] V) : V →ₗ[ℝ] V := P.comp Q - Q.comp P

def q (B : SymmetricCubic) (x y : V) : V →ₗ[ℝ] V :=
  operatorComm (KB B x) (KB B y)

/-- Literal cyclic Jacobi map on every symmetric cubic, with no extra premises. -/
def A (T : V → V → (V →ₗ[ℝ] V)) (B : SymmetricCubic)
    (x y z : V) : V →ₗ[ℝ] V :=
  operatorComm (KB B x) (T y z) + operatorComm (KB B y) (T z x) +
    operatorComm (KB B z) (T x y)

def wedge (x y : V) : V →ₗ[ℝ] V where
  toFun z := gA y z • x - gA x z • y
  map_add' z w := by
    simp only [gA_add_right, add_smul]
    module
  map_smul' r z := by
    simp only [RingHom.id_apply, gA_smul_right, mul_smul, smul_sub]

/-- The native algebraic reference tensor; this is not a definition of the
actual Levi-Civita curvature required by the complete geometric endpoint. -/
def D (x y : V) : V →ₗ[ℝ] V := wedge x y + q referenceCubic x y

end
end AlbertRecognition
