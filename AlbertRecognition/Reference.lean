/- Native compact-Albert reference for the bounded curvature-recognition gate.
The metric is explicitly trace/3. No global metric instance is introduced.
This file does not assert the fixed-frame or geometric recognition theorem. -/
module

public import Glennie.Native.AlgebraLaws

@[expose] public section
namespace AlbertRecognition
noncomputable section

open Glennie
open scoped BigOperators

def traceLinear : Albert →ₗ[ℝ] ℝ where
  toFun := Glennie.trace
  map_add' := Glennie.trace_add
  map_smul' r x := by
    simpa only [RingHom.id_apply, smul_eq_mul] using Glennie.trace_smul r x

@[simp] theorem traceLinear_apply (x : Albert) : traceLinear x = Glennie.trace x := rfl

def traceFreeSpace : Submodule ℝ Albert := traceLinear.ker
abbrev V := traceFreeSpace

@[simp] theorem trace_V (x : V) : Glennie.trace (x : Albert) = 0 := x.property

def project : Albert →ₗ[ℝ] V where
  toFun x := ⟨Glennie.traceless x, Glennie.trace_traceless x⟩
  map_add' x y := by
    apply Subtype.ext
    change Glennie.traceless (x + y) = Glennie.traceless x + Glennie.traceless y
    simp only [Glennie.traceless, Glennie.trace_add, add_div, add_smul]
    module
  map_smul' r x := by
    apply Subtype.ext
    change Glennie.traceless (r • x) = r • Glennie.traceless x
    simp only [Glennie.traceless, Glennie.trace_smul, smul_sub, smul_smul,
      mul_div_assoc]

@[simp] theorem project_coe (x : Albert) :
    (project x : Albert) = Glennie.traceless x := rfl

@[simp] theorem project_V (x : V) : project (x : Albert) = x := by
  apply Subtype.ext
  simp only [project_coe, Glennie.traceless, trace_V, zero_div, zero_smul, sub_zero]

/-- The specified scaled trace metric, carried explicitly throughout this gate. -/
def gA (x y : V) : ℝ := Glennie.inner (x : Albert) (y : Albert) / 3

theorem gA_comm (x y : V) : gA x y = gA y x := by
  exact congrArg (fun r : ℝ => r / 3) (Glennie.inner_comm _ _)

theorem gA_add_left (x y z : V) : gA (x + y) z = gA x z + gA y z := by
  change Glennie.inner ((x : Albert) + (y : Albert)) (z : Albert) / 3 = _
  rw [Glennie.inner_add_left, add_div]
  rfl

theorem gA_add_right (x y z : V) : gA x (y + z) = gA x y + gA x z := by
  change Glennie.inner (x : Albert) ((y : Albert) + (z : Albert)) / 3 = _
  rw [Glennie.inner_add_right, add_div]
  rfl

theorem gA_smul_left (r : ℝ) (x y : V) : gA (r • x) y = r * gA x y := by
  change Glennie.inner (r • (x : Albert)) (y : Albert) / 3 = _
  rw [Glennie.inner_smul_left, mul_div_assoc]
  rfl

theorem gA_smul_right (r : ℝ) (x y : V) : gA x (r • y) = r * gA x y := by
  change Glennie.inner (x : Albert) (r • (y : Albert)) / 3 = _
  rw [Glennie.inner_smul_right, mul_div_assoc]
  rfl

theorem gA_self_nonneg (x : V) : 0 ≤ gA x x :=
  div_nonneg (Glennie.inner_self_nonneg _) (by norm_num)

theorem gA_self_eq_zero (x : V) : gA x x = 0 ↔ x = 0 := by
  constructor
  · intro hx
    have hinner : Glennie.inner (x : Albert) (x : Albert) = 0 := by
      change Glennie.inner (x : Albert) (x : Albert) / 3 = 0 at hx
      linarith
    exact Subtype.ext ((Glennie.inner_self_eq_zero _).mp hinner)
  · rintro rfl
    change Glennie.inner (0 : Albert) 0 / 3 = 0
    simp only [Glennie.inner, Glennie.jordan_zero_left, Glennie.trace]
    norm_num

/-- Orthogonal tracefree projection in the exact scale used by the target. -/
theorem project_pairing (u : Albert) (z : V) :
    gA (project u) z = Glennie.inner u (z : Albert) / 3 := by
  change Glennie.inner (Glennie.traceless u) (z : Albert) / 3 = _
  rw [Glennie.traceless, Glennie.inner_sub_left, Glennie.inner_smul_left]
  have hunit : Glennie.inner (1 : Albert) (z : Albert) = 0 := by
    simp only [Glennie.inner, Glennie.jordan_unit_left, trace_V]
  rw [hunit]
  simp only [mul_zero, sub_zero]

/-- The literal projected native Jordan multiplication, bilinear in both inputs. -/
def KA : V →ₗ[ℝ] (V →ₗ[ℝ] V) where
  toFun x :=
    { toFun := fun y => project (Glennie.jordan (x : Albert) (y : Albert))
      map_add' y z := by
        change project (Glennie.jordan (x : Albert) ((y : Albert) + (z : Albert))) = _
        rw [Glennie.jordan_add_right, map_add]
      map_smul' r y := by
        simp only [RingHom.id_apply]
        change project (Glennie.jordan (x : Albert) (r • (y : Albert))) =
          r • project (Glennie.jordan (x : Albert) (y : Albert))
        rw [Glennie.jordan_smul_right, map_smul] }
  map_add' x y := by
    apply LinearMap.ext
    intro z
    change project (Glennie.jordan ((x : Albert) + (y : Albert)) (z : Albert)) =
      project (Glennie.jordan (x : Albert) (z : Albert)) +
        project (Glennie.jordan (y : Albert) (z : Albert))
    rw [Glennie.jordan_add_left, map_add]
  map_smul' r x := by
    simp only [RingHom.id_apply]
    apply LinearMap.ext
    intro y
    change project (Glennie.jordan (r • (x : Albert)) (y : Albert)) =
      r • project (Glennie.jordan (x : Albert) (y : Albert))
    rw [Glennie.jordan_smul_left, map_smul]

@[simp] theorem KA_apply (x y : V) :
    KA x y = project (Glennie.jordan (x : Albert) (y : Albert)) := rfl

theorem KA_comm (x y : V) : KA x y = KA y x := by
  simp only [KA_apply, Glennie.jordan_comm]

def CA (x y z : V) : ℝ := gA (KA x y) z

theorem CA_eq_native (x y z : V) :
    CA x y z = Glennie.inner (Glennie.jordan (x : Albert) (y : Albert))
      (z : Albert) / 3 :=
  project_pairing _ _

theorem CA_swap12 (x y z : V) : CA x y z = CA y x z := by
  unfold CA
  rw [KA_comm]

theorem CA_swap23 (x y z : V) : CA x y z = CA x z y := by
  rw [CA_eq_native, CA_eq_native,
    Glennie.inner_jordan_associative, Glennie.inner_jordan_associative,
    Glennie.jordan_comm (y : Albert) (z : Albert)]

/-- Arbitrary symmetric real trilinear forms on the actual tracefree space.
Adjacent-swap symmetry and real multilinearity are the only fields. -/
structure SymmetricCubic where
  form : V →ₗ[ℝ] (V →ₗ[ℝ] (V →ₗ[ℝ] ℝ))
  swap12 : ∀ x y z, form x y z = form y x z
  swap23 : ∀ x y z, form x y z = form x z y

/-- Native zero-based diagonal idempotent coordinates, independent of any
spectral-decomposition or automorphic-diagonalization module. -/
def e : Fin 3 → Albert :=
  ![⟨1, 0, 0, 0, 0, 0⟩, ⟨0, 1, 0, 0, 0, 0⟩, ⟨0, 0, 1, 0, 0, 0⟩]

@[simp] theorem trace_e (i : Fin 3) : Glennie.trace (e i) = 1 := by
  fin_cases i <;> norm_num [e, Glennie.trace]

theorem e_sum_unit : e 0 + e 1 + e 2 = (1 : Albert) := by
  apply Albert.ext <;> norm_num [e, Glennie.unit]

def h (i : Fin 3) : V :=
  ⟨(1 : Albert) - (3 : ℝ) • e i, by
    change Glennie.trace ((1 : Albert) - (3 : ℝ) • e i) = 0
    rw [Glennie.trace_sub, Glennie.trace_unit, Glennie.trace_smul, trace_e]
    norm_num⟩

@[simp] theorem h_coe (i : Fin 3) :
    (h i : Albert) = (1 : Albert) - (3 : ℝ) • e i := rfl

theorem h_sum_zero : h 0 + h 1 + h 2 = 0 := by
  apply Subtype.ext
  apply Albert.ext <;> norm_num [h, e, Glennie.unit]

/-- Three native upper-entry octonion slots; the lower entries are determined
by native Hermitian conjugation, never by inherited pair multiplication. -/
def X01 : Octonion →ₗ[ℝ] V where
  toFun a := ⟨⟨0, 0, 0, a, 0, 0⟩, by change (0 : ℝ) + 0 + 0 = 0; norm_num⟩
  map_add' a b := by apply Subtype.ext; apply Albert.ext <;> simp
  map_smul' r a := by apply Subtype.ext; apply Albert.ext <;> simp

def X02 : Octonion →ₗ[ℝ] V where
  toFun a := ⟨⟨0, 0, 0, 0, a, 0⟩, by change (0 : ℝ) + 0 + 0 = 0; norm_num⟩
  map_add' a b := by apply Subtype.ext; apply Albert.ext <;> simp
  map_smul' r a := by apply Subtype.ext; apply Albert.ext <;> simp

def X12 : Octonion →ₗ[ℝ] V where
  toFun a := ⟨⟨0, 0, 0, 0, 0, a⟩, by change (0 : ℝ) + 0 + 0 = 0; norm_num⟩
  map_add' a b := by apply Subtype.ext; apply Albert.ext <;> simp
  map_smul' r a := by apply Subtype.ext; apply Albert.ext <;> simp

end
end AlbertRecognition
