/- One literal compact imaginary-unit transporter for the initial Albert gate.
-/
module
public import AlbertRecognition.Reference
public import Glennie.Native.Triality
public import Glennie.Native.RealConjugation
public import Glennie.Automorphism

@[expose] public section
namespace AlbertRecognition.Transporter
noncomputable section
open Glennie
open scoped BigOperators

/-- A specific imaginary unit in the first quaternion, using octMul throughout. -/
def imaginaryUnit : Octonion := (⟨0, 1, 0, 0⟩, 0)

theorem imaginaryUnit_norm : octNormSq imaginaryUnit = 1 := by
  norm_num [imaginaryUnit, octNormSq, Quaternion.normSq_def']

theorem imaginaryUnit_real : octRe imaginaryUnit = 0 := rfl

def halfRoot : ℝ := Real.sqrt (1 / 2)

theorem halfRoot_sq : halfRoot ^ 2 = (1 / 2 : ℝ) := by
  exact Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1 / 2)

theorem rotation_condition : halfRoot ^ 2 + (-halfRoot) ^ 2 = 1 := by
  nlinarith [halfRoot_sq]

/-- The genuine native upper-slot12 trace-one idempotent candidate. -/
def p12Plus (a : Octonion) : Albert :=
  (1 / 2 : ℝ) • (e 1 + e 2 + (X12 a : Albert))

theorem p12Plus_coordinates (a : Octonion) :
    p12Plus a = ⟨0, 1 / 2, 1 / 2, 0, 0, (1 / 2 : ℝ) • a⟩ := by
  apply Albert.ext <;> norm_num [p12Plus, e, X12]

theorem swap_image : realSwap01Automorphism.equiv (e 0) = e 1 := by
  change realConjugateAlbert realSwap01 (e 0) = e 1
  rw [realSwap01_coordinates]
  apply Albert.ext <;> simp [e, octConj]

/-- This sign is forced by column1=(0,c,-s) of the declared rotation matrix. -/
theorem rotation_e1_coordinates (c s : ℝ) :
    realConjugateAlbert (realRotation12 c s) (e 1) =
      ⟨0, c*c, s*s, 0, 0, octScalar (-(c*s))⟩ := by
  ext <;>
    simp [realConjugateAlbert, fromMatrix, matrixConjugateReal,
      matrixRowMix, matrixColMix, realRotation12, toMatrix,
      Fin.sum_univ_three, e, octRe, octScalar, octConj, smul_eq_mul] <;> ring

def realHalfRotation : CompactAutomorphism :=
  realRotation12Automorphism halfRoot (-halfRoot) rotation_condition

theorem rotation_image :
    realHalfRotation.equiv (e 1) = p12Plus (octScalar 1) := by
  change realConjugateAlbert (realRotation12 halfRoot (-halfRoot)) (e 1) = _
  rw [rotation_e1_coordinates, p12Plus_coordinates]
  have hr : halfRoot * halfRoot = (1 / 2 : ℝ) := by
    nlinarith [halfRoot_sq]
  apply Albert.ext <;> simp [hr, octScalar_smul]

theorem middle_image (a : Octonion) (ha : octNormSq a = 1) :
    (octMiddleTriple a ha).compactAutomorphism.equiv (p12Plus (octScalar 1)) =
      p12Plus a := by
  rw [p12Plus_coordinates, p12Plus_coordinates]
  change (octMiddleTriple a ha).albertEquiv _ = _
  apply Albert.ext <;>
    simp [OctRelatedTriple.albertEquiv, OctRelatedTriple.middle_B,
      octMul_smul_left, octMul_scalar_left] <;> simp [octMul]

/-- First swap, then the signed real rotation, then native middle-Moufang triality. -/
def imaginaryTransporter : CompactAutomorphism :=
  (octMiddleTriple imaginaryUnit imaginaryUnit_norm).compactAutomorphism.comp
    (realHalfRotation.comp realSwap01Automorphism)

theorem imaginaryTransporter_image :
    imaginaryTransporter.equiv (e 0) = p12Plus imaginaryUnit := by
  simp only [imaginaryTransporter, CompactAutomorphism.comp_apply]
  rw [swap_image, rotation_image, middle_image]

theorem imaginaryTransporter_h_image :
    imaginaryTransporter.equiv (h 0 : Albert) =
      (1 : Albert) - (3 : ℝ) • p12Plus imaginaryUnit := by
  rw [h_coe, map_sub, map_smul, imaginaryTransporter.map_unit,
    imaginaryTransporter_image]

end
end AlbertRecognition.Transporter
