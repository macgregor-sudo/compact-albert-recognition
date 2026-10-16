/- Literal compact quaternionic slice; original native U and raw trace pairing.
No generated data, differential, invariant-ring or generation assumption. -/
module

public import Glennie.Sector

@[expose] public section

namespace Glennie.QuaternionicSliceR01
noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 2000000

def qi : Quaternion ℝ := ⟨0, 1, 0, 0⟩
def qj : Quaternion ℝ := ⟨0, 0, 1, 0⟩
def qk : Quaternion ℝ := ⟨0, 0, 0, 1⟩

/-- Upper slots are 01,02,12; the native product is the half-Jordan product. -/
def sliceX : Albert := diagonalAlbert (-1) 0 1
def sliceY (r : Quaternion ℝ) : Albert :=
  ⟨0, 0, 0, (1, r), (1, 0), (1, 0)⟩
def sliceZ (s : Quaternion ℝ) : Albert :=
  ⟨0, 0, 0, (qi, s), (qj, 0), (qk, 0)⟩

/-- Explicit product argument, still bound to the actual native product below. -/
private def argumentValue (r : Quaternion ℝ) : Albert :=
  ⟨0, 0, 0, (-(1 / 2 : ℝ)) • ((1 : Quaternion ℝ), r),
    0, octScalar (1 / 2)⟩

private def commutatorValue (r s : Quaternion ℝ) : Albert :=
  ⟨0, 0, 0, (-qj, -(r * qj)),
    (qi + qk - star (star r * s), s - r * qi), (-qj, 0)⟩

private def twiceU01 (r s : Quaternion ℝ) : Octonion :=
  (⟨1 + Quaternion.normSq s, -2 * (star r * s).re, 1, 0⟩,
    (1 + Quaternion.normSq s) • r - (2 * (star r * s).re) • s + s * qk)

private def twiceU02 (r s : Quaternion ℝ) : Octonion :=
  (qi - qk - qj * (star r * s), r * qk + s * qj)

private def twiceU12 (r s : Quaternion ℝ) : Octonion :=
  (-1 - qj - qk * (star r * s), -(r * qj) - s * qk)

private theorem jordan_sliceXY (r : Quaternion ℝ) :
    jordan sliceX (sliceY r) = argumentValue r := by
  ext <;>
    simp [sliceX, sliceY, argumentValue, diagonalAlbert, jordan_d0, jordan_d1,
      jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates,
      octMul, octConj, octScalar, Quaternion.re_mul, Quaternion.imI_mul,
      Quaternion.imJ_mul, Quaternion.imK_mul, smul_eq_mul] <;>
    simp only [← Quaternion.coe_inv, Quaternion.re_coe, Quaternion.imI_coe,
      Quaternion.imJ_coe, Quaternion.imK_coe] <;> norm_num <;> ring

/-- The original two quadratic operators, not a replacement commutator. -/
private theorem commutator_formula (r s : Quaternion ℝ) :
    U sliceX (U (sliceY r) (sliceZ s)) -
      U (sliceY r) (U sliceX (sliceZ s)) = commutatorValue r s := by
  simp only [sliceX, U_diagonal]
  ext <;>
    simp [sliceY, sliceZ, commutatorValue, qi, qj, qk, U,
      jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12,
      octDot_coordinates, octMul, octConj, octScalar, Quaternion.normSq_def',
      Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
      Quaternion.imK_mul, smul_eq_mul] <;> ring

/-- Only the three slots needed by the zero-diagonal commutator are expanded. -/
private theorem twice_U_argument_o01 (r s : Quaternion ℝ) :
    ((2 : ℝ) • U (sliceZ s) (jordan sliceX (sliceY r))).o01 = twiceU01 r s := by
  rw [jordan_sliceXY]
  apply Prod.ext <;> apply Quaternion.ext <;>
    simp [sliceZ, argumentValue, twiceU01, qi, qj, qk, U,
      jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12,
      octDot_coordinates, octMul, octConj, octScalar, octNormSq, Quaternion.normSq_def',
      Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
      Quaternion.imK_mul, smul_eq_mul] <;>
    simp only [← Quaternion.coe_inv, Quaternion.re_coe, Quaternion.imI_coe,
      Quaternion.imJ_coe, Quaternion.imK_coe] <;> norm_num <;> ring

private theorem twice_U_argument_o02 (r s : Quaternion ℝ) :
    ((2 : ℝ) • U (sliceZ s) (jordan sliceX (sliceY r))).o02 = twiceU02 r s := by
  rw [jordan_sliceXY]
  apply Prod.ext <;> apply Quaternion.ext <;>
    simp [sliceZ, argumentValue, twiceU02, qi, qj, qk, U,
      jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12,
      octDot_coordinates, octMul, octConj, octScalar, octNormSq, Quaternion.normSq_def',
      Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
      Quaternion.imK_mul, smul_eq_mul] <;>
    (try simp only [← Quaternion.coe_inv, Quaternion.re_coe, Quaternion.imI_coe,
      Quaternion.imJ_coe, Quaternion.imK_coe]) <;> norm_num <;> ring

private theorem twice_U_argument_o12 (r s : Quaternion ℝ) :
    ((2 : ℝ) • U (sliceZ s) (jordan sliceX (sliceY r))).o12 = twiceU12 r s := by
  rw [jordan_sliceXY]
  apply Prod.ext <;> apply Quaternion.ext <;>
    simp [sliceZ, argumentValue, twiceU12, qi, qj, qk, U,
      jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12,
      octDot_coordinates, octMul, octConj, octScalar, octNormSq, Quaternion.normSq_def',
      Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
      Quaternion.imK_mul, smul_eq_mul] <;>
    simp only [← Quaternion.coe_inv, Quaternion.re_coe, Quaternion.imI_coe,
      Quaternion.imJ_coe, Quaternion.imK_coe] <;> norm_num <;> ring

private theorem contraction01 (r s : Quaternion ℝ) :
    octDot (commutatorValue r s).o01 (twiceU01 r s) =
      -1 + 2 * (star r * s).re * (star r * s).imJ + (star r * s).imI := by
  simp [commutatorValue, twiceU01, qi, qj, qk, octDot_coordinates,
    Quaternion.normSq_def', Quaternion.re_mul, Quaternion.imI_mul,
    Quaternion.imJ_mul, Quaternion.imK_mul, smul_eq_mul] <;> ring

private theorem contraction02 (r s : Quaternion ℝ) :
    octDot (commutatorValue r s).o02 (twiceU02 r s) =
      2 * (star r * s).imI - 2 * (star r * s).re * (star r * s).imJ := by
  simp [commutatorValue, twiceU02, qi, qj, qk, octDot_coordinates,
    Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
    Quaternion.imK_mul, smul_eq_mul] <;> ring

private theorem contraction12 (r s : Quaternion ℝ) :
    octDot (commutatorValue r s).o12 (twiceU12 r s) =
      1 + (star r * s).imI := by
  simp [commutatorValue, twiceU12, qi, qj, qk, octDot_coordinates,
    Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
    Quaternion.imK_mul, smul_eq_mul] <;> ring

private theorem contraction (r s : Quaternion ℝ) :
    inner (commutatorValue r s)
        ((2 : ℝ) • U (sliceZ s) (jordan sliceX (sliceY r))) =
      8 * (star r * s).imI := by
  rw [inner_coordinates, twice_U_argument_o01, twice_U_argument_o02,
    twice_U_argument_o12, contraction01, contraction02, contraction12]
  simp only [commutatorValue, zero_mul, zero_add] <;> ring

/-- Exact original-U scalar on the entire affine quaternionic family.
The coefficient 4 uses the raw trace pairing, whose off-diagonal weight is 2. -/
theorem quaternionicSlice_phi (r s : Quaternion ℝ) :
    phi sliceX (sliceY r) (sliceZ s) = 4 * (star r * s).imI := by
  have h : 2 * phi sliceX (sliceY r) (sliceZ s) = 8 * (star r * s).imI := by
    calc
      _ = inner (U sliceX (U (sliceY r) (sliceZ s)) -
          U (sliceY r) (U sliceX (sliceZ s)))
          ((2 : ℝ) • U (sliceZ s) (jordan sliceX (sliceY r))) := by
        exact (inner_smul_right (2 : ℝ) _ _).symm
      _ = inner (commutatorValue r s)
          ((2 : ℝ) • U (sliceZ s) (jordan sliceX (sliceY r))) := by
        rw [commutator_formula]
      _ = _ := contraction r s
  linarith

/-- The coordinate formula fixes the orientation of the quaternionic i-axis. -/
theorem quaternionicSlice_phi_coordinates (r s : Quaternion ℝ) :
    phi sliceX (sliceY r) (sliceZ s) =
      4 * (r.re * s.imI - r.imI * s.re - r.imJ * s.imK + r.imK * s.imJ) := by
  rw [quaternionicSlice_phi]
  simp [Quaternion.imI_mul] <;> ring

theorem quaternionicSlice_phi_zero_right (r : Quaternion ℝ) :
    phi sliceX (sliceY r) (sliceZ 0) = 0 := by
  rw [quaternionicSlice_phi]
  simp

theorem quaternionicSlice_phi_zero_left (s : Quaternion ℝ) :
    phi sliceX (sliceY 0) (sliceZ s) = 0 := by
  rw [quaternionicSlice_phi]
  simp

/-- A direct positive witness, with no generation conclusion imported. -/
theorem quaternionicSlice_phi_one_i :
    phi sliceX (sliceY 1) (sliceZ qi) = 4 := by
  rw [quaternionicSlice_phi]
  norm_num [qi]

theorem quaternionicSlice_phi_one_neg_i :
    phi sliceX (sliceY 1) (sliceZ (-qi)) = -4 := by
  rw [quaternionicSlice_phi]
  norm_num [qi]

theorem quaternionicSlice_phi_one_i_ne_zero :
    phi sliceX (sliceY 1) (sliceZ qi) ≠ 0 := by
  rw [quaternionicSlice_phi_one_i]
  norm_num

end
end Glennie.QuaternionicSliceR01
