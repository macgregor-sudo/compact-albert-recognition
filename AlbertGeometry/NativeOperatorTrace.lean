/- A full-native operator trace lemma; no geometry or compact fixture input.
All native operations are the literal compact quaternion-pair definitions.
No trace preservation is assumed for product-preserving linear equivalences.
-/
module

public import Glennie.Native.AlgebraLaws
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.BigOperators

@[expose] public section
namespace AlbertGeometry.NativeOperatorTrace
noncomputable section
open Module Glennie
open scoped BigOperators Quaternion

abbrev FullIndex := Fin 3 ⊕ (Fin 3 × Fin 8)

/-- Scalar coordinates of the actual quaternion-pair octonion carrier. -/
def octCoeff (u : Octonion) : Fin 8 → ℝ :=
  ![u.1.re, u.1.imI, u.1.imJ, u.1.imK,
    u.2.re, u.2.imI, u.2.imJ, u.2.imK]

def octFrom (c : Fin 8 → ℝ) : Octonion :=
  (⟨c 0, c 1, c 2, c 3⟩, ⟨c 4, c 5, c 6, c 7⟩)

/-- A genuine linear equivalence, proved by literal coordinate inverses. -/
def octCoordinates : Octonion ≃ₗ[ℝ] (Fin 8 → ℝ) where
  toFun := octCoeff
  invFun := octFrom
  left_inv u := by
    apply Prod.ext <;> apply Quaternion.ext <;> rfl
  right_inv c := by
    ext t
    fin_cases t <;> rfl
  map_add' u v := by
    ext t
    fin_cases t <;> rfl
  map_smul' r u := by
    ext t
    fin_cases t <;> rfl

@[simp] theorem octCoordinates_apply (u : Octonion) :
    octCoordinates u = octCoeff u := rfl

@[simp] theorem octCoordinates_symm_apply (c : Fin 8 → ℝ) :
    octCoordinates.symm c = octFrom c := rfl

/-- Three diagonal scalar entries followed by slots 01,02,12. -/
def fullCoeff (x : Albert) : FullIndex → ℝ
  | Sum.inl i => ![x.d0, x.d1, x.d2] i
  | Sum.inr (s,t) => octCoeff (![x.o01, x.o02, x.o12] s) t

def fullFrom (c : FullIndex → ℝ) : Albert :=
  ⟨c (Sum.inl 0), c (Sum.inl 1), c (Sum.inl 2),
    octFrom (fun t => c (Sum.inr (0,t))),
    octFrom (fun t => c (Sum.inr (1,t))),
    octFrom (fun t => c (Sum.inr (2,t)))⟩

/-- The full27 coordinate equivalence is not a tracefree restriction. -/
def fullCoordinates : Albert ≃ₗ[ℝ] (FullIndex → ℝ) where
  toFun := fullCoeff
  invFun := fullFrom
  left_inv x := by
    apply Albert.ext
    · rfl
    · rfl
    · rfl
    · apply Prod.ext <;> apply Quaternion.ext <;> rfl
    · apply Prod.ext <;> apply Quaternion.ext <;> rfl
    · apply Prod.ext <;> apply Quaternion.ext <;> rfl
  right_inv c := by
    ext i
    rcases i with j | ⟨s,t⟩
    · fin_cases j <;> rfl
    · fin_cases s <;> fin_cases t <;> rfl
  map_add' x y := by
    ext i
    rcases i with j | ⟨s,t⟩
    · fin_cases j <;> rfl
    · fin_cases s <;> fin_cases t <;> rfl
  map_smul' r x := by
    ext i
    rcases i with j | ⟨s,t⟩
    · fin_cases j <;> rfl
    · fin_cases s <;> fin_cases t <;> rfl

@[simp] theorem fullCoordinates_apply (x : Albert) :
    fullCoordinates x = fullCoeff x := rfl

@[simp] theorem fullCoordinates_symm_apply (c : FullIndex → ℝ) :
    fullCoordinates.symm c = fullFrom c := rfl

/-- All27 vectors form an actual basis because fullCoordinates is an equivalence. -/
def nativeBasis : Basis FullIndex ℝ Albert := Basis.ofEquivFun fullCoordinates

@[simp] theorem nativeBasis_repr (x : Albert) (i : FullIndex) :
    nativeBasis.repr x i = fullCoeff x i :=
  Basis.ofEquivFun_repr_apply fullCoordinates x i

@[simp] theorem nativeBasis_apply (i : FullIndex) :
    nativeBasis i = fullFrom (Pi.single i (1 : ℝ)) := by
  exact congrFun (Basis.coe_ofEquivFun fullCoordinates) i

theorem fullIndex_card : Fintype.card FullIndex = 27 := by
  simp [FullIndex]

/-- Left multiplication packaged as an actual real linear endomorphism. -/
def nativeLeft (x : Albert) : Module.End ℝ Albert where
  toFun y := jordan x y
  map_add' y z := jordan_add_right x y z
  map_smul' r y := by
    simpa only [RingHom.id_apply] using jordan_smul_right r x y

@[simp] theorem nativeLeft_apply (x y : Albert) :
    nativeLeft x y = jordan x y := rfl

def diagonalCoefficient (x : Albert) : Fin 3 → ℝ := ![x.d0, x.d1, x.d2]

def slotCoefficient (x : Albert) : Fin 3 → ℝ :=
  ![(x.d0+x.d1)/2, (x.d0+x.d2)/2, (x.d1+x.d2)/2]

/-- Only matrix diagonal coefficients are needed; no block is assumed invariant. -/
theorem matrix_diagonal_entry (x : Albert) (i : Fin 3) :
    LinearMap.toMatrix nativeBasis nativeBasis (nativeLeft x)
      (Sum.inl i) (Sum.inl i) = diagonalCoefficient x i := by
  rw [LinearMap.toMatrix_apply, nativeBasis_repr, nativeLeft_apply,
    nativeBasis_apply]
  fin_cases i <;>
    norm_num [fullCoeff, fullFrom, octFrom, octCoeff, Pi.single_apply,
      diagonalCoefficient, jordan_d0, jordan_d1, jordan_d2, octDot_coordinates]

-- Declaration-scoped resource budget for 24 literal coordinate goals.

set_option maxHeartbeats 2000000 in
/-- The matching eight scalar entries each carry half the incident diagonal sum.
Cross-slot outputs of left multiplication may be nonzero and are not discarded
as an asserted invariant-subspace decomposition. -/
theorem matrix_slot_entry (x : Albert) (s : Fin 3) (t : Fin 8) :
    LinearMap.toMatrix nativeBasis nativeBasis (nativeLeft x)
      (Sum.inr (s,t)) (Sum.inr (s,t)) = slotCoefficient x s := by
  rw [LinearMap.toMatrix_apply, nativeBasis_repr, nativeLeft_apply,
    nativeBasis_apply]
  fin_cases s <;> fin_cases t <;>
    norm_num [fullCoeff, fullFrom, octFrom, octCoeff, Pi.single_apply,
      slotCoefficient, jordan_o01, jordan_o02, jordan_o12,
      octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul,
      Quaternion.imJ_mul, Quaternion.imK_mul, smul_eq_mul] <;> ring

/-- Ordinary real trace of the literal native multiplication operator.
This factor9 identity is native-specific, with no unknown-cubic hypothesis. -/
theorem nativeLeft_trace (x : Albert) :
    LinearMap.trace ℝ Albert (nativeLeft x) = 9 * Glennie.trace x := by
  rw [LinearMap.trace_eq_matrix_trace ℝ nativeBasis]
  simp only [Matrix.trace, Matrix.diag_apply, Fintype.sum_sum_type, Fintype.sum_prod_type,
    matrix_diagonal_entry, matrix_slot_entry]
  norm_num [Fin.sum_univ_three, diagonalCoefficient, slotCoefficient,
    Glennie.trace] <;> ring

/-- Product preservation gives actual similarity of multiplication operators.
No trace, norm, metric or CompactAutomorphism field is an input. -/
theorem nativeLeft_conj (F : Albert ≃ₗ[ℝ] Albert)
    (hF : ∀ x y : Albert, F (jordan x y) = jordan (F x) (F y)) (x : Albert) :
    F.conj (nativeLeft x) = nativeLeft (F x) := by
  apply LinearMap.ext
  intro y
  change F (jordan x (F.symm y)) = jordan (F x) y
  rw [hF, F.apply_symm_apply]

/-- Derive native trace preservation for every real product automorphism.
It in particular applies to every unital one; unit preservation is not needed
for this stronger intermediate consequence of invertible product preservation. -/
theorem trace_map_of_jordan (F : Albert ≃ₗ[ℝ] Albert)
    (hF : ∀ x y : Albert, F (jordan x y) = jordan (F x) (F y)) (x : Albert) :
    Glennie.trace (F x) = Glennie.trace x := by
  have hc := LinearMap.trace_conj' (nativeLeft x) F
  rw [nativeLeft_conj F hF x, nativeLeft_trace, nativeLeft_trace] at hc
  linarith

end
end AlbertGeometry.NativeOperatorTrace
