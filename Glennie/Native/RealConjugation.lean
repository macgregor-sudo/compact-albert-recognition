/- Real matrix conjugation for the explicit binary octonion matrix product.
Only real scalar associativity is used; no octonion matrix associativity is assumed.
-/
module

public import Glennie.Native.AlgebraLaws
public import Glennie.Obligations

@[expose] public section

open scoped BigOperators

namespace Glennie
noncomputable section

set_option maxHeartbeats 2000000

def matrixRowMix (Q : Matrix (Fin 3) (Fin 3) ℝ)
    (A : Matrix (Fin 3) (Fin 3) Octonion) : Matrix (Fin 3) (Fin 3) Octonion :=
  fun i j => ∑ a, Q i a • A a j

def matrixColMix (Q : Matrix (Fin 3) (Fin 3) ℝ)
    (A : Matrix (Fin 3) (Fin 3) Octonion) : Matrix (Fin 3) (Fin 3) Octonion :=
  fun i j => ∑ a, Q j a • A i a

def matrixConjugateReal (Q : Matrix (Fin 3) (Fin 3) ℝ)
    (A : Matrix (Fin 3) (Fin 3) Octonion) : Matrix (Fin 3) (Fin 3) Octonion :=
  matrixRowMix Q (matrixColMix Q A)

def RealColumnsOrthogonal (Q : Matrix (Fin 3) (Fin 3) ℝ) : Prop :=
  ∀ a b, ∑ k, Q k a * Q k b = if a = b then 1 else 0

theorem octMul_sum_left (f : Fin 3 → Octonion) (z : Octonion) :
    octMul (∑ i, f i) z = ∑ i, octMul (f i) z := by
  simp [Fin.sum_univ_three, octMul_add_left]

theorem octMul_sum_right (z : Octonion) (f : Fin 3 → Octonion) :
    octMul z (∑ i, f i) = ∑ i, octMul z (f i) := by
  simp [Fin.sum_univ_three, octMul_add_right]

theorem matrixMul_rowMix_left (Q : Matrix (Fin 3) (Fin 3) ℝ)
    (A B : Matrix (Fin 3) (Fin 3) Octonion) :
    matrixMul (matrixRowMix Q A) B = matrixRowMix Q (matrixMul A B) := by
  apply Matrix.ext
  intro i j
  simp only [matrixMul, matrixRowMix, octMul_sum_left, octMul_smul_left,
    Finset.smul_sum]
  rw [Finset.sum_comm]

theorem matrixMul_colMix_right (Q : Matrix (Fin 3) (Fin 3) ℝ)
    (A B : Matrix (Fin 3) (Fin 3) Octonion) :
    matrixMul A (matrixColMix Q B) = matrixColMix Q (matrixMul A B) := by
  apply Matrix.ext
  intro i j
  simp only [matrixMul, matrixColMix, octMul_sum_right, octMul_smul_right,
    Finset.smul_sum]
  rw [Finset.sum_comm]

theorem matrixMul_colMix_rowMix (Q : Matrix (Fin 3) (Fin 3) ℝ)
    (hQ : RealColumnsOrthogonal Q)
    (A B : Matrix (Fin 3) (Fin 3) Octonion) :
    matrixMul (matrixColMix Q A) (matrixRowMix Q B) = matrixMul A B := by
  apply Matrix.ext
  intro i j
  simp only [matrixMul, matrixColMix, matrixRowMix,
    octMul_sum_left, octMul_sum_right, octMul_smul_left, octMul_smul_right,
    Finset.smul_sum, smul_smul]
  calc
    (∑ k, ∑ b, ∑ a, (Q k b * Q k a) • octMul (A i a) (B b j)) =
        ∑ k, ∑ a, ∑ b, (Q k a * Q k b) • octMul (A i a) (B b j) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.sum_comm]
      simp only [mul_comm]
    _ =
        ∑ a, ∑ b, ∑ k, (Q k a * Q k b) • octMul (A i a) (B b j) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
    _ = ∑ a, ∑ b, (∑ k, Q k a * Q k b) • octMul (A i a) (B b j) := by
      simp only [Finset.sum_smul]
    _ = ∑ a, octMul (A i a) (B a j) := by
      apply Finset.sum_congr rfl
      intro a _
      simp only [hQ a, ite_smul, one_smul, zero_smul]
      simp [eq_comm]

theorem matrixConjugateReal_mul (Q : Matrix (Fin 3) (Fin 3) ℝ)
    (hQ : RealColumnsOrthogonal Q)
    (A B : Matrix (Fin 3) (Fin 3) Octonion) :
    matrixMul (matrixConjugateReal Q A) (matrixConjugateReal Q B) =
      matrixConjugateReal Q (matrixMul A B) := by
  rw [matrixConjugateReal, matrixConjugateReal, matrixMul_rowMix_left,
    matrixMul_colMix_rowMix Q hQ, matrixMul_colMix_right]
  rfl

theorem matrixConjugateReal_hermitian (Q : Matrix (Fin 3) (Fin 3) ℝ)
    (A : Matrix (Fin 3) (Fin 3) Octonion)
    (hA : ∀ i j, octConj (A i j) = A j i) (i j : Fin 3) :
    octConj (matrixConjugateReal Q A i j) = matrixConjugateReal Q A j i := by
  simp only [matrixConjugateReal, matrixRowMix, matrixColMix,
    octConj_sum, octConj_smul, hA, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [mul_comm]

theorem matrixRowMix_add (Q : Matrix (Fin 3) (Fin 3) ℝ)
    (A B : Matrix (Fin 3) (Fin 3) Octonion) :
    matrixRowMix Q (A+B) = matrixRowMix Q A + matrixRowMix Q B := by
  apply Matrix.ext
  intro i j
  simp [matrixRowMix, Matrix.add_apply, smul_add, Finset.sum_add_distrib]

theorem matrixColMix_add (Q : Matrix (Fin 3) (Fin 3) ℝ)
    (A B : Matrix (Fin 3) (Fin 3) Octonion) :
    matrixColMix Q (A+B) = matrixColMix Q A + matrixColMix Q B := by
  apply Matrix.ext
  intro i j
  simp [matrixColMix, Matrix.add_apply, smul_add, Finset.sum_add_distrib]

theorem matrixRowMix_smul (Q : Matrix (Fin 3) (Fin 3) ℝ)
    (r : ℝ) (A : Matrix (Fin 3) (Fin 3) Octonion) :
    matrixRowMix Q (r • A) = r • matrixRowMix Q A := by
  apply Matrix.ext
  intro i j
  simp [matrixRowMix, Matrix.smul_apply, Finset.smul_sum, smul_smul, mul_comm]

theorem matrixColMix_smul (Q : Matrix (Fin 3) (Fin 3) ℝ)
    (r : ℝ) (A : Matrix (Fin 3) (Fin 3) Octonion) :
    matrixColMix Q (r • A) = r • matrixColMix Q A := by
  apply Matrix.ext
  intro i j
  simp [matrixColMix, Matrix.smul_apply, Finset.smul_sum, smul_smul, mul_comm]

theorem matrixConjugateReal_add (Q : Matrix (Fin 3) (Fin 3) ℝ)
    (A B : Matrix (Fin 3) (Fin 3) Octonion) :
    matrixConjugateReal Q (A+B) = matrixConjugateReal Q A + matrixConjugateReal Q B := by
  simp only [matrixConjugateReal, matrixRowMix_add, matrixColMix_add]

theorem matrixConjugateReal_smul (Q : Matrix (Fin 3) (Fin 3) ℝ)
    (r : ℝ) (A : Matrix (Fin 3) (Fin 3) Octonion) :
    matrixConjugateReal Q (r • A) = r • matrixConjugateReal Q A := by
  simp only [matrixConjugateReal, matrixRowMix_smul, matrixColMix_smul]

theorem matrixRowMix_comp (P Q : Matrix (Fin 3) (Fin 3) ℝ)
    (A : Matrix (Fin 3) (Fin 3) Octonion) :
    matrixRowMix P (matrixRowMix Q A) = matrixRowMix (P*Q) A := by
  apply Matrix.ext
  intro i j
  simp only [matrixRowMix, Matrix.mul_apply, Finset.smul_sum, smul_smul,
    Finset.sum_smul]
  rw [Finset.sum_comm]

theorem matrixColMix_comp (P Q : Matrix (Fin 3) (Fin 3) ℝ)
    (A : Matrix (Fin 3) (Fin 3) Octonion) :
    matrixColMix P (matrixColMix Q A) = matrixColMix (P*Q) A := by
  apply Matrix.ext
  intro i j
  simp only [matrixColMix, Matrix.mul_apply, Finset.smul_sum, smul_smul,
    Finset.sum_smul]
  rw [Finset.sum_comm]

theorem matrixColMix_rowMix (P Q : Matrix (Fin 3) (Fin 3) ℝ)
    (A : Matrix (Fin 3) (Fin 3) Octonion) :
    matrixColMix P (matrixRowMix Q A) = matrixRowMix Q (matrixColMix P A) := by
  apply Matrix.ext
  intro i j
  simp only [matrixColMix, matrixRowMix, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp only [mul_comm]

theorem matrixConjugateReal_comp (P Q : Matrix (Fin 3) (Fin 3) ℝ)
    (A : Matrix (Fin 3) (Fin 3) Octonion) :
    matrixConjugateReal P (matrixConjugateReal Q A) = matrixConjugateReal (P*Q) A := by
  simp only [matrixConjugateReal, matrixColMix_rowMix, matrixRowMix_comp,
    matrixColMix_comp]

theorem matrixConjugateReal_one (A : Matrix (Fin 3) (Fin 3) Octonion) :
    matrixConjugateReal 1 A = A := by
  apply Matrix.ext
  intro i j
  simp [matrixConjugateReal, matrixRowMix, matrixColMix, Matrix.one_apply]

theorem real_transpose_mul_self (Q : Matrix (Fin 3) (Fin 3) ℝ)
    (hQ : RealColumnsOrthogonal Q) : Q.transpose * Q = 1 := by
  apply Matrix.ext
  intro i j
  simpa [Matrix.mul_apply, Matrix.one_apply, eq_comm] using hQ i j

theorem matrixConjugateReal_inverse (Q : Matrix (Fin 3) (Fin 3) ℝ)
    (hQ : RealColumnsOrthogonal Q) (A : Matrix (Fin 3) (Fin 3) Octonion) :
    matrixConjugateReal Q.transpose (matrixConjugateReal Q A) = A := by
  rw [matrixConjugateReal_comp, real_transpose_mul_self Q hQ,
    matrixConjugateReal_one]

theorem toMatrix_add (x y : Albert) : toMatrix (x+y) = toMatrix x+toMatrix y := by
  apply Matrix.ext
  intro i j
  change toMatrix (x+y) i j = toMatrix x i j + toMatrix y i j
  fin_cases i <;> fin_cases j <;>
    simp [toMatrix, octScalar, octConj_add]

theorem toMatrix_smul (r : ℝ) (x : Albert) : toMatrix (r • x) = r • toMatrix x := by
  apply Matrix.ext
  intro i j
  change toMatrix (r • x) i j = r • toMatrix x i j
  fin_cases i <;> fin_cases j <;>
    simp [toMatrix, octConj_smul, ← octScalar_smul, smul_eq_mul]

theorem fromMatrix_add (A B : Matrix (Fin 3) (Fin 3) Octonion) :
    fromMatrix (A+B) = fromMatrix A+fromMatrix B := by
  apply Albert.ext <;> rfl

theorem fromMatrix_smul (r : ℝ) (A : Matrix (Fin 3) (Fin 3) Octonion) :
    fromMatrix (r • A) = r • fromMatrix A := by
  apply Albert.ext <;> rfl

def realConjugateAlbert (Q : Matrix (Fin 3) (Fin 3) ℝ) (x : Albert) : Albert :=
  fromMatrix (matrixConjugateReal Q (toMatrix x))

theorem toMatrix_realConjugateAlbert (Q : Matrix (Fin 3) (Fin 3) ℝ) (x : Albert) :
    toMatrix (realConjugateAlbert Q x) = matrixConjugateReal Q (toMatrix x) :=
  toMatrix_fromMatrix_hermitian _ (matrixConjugateReal_hermitian Q _ (toMatrix_hermitian x))

theorem realConjugateAlbert_jordan (Q : Matrix (Fin 3) (Fin 3) ℝ)
    (hQ : RealColumnsOrthogonal Q) (x y : Albert) :
    realConjugateAlbert Q (jordan x y) =
      jordan (realConjugateAlbert Q x) (realConjugateAlbert Q y) := by
  apply toMatrix_injective
  simp only [toMatrix_realConjugateAlbert, toMatrix_jordan,
    matrixConjugateReal_smul, matrixConjugateReal_add,
    matrixConjugateReal_mul Q hQ]

def realConjugateAlbertEquiv (Q : Matrix (Fin 3) (Fin 3) ℝ)
    (hQ : RealColumnsOrthogonal Q) (hQt : RealColumnsOrthogonal Q.transpose) :
    Albert ≃ₗ[ℝ] Albert where
  toFun := realConjugateAlbert Q
  invFun := realConjugateAlbert Q.transpose
  left_inv x := by
    apply toMatrix_injective
    rw [toMatrix_realConjugateAlbert, toMatrix_realConjugateAlbert,
      matrixConjugateReal_inverse Q hQ]
  right_inv x := by
    apply toMatrix_injective
    rw [toMatrix_realConjugateAlbert, toMatrix_realConjugateAlbert]
    simpa only [Matrix.transpose_transpose] using matrixConjugateReal_inverse Q.transpose hQt (toMatrix x)
  map_add' x y := by
    simp only [realConjugateAlbert, toMatrix_add, matrixConjugateReal_add, fromMatrix_add]
  map_smul' r x := by
    simp only [realConjugateAlbert, toMatrix_smul, matrixConjugateReal_smul, fromMatrix_smul, RingHom.id_apply]

theorem matrixConjugateReal_diagonal_sum (Q : Matrix (Fin 3) (Fin 3) ℝ)
    (hQ : RealColumnsOrthogonal Q) (A : Matrix (Fin 3) (Fin 3) Octonion) :
    (∑ i, matrixConjugateReal Q A i i) = ∑ i, A i i := by
  simp only [matrixConjugateReal, matrixRowMix, matrixColMix, Finset.smul_sum, smul_smul]
  calc
    (∑ i, ∑ a, ∑ b, (Q i a * Q i b) • A a b) =
        ∑ a, ∑ b, ∑ i, (Q i a * Q i b) • A a b := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
    _ = ∑ a, ∑ b, (∑ i, Q i a * Q i b) • A a b := by
      simp only [Finset.sum_smul]
    _ = ∑ a, A a a := by
      apply Finset.sum_congr rfl
      intro a _
      simp only [hQ a, ite_smul, one_smul, zero_smul]
      simp [eq_comm]

theorem realConjugateAlbert_trace (Q : Matrix (Fin 3) (Fin 3) ℝ)
    (hQ : RealColumnsOrthogonal Q) (x : Albert) :
    trace (realConjugateAlbert Q x) = trace x := by
  have h := congrArg octRe (matrixConjugateReal_diagonal_sum Q hQ (toMatrix x))
  simpa [Fin.sum_univ_three, realConjugateAlbert, fromMatrix, trace, toMatrix, octRe, octScalar] using h

/-- Actual native automorphism, with both orthogonality identities checked by its caller. -/
def realOrthogonalAutomorphism (Q : Matrix (Fin 3) (Fin 3) ℝ)
    (hQ : RealColumnsOrthogonal Q) (hQt : RealColumnsOrthogonal Q.transpose) :
    CompactAutomorphism where
  equiv := realConjugateAlbertEquiv Q hQ hQt
  map_jordan := realConjugateAlbert_jordan Q hQ
  map_trace := realConjugateAlbert_trace Q hQ

/-- Real rotation in the lower 2×2 block, in the exact upper-slot convention. -/
def realRotation12 (c s : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  ![![1,0,0],![0,c,s],![0,-s,c]]

theorem realRotation12_columns (c s : ℝ) (h : c^2+s^2=1) :
    RealColumnsOrthogonal (realRotation12 c s) := by
  intro a b
  fin_cases a <;> fin_cases b <;>
    simp [realRotation12, Fin.sum_univ_three] <;> nlinarith

theorem realRotation12_transpose (c s : ℝ) :
    (realRotation12 c s).transpose = realRotation12 c (-s) := by
  apply Matrix.ext
  intro i j
  change realRotation12 c s j i = realRotation12 c (-s) i j
  fin_cases i <;> fin_cases j <;> simp [realRotation12]

def realRotation12Automorphism (c s : ℝ) (h : c^2+s^2=1) : CompactAutomorphism :=
  realOrthogonalAutomorphism (realRotation12 c s) (realRotation12_columns c s h)
    (by rw [realRotation12_transpose]; apply realRotation12_columns; nlinarith)

theorem realRotation12_d0 (c s : ℝ) (x : Albert) :
    (realConjugateAlbert (realRotation12 c s) x).d0 = x.d0 := by
  simp [realConjugateAlbert, fromMatrix, matrixConjugateReal, matrixRowMix,
    matrixColMix, realRotation12, toMatrix, Fin.sum_univ_three, octRe, octScalar]

theorem realRotation12_d1 (c s : ℝ) (x : Albert) :
    (realConjugateAlbert (realRotation12 c s) x).d1 =
      c^2*x.d1+s^2*x.d2+2*c*s*octRe x.o12 := by
  simp [realConjugateAlbert, fromMatrix, matrixConjugateReal, matrixRowMix,
    matrixColMix, realRotation12, toMatrix, Fin.sum_univ_three, octRe, octScalar,
    octConj, smul_eq_mul]
  ring

theorem realRotation12_d2 (c s : ℝ) (x : Albert) :
    (realConjugateAlbert (realRotation12 c s) x).d2 =
      s^2*x.d1+c^2*x.d2-2*c*s*octRe x.o12 := by
  simp [realConjugateAlbert, fromMatrix, matrixConjugateReal, matrixRowMix,
    matrixColMix, realRotation12, toMatrix, Fin.sum_univ_three, octRe, octScalar,
    octConj, smul_eq_mul]
  ring

def realSwap01 : Matrix (Fin 3) (Fin 3) ℝ := ![![0,1,0],![1,0,0],![0,0,1]]
def realSwap02 : Matrix (Fin 3) (Fin 3) ℝ := ![![0,0,1],![0,1,0],![1,0,0]]

theorem realSwap01_columns : RealColumnsOrthogonal realSwap01 := by
  intro a b
  fin_cases a <;> fin_cases b <;> norm_num [realSwap01, Fin.sum_univ_three]

theorem realSwap02_columns : RealColumnsOrthogonal realSwap02 := by
  intro a b
  fin_cases a <;> fin_cases b <;> norm_num [realSwap02, Fin.sum_univ_three]

theorem realSwap01_transpose : realSwap01.transpose = realSwap01 := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> rfl

theorem realSwap02_transpose : realSwap02.transpose = realSwap02 := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> rfl

def realSwap01Automorphism : CompactAutomorphism :=
  realOrthogonalAutomorphism realSwap01 realSwap01_columns
    (by rw [realSwap01_transpose]; exact realSwap01_columns)

def realSwap02Automorphism : CompactAutomorphism :=
  realOrthogonalAutomorphism realSwap02 realSwap02_columns
    (by rw [realSwap02_transpose]; exact realSwap02_columns)

theorem realSwap01_coordinates (x : Albert) :
    realConjugateAlbert realSwap01 x =
      ⟨x.d1,x.d0,x.d2,octConj x.o01,x.o12,x.o02⟩ := by
  apply Albert.ext
  all_goals simp [realConjugateAlbert, fromMatrix, matrixConjugateReal,
    matrixRowMix, matrixColMix, realSwap01, toMatrix, Fin.sum_univ_three,
    octRe, octScalar]

theorem realSwap02_coordinates (x : Albert) :
    realConjugateAlbert realSwap02 x =
      ⟨x.d2,x.d1,x.d0,octConj x.o12,octConj x.o02,octConj x.o01⟩ := by
  apply Albert.ext
  all_goals simp [realConjugateAlbert, fromMatrix, matrixConjugateReal,
    matrixRowMix, matrixColMix, realSwap02, toMatrix, Fin.sum_univ_three,
    octRe, octScalar]

end
end Glennie
