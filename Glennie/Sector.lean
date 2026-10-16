/- Fixed compact complex-sector coordinates in the declared gauge.
The hidden columns are (-extract(o12), +extract(o02), -extract(o01)). -/
module
public import Glennie.Native.AlgebraLaws
public import Mathlib.Basic.Complex.Basic

@[expose] public section
namespace Glennie
noncomputable section

set_option maxHeartbeats 2000000

def complexPart (x : Octonion) : ℂ := ⟨x.1.re,x.1.imI⟩

def complexOct (z : ℂ) : Octonion := (⟨z.re,z.im,0,0⟩,0)

/-- The last imaginary coordinate has the sign i(jℓ)=−kℓ. -/
def hiddenColumn (x : Octonion) : Fin 3 → ℂ :=
  ![⟨x.1.imJ,x.1.imK⟩,⟨x.2.re,x.2.imI⟩,⟨x.2.imJ,-x.2.imK⟩]

def hiddenOct (v : Fin 3 → ℂ) : Octonion :=
  (⟨0,0,(v 0).re,(v 0).im⟩,⟨(v 1).re,(v 1).im,(v 2).re,-(v 2).im⟩)

def hiddenMatrix (z : Albert) : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i => ![-hiddenColumn z.o12 i, hiddenColumn z.o02 i, -hiddenColumn z.o01 i]

def hiddenAlbert (M : Matrix (Fin 3) (Fin 3) ℂ) : Albert :=
  ⟨0,0,0,-hiddenOct (fun i => M i 2),hiddenOct (fun i => M i 1),
    -hiddenOct (fun i => M i 0)⟩

def complexProjection (z : Albert) : Albert :=
  ⟨z.d0,z.d1,z.d2,complexOct (complexPart z.o01),
    complexOct (complexPart z.o02),complexOct (complexPart z.o12)⟩

def diagonalAlbert (a b c : ℝ) : Albert := ⟨a,b,c,0,0,0⟩

def complexAlbert (a b c : ℝ) (u v w : ℂ) : Albert :=
  ⟨a,b,c,complexOct u,complexOct v,complexOct w⟩

theorem oct_complex_hidden_decomposition (x : Octonion) :
    complexOct (complexPart x) + hiddenOct (hiddenColumn x) = x := by
  apply Prod.ext <;> apply Quaternion.ext <;>
    simp [complexOct, complexPart, hiddenOct, hiddenColumn]

theorem complex_hidden_decomposition (z : Albert) :
    complexProjection z + hiddenAlbert (hiddenMatrix z) = z := by
  apply Albert.ext
  all_goals simp [complexProjection, hiddenAlbert, hiddenMatrix, hiddenColumn,
    hiddenOct, complexPart, complexOct]
  all_goals apply Prod.ext <;> apply Quaternion.ext <;> simp

theorem complex_hidden_orthogonal (x : Albert) (M : Matrix (Fin 3) (Fin 3) ℂ) :
    inner (complexProjection x) (hiddenAlbert M) = 0 := by
  simp [inner_coordinates, octDot_coordinates, complexProjection, hiddenAlbert,
    complexOct, hiddenOct]

theorem hiddenAlbert_norm (M : Matrix (Fin 3) (Fin 3) ℂ) :
    inner (hiddenAlbert M) (hiddenAlbert M) =
      2 * ∑ i, ∑ j, Complex.normSq (M i j) := by
  simp [inner_coordinates, octDot_coordinates, octNormSq, Quaternion.normSq_def',
    hiddenAlbert, hiddenOct, Complex.normSq_apply,
    Fin.sum_univ_three]
  ring

def sectorColumnGram (M : Matrix (Fin 3) (Fin 3) ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  M.conjTranspose * M

def sectorFrobeniusSq (M : Matrix (Fin 3) (Fin 3) ℂ) : ℝ :=
  ∑ i, ∑ j, Complex.normSq (M i j)

/-- The full complex projection of the square, in the actual hidden-column gauge. -/
theorem hidden_square_complexProjection (M : Matrix (Fin 3) (Fin 3) ℂ) :
    complexProjection (jordan (hiddenAlbert M) (hiddenAlbert M)) =
      complexAlbert
        (sectorFrobeniusSq M - (sectorColumnGram M 0 0).re)
        (sectorFrobeniusSq M - (sectorColumnGram M 1 1).re)
        (sectorFrobeniusSq M - (sectorColumnGram M 2 2).re)
        (-sectorColumnGram M 0 1) (-sectorColumnGram M 0 2)
        (-sectorColumnGram M 1 2) := by
  ext
  all_goals simp [complexProjection, complexAlbert, complexOct, complexPart,
    hiddenAlbert, hiddenOct, jordan_d0, jordan_d1, jordan_d2, jordan_o01,
    jordan_o02, jordan_o12, octDot_coordinates, octNormSq, Quaternion.normSq_def',
    octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
    Quaternion.imK_mul, smul_eq_mul, sectorColumnGram, sectorFrobeniusSq,
    Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_three,
    Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  all_goals ring

theorem U_diagonal (a b c : ℝ) (z : Albert) :
    U (diagonalAlbert a b c) z =
      ⟨a^2*z.d0,b^2*z.d1,c^2*z.d2,(a*b) • z.o01,
        (a*c) • z.o02,(b*c) • z.o12⟩ := by
  ext
  all_goals simp [U, diagonalAlbert, jordan_d0, jordan_d1, jordan_d2,
    jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul,
    octConj, octNormSq, Quaternion.normSq_def', smul_smul, smul_eq_mul]
  all_goals ring

end
end Glennie
