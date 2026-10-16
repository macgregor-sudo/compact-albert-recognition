/- The full real-linear compact sector model and its native matrix semantics.
The complex Hermitian coordinate type stores three real diagonal entries and
three complex upper entries; it is not the split Albert model. -/
module
public import Glennie.SectorSubspace
public import Mathlib.LinearAlgebra.Matrix.Adjugate

@[expose] public section
namespace Glennie
noncomputable section

set_option maxHeartbeats 2000000

abbrev ComplexHermitianCoordinates := ComplexCoordinates

def complexHermitianMatrix (q : ComplexHermitianCoordinates) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![(q.1.1:ℂ),q.2.1,q.2.2.1;
     star q.2.1,(q.1.2.1:ℂ),q.2.2.2;
     star q.2.2.1,star q.2.2.2,(q.1.2.2:ℂ)]

def matrixComplexCoordinates (H : Matrix (Fin 3) (Fin 3) ℂ) : ComplexHermitianCoordinates :=
  (((H 0 0).re,(H 1 1).re,(H 2 2).re),(H 0 1,H 0 2,H 1 2))

theorem complexHermitianMatrix_isHermitian (q : ComplexHermitianCoordinates) :
    (complexHermitianMatrix q).IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [complexHermitianMatrix, Matrix.conjTranspose_apply]

theorem matrixComplexCoordinates_inverse (q : ComplexHermitianCoordinates) :
    matrixComplexCoordinates (complexHermitianMatrix q)=q := by
  rcases q with ⟨⟨a,b,c⟩,⟨u,v,w⟩⟩
  simp [matrixComplexCoordinates,complexHermitianMatrix]

theorem complexHermitianMatrix_inverse (H : Matrix (Fin 3) (Fin 3) ℂ)
    (hH : H.IsHermitian) : complexHermitianMatrix (matrixComplexCoordinates H)=H := by
  have hs (i j : Fin 3) : star (H j i)=H i j := congrFun (congrFun hH i) j
  have hd (i : Fin 3) : ((H i i).re:ℂ)=H i i := by
    apply Complex.ext
    · simp
    · have h := congrArg Complex.im (hs i i)
      simp at h ⊢
      linarith
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [complexHermitianMatrix,matrixComplexCoordinates,hd,hs]

def sectorHiddenLinear : Albert →ₗ[ℝ] Matrix (Fin 3) (Fin 3) ℂ where
  toFun := hiddenMatrix
  map_add' x y := by
    ext i j
    fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
      simp [hiddenMatrix,hiddenColumn]
    all_goals ring
  map_smul' r x := by
    ext i j
    fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
      simp [hiddenMatrix,hiddenColumn,smul_eq_mul,Complex.mul_re,Complex.mul_im]

theorem hiddenMatrix_hiddenAlbert (M : Matrix (Fin 3) (Fin 3) ℂ) :
    hiddenMatrix (hiddenAlbert M)=M := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [hiddenMatrix,hiddenAlbert,hiddenColumn,hiddenOct]

theorem hiddenMatrix_complexAlbert (q : ComplexCoordinates) :
    hiddenMatrix (complexAlbertLinear q)=0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [hiddenMatrix,complexAlbertLinear,complexAlbert,hiddenColumn,complexOct]

theorem complexCoordinates_hiddenAlbert (M : Matrix (Fin 3) (Fin 3) ℂ) :
    complexCoordinatesLinear (hiddenAlbert M)=0 := by
  simp [complexCoordinatesLinear,hiddenAlbert,complexPart,hiddenOct,Complex.ext_iff]

/-- The actual full real-linear sector equivalence. -/
def compactSectorEquiv : Albert ≃ₗ[ℝ]
    ComplexHermitianCoordinates × Matrix (Fin 3) (Fin 3) ℂ where
  toFun x := (complexCoordinatesLinear x,sectorHiddenLinear x)
  invFun p := complexAlbertLinear p.1+hiddenAlbert p.2
  left_inv x := by
    change complexProjection x+hiddenAlbert (hiddenMatrix x)=x
    exact complex_hidden_decomposition x
  right_inv p := by
    apply Prod.ext
    · change complexCoordinatesLinear (complexAlbertLinear p.1+hiddenAlbert p.2)=p.1
      rw [map_add,complexCoordinates_albert,complexCoordinates_hiddenAlbert,add_zero]
    · change sectorHiddenLinear (complexAlbertLinear p.1+hiddenAlbert p.2)=p.2
      rw [map_add]
      change hiddenMatrix (complexAlbertLinear p.1)+hiddenMatrix (hiddenAlbert p.2)=p.2
      rw [hiddenMatrix_complexAlbert,hiddenMatrix_hiddenAlbert,zero_add]
  map_add' x y := by simp only [map_add,Prod.mk_add_mk]
  map_smul' r x := by simp only [map_smul,Prod.smul_mk,RingHom.id_apply]

def sectorComplexMatrix (x : Albert) : Matrix (Fin 3) (Fin 3) ℂ :=
  complexHermitianMatrix (complexCoordinatesLinear x)

theorem sectorComplexMatrix_isHermitian (x : Albert) :
    (sectorComplexMatrix x).IsHermitian :=
  complexHermitianMatrix_isHermitian (complexCoordinatesLinear x)

def sectorDecode (H : Matrix (Fin 3) (Fin 3) ℂ)
    (M : Matrix (Fin 3) (Fin 3) ℂ) : Albert :=
  complexAlbertLinear (matrixComplexCoordinates H)+hiddenAlbert M

def sectorAdjointAdjugate (M : Matrix (Fin 3) (Fin 3) ℂ) := M.adjugate.conjTranspose

def sectorPolarAdjugate (M N : Matrix (Fin 3) (Fin 3) ℂ) :=
  sectorAdjointAdjugate (M+N)-sectorAdjointAdjugate M-sectorAdjointAdjugate N

def sectorProductComplex (H M K N : Matrix (Fin 3) (Fin 3) ℂ) :=
  (1/2:ℂ) • (H*K+K*H-M.conjTranspose*N-N.conjTranspose*M)+
    ((M.conjTranspose*N).trace.re:ℂ) • (1 : Matrix (Fin 3) (Fin 3) ℂ)

def sectorProductHidden (H M K N : Matrix (Fin 3) (Fin 3) ℂ) :=
  (1/2:ℂ) • (M*(K.trace • (1 : Matrix (Fin 3) (Fin 3) ℂ)-K)+
    N*(H.trace • (1 : Matrix (Fin 3) (Fin 3) ℂ)-H)+sectorPolarAdjugate M N)


/-- The compact native square has the positive adjoint-adjugate hidden part.
No invertibility of the hidden matrix is used. -/
theorem hidden_square_hiddenMatrix (M : Matrix (Fin 3) (Fin 3) ℂ) :
    hiddenMatrix (jordan (hiddenAlbert M) (hiddenAlbert M)) =
      sectorAdjointAdjugate M := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext
  all_goals simp [hiddenMatrix, hiddenColumn, hiddenAlbert, hiddenOct,
    jordan_o01, jordan_o02, jordan_o12, octMul, octConj,
    Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
    Quaternion.imK_mul, smul_eq_mul, sectorAdjointAdjugate,
    Matrix.adjugate_fin_three, Matrix.conjTranspose_apply,
    Complex.mul_re, Complex.mul_im]
  all_goals ring

/-- The complex component of the complete bilinear product, in the 
column gauge. Both arguments range over all 27 real coordinates. -/
theorem sectorComplexMatrix_jordan (x y : Albert) :
    sectorComplexMatrix (jordan x y) =
      sectorProductComplex (sectorComplexMatrix x) (hiddenMatrix x)
        (sectorComplexMatrix y) (hiddenMatrix y) := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext
  all_goals simp [sectorComplexMatrix, complexHermitianMatrix,
    complexCoordinatesLinear, complexPart, hiddenMatrix, hiddenColumn,
    sectorProductComplex, jordan_d0, jordan_d1, jordan_d2,
    jordan_o01, jordan_o02, jordan_o12, octDot_coordinates,
    octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul,
    Quaternion.imJ_mul, Quaternion.imK_mul, smul_eq_mul,
    Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.trace,
    Matrix.diag, Matrix.one_apply, Fin.sum_univ_three,
    Complex.mul_re, Complex.mul_im]
  all_goals ring

/-- The hidden component includes the full polarized adjoint-adjugate term.
This polynomial identity also covers singular hidden matrices. -/
theorem hiddenMatrix_jordan (x y : Albert) :
    hiddenMatrix (jordan x y) =
      sectorProductHidden (sectorComplexMatrix x) (hiddenMatrix x)
        (sectorComplexMatrix y) (hiddenMatrix y) := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext
  all_goals simp [hiddenMatrix, hiddenColumn, sectorComplexMatrix,
    complexHermitianMatrix, complexCoordinatesLinear, complexPart,
    sectorProductHidden, sectorPolarAdjugate, sectorAdjointAdjugate,
    jordan_o01, jordan_o02, jordan_o12, octMul, octConj,
    Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
    Quaternion.imK_mul, smul_eq_mul, Matrix.adjugate_fin_three,
    Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.trace,
    Matrix.diag, Matrix.one_apply, Fin.sum_univ_three,
    Complex.mul_re, Complex.mul_im]
  all_goals ring

/-- Raw trace normalization T(1)=3 is preserved by the complex matrix component. -/
theorem trace_sectorComplexMatrix (x : Albert) :
    (sectorComplexMatrix x).trace = (trace x : ℂ) := by
  simp [sectorComplexMatrix, complexHermitianMatrix, complexCoordinatesLinear,
    Matrix.trace, Matrix.diag, Fin.sum_univ_three, trace]

/-- The full positive compact metric, with the required factor two on hidden
matrix coordinates. No normalized trace is substituted. -/
theorem inner_sector_model (x y : Albert) :
    inner x y = ((sectorComplexMatrix x * sectorComplexMatrix y).trace).re +
      2 * (((hiddenMatrix x).conjTranspose * hiddenMatrix y).trace).re := by
  simp [inner_coordinates, octDot_coordinates, sectorComplexMatrix,
    complexHermitianMatrix, complexCoordinatesLinear, complexPart,
    hiddenMatrix, hiddenColumn, Matrix.trace, Matrix.diag,
    Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_three,
    Complex.mul_re, Complex.mul_im]
  ring

@[simp] theorem sectorDecode_encode (x : Albert) :
    sectorDecode (sectorComplexMatrix x) (hiddenMatrix x) = x := by
  unfold sectorDecode sectorComplexMatrix
  rw [matrixComplexCoordinates_inverse]
  exact complex_hidden_decomposition x

/-- Decoding arbitrary complex matrices is an inverse only on the stated
Hermitian component; there is no silent extension to non-Hermitian inputs. -/
theorem sectorComplexMatrix_decode (H M : Matrix (Fin 3) (Fin 3) ℂ)
    (hH : H.IsHermitian) : sectorComplexMatrix (sectorDecode H M) = H := by
  simp only [sectorDecode, sectorComplexMatrix, map_add,
    complexCoordinates_albert, complexCoordinates_hiddenAlbert, add_zero]
  exact complexHermitianMatrix_inverse H hH

theorem hiddenMatrix_decode (H M : Matrix (Fin 3) (Fin 3) ℂ) :
    hiddenMatrix (sectorDecode H M) = M := by
  change sectorHiddenLinear (complexAlbertLinear (matrixComplexCoordinates H) +
    hiddenAlbert M) = M
  rw [map_add]
  change hiddenMatrix (complexAlbertLinear (matrixComplexCoordinates H)) +
    hiddenMatrix (hiddenAlbert M) = M
  rw [hiddenMatrix_complexAlbert, hiddenMatrix_hiddenAlbert, zero_add]

/-- The real-linear equivalence intertwines the complete compact Jordan product. -/
theorem compactSectorEquiv_product (x y : Albert) :
    compactSectorEquiv (jordan x y) =
      (matrixComplexCoordinates
        (sectorProductComplex (sectorComplexMatrix x) (hiddenMatrix x)
          (sectorComplexMatrix y) (hiddenMatrix y)),
       sectorProductHidden (sectorComplexMatrix x) (hiddenMatrix x)
          (sectorComplexMatrix y) (hiddenMatrix y)) := by
  apply Prod.ext
  · change complexCoordinatesLinear (jordan x y) = _
    have h := congrArg matrixComplexCoordinates (sectorComplexMatrix_jordan x y)
    simpa only [sectorComplexMatrix, matrixComplexCoordinates_inverse] using h
  · exact hiddenMatrix_jordan x y

theorem sectorDecode_product (x y : Albert) :
    sectorDecode
      (sectorProductComplex (sectorComplexMatrix x) (hiddenMatrix x)
        (sectorComplexMatrix y) (hiddenMatrix y))
      (sectorProductHidden (sectorComplexMatrix x) (hiddenMatrix x)
        (sectorComplexMatrix y) (hiddenMatrix y)) = jordan x y := by
  rw [← sectorComplexMatrix_jordan, ← hiddenMatrix_jordan, sectorDecode_encode]


/-- The actual real vector space of Hermitian complex matrices. -/
def Hermitian3C : Submodule ℝ (Matrix (Fin 3) (Fin 3) ℂ) where
  carrier := {H | H.IsHermitian}
  zero_mem' := Matrix.isHermitian_zero
  add_mem' hH hK := hH.add hK
  smul_mem' r H hH := hH.smul (IsSelfAdjoint.all r)

def sectorComplexLinear : Albert →ₗ[ℝ] Matrix (Fin 3) (Fin 3) ℂ where
  toFun := sectorComplexMatrix
  map_add' x y := by
    ext i j
    fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
      simp [sectorComplexMatrix, complexHermitianMatrix,
        complexCoordinatesLinear, complexPart]
    all_goals ring
  map_smul' r x := by
    ext i j
    fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
      simp [sectorComplexMatrix, complexHermitianMatrix,
        complexCoordinatesLinear, complexPart, smul_eq_mul,
        Complex.mul_re, Complex.mul_im]

/-- The full sector equivalence with the literal Hermitian-matrix carrier.
The earlier coordinate carrier supplies its explicit nine-real-dimensional
presentation; this version makes the Hermitian input constraint part of the type. -/
def compactHermitianSectorEquiv : Albert ≃ₗ[ℝ]
    Hermitian3C × Matrix (Fin 3) (Fin 3) ℂ where
  toFun x := (⟨sectorComplexMatrix x, sectorComplexMatrix_isHermitian x⟩,
    hiddenMatrix x)
  invFun p := sectorDecode p.1.1 p.2
  left_inv := sectorDecode_encode
  right_inv p := by
    apply Prod.ext
    · apply Subtype.ext
      exact sectorComplexMatrix_decode p.1.1 p.2 p.1.2
    · exact hiddenMatrix_decode p.1.1 p.2
  map_add' x y := by
    apply Prod.ext
    · apply Subtype.ext
      exact sectorComplexLinear.map_add x y
    · exact sectorHiddenLinear.map_add x y
  map_smul' r x := by
    apply Prod.ext
    · apply Subtype.ext
      exact sectorComplexLinear.map_smul r x
    · exact sectorHiddenLinear.map_smul r x


/-- The displayed product closes on every Hermitian complex component, with
arbitrary hidden matrices. Closure follows from the proved native product and
explicit inverse, not from an assumed sector-algebra structure. -/
theorem sectorProductComplex_isHermitian
    (H M K N : Matrix (Fin 3) (Fin 3) ℂ)
    (hH : H.IsHermitian) (hK : K.IsHermitian) :
    (sectorProductComplex H M K N).IsHermitian := by
  have h : sectorComplexMatrix (jordan (sectorDecode H M) (sectorDecode K N)) =
      sectorProductComplex H M K N := by
    rw [sectorComplexMatrix_jordan, sectorComplexMatrix_decode H M hH,
      sectorComplexMatrix_decode K N hK, hiddenMatrix_decode H M,
      hiddenMatrix_decode K N]
  rw [← h]
  exact sectorComplexMatrix_isHermitian _

/-- The actual compact sector product on its literal Hermitian carrier. -/
def compactHermitianSectorProduct
    (p q : Hermitian3C × Matrix (Fin 3) (Fin 3) ℂ) :
    Hermitian3C × Matrix (Fin 3) (Fin 3) ℂ :=
  (⟨sectorProductComplex p.1.1 p.2 q.1.1 q.2,
      sectorProductComplex_isHermitian _ _ _ _ p.1.2 q.1.2⟩,
   sectorProductHidden p.1.1 p.2 q.1.1 q.2)

/-- The literal-carrier equivalence preserves the actual native Jordan product. -/
theorem compactHermitianSectorEquiv_product (x y : Albert) :
    compactHermitianSectorEquiv (jordan x y) =
      compactHermitianSectorProduct
        (compactHermitianSectorEquiv x) (compactHermitianSectorEquiv y) := by
  apply Prod.ext
  · apply Subtype.ext
    exact sectorComplexMatrix_jordan x y
  · exact hiddenMatrix_jordan x y

end
end Glennie
