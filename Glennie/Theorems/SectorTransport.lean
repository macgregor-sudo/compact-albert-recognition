/- Actual determinant-one unitary transport of the compact native sector.
The action is (H,M) ↦ (g H g†, M g†). Every adjugate identity below
is polynomial; singular hidden matrices are included. -/
module
public import Glennie.SectorModel
public import Glennie.Automorphism
public import Glennie.SectorFactor
public import Mathlib.Algebra.Star.UnitaryStarAlgAut
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Analysis.Matrix.Spectrum

@[expose] public section
namespace Glennie
noncomputable section

abbrev SectorMatrix := Matrix (Fin 3) (Fin 3) ℂ
abbrev SectorUnitary := Matrix.unitaryGroup (Fin 3) ℂ

set_option maxHeartbeats 2000000

def sectorConjugation (g : SectorUnitary) (H : SectorMatrix) : SectorMatrix :=
  (g : SectorMatrix) * H * (g : SectorMatrix).conjTranspose

private theorem su_left (g : SectorUnitary) :
    (g : SectorMatrix).conjTranspose * (g : SectorMatrix) = 1 := g.property.1
private theorem su_right (g : SectorUnitary) :
    (g : SectorMatrix) * (g : SectorMatrix).conjTranspose = 1 := g.property.2
private theorem su_cancel (g : SectorUnitary) (H : SectorMatrix) :
    (g : SectorMatrix).conjTranspose * ((g : SectorMatrix) * H) = H := by
  rw [← Matrix.mul_assoc, su_left, Matrix.one_mul]

@[simp] theorem sectorConjugation_add (g : SectorUnitary) (H K : SectorMatrix) :
    sectorConjugation g (H+K)=sectorConjugation g H+sectorConjugation g K := by
  simp [sectorConjugation, Matrix.mul_add, Matrix.add_mul]
@[simp] theorem sectorConjugation_sub (g : SectorUnitary) (H K : SectorMatrix) :
    sectorConjugation g (H-K)=sectorConjugation g H-sectorConjugation g K := by
  simp [sectorConjugation, Matrix.mul_sub, Matrix.sub_mul]
@[simp] theorem sectorConjugation_smul (g : SectorUnitary) (a : ℂ) (H : SectorMatrix) :
    sectorConjugation g (a • H)=a • sectorConjugation g H := by
  simp [sectorConjugation, Matrix.mul_smul, Matrix.smul_mul]
@[simp] theorem sectorConjugation_real_smul (g : SectorUnitary) (a : ℝ) (H : SectorMatrix) :
    sectorConjugation g (a • H)=a • sectorConjugation g H := by
  simp [sectorConjugation, Matrix.mul_smul, Matrix.smul_mul]
@[simp] theorem sectorConjugation_one (g : SectorUnitary) : sectorConjugation g 1=1 := by
  simp only [sectorConjugation, Matrix.mul_one, su_right]
@[simp] theorem sectorConjugation_mul (g : SectorUnitary) (H K : SectorMatrix) :
    sectorConjugation g (H*K)=sectorConjugation g H*sectorConjugation g K := by
  simp only [sectorConjugation, Matrix.mul_assoc, su_cancel]
@[simp] theorem sectorConjugation_trace (g : SectorUnitary) (H : SectorMatrix) :
    (sectorConjugation g H).trace=H.trace := by
  rw [sectorConjugation, Matrix.trace_mul_cycle, su_left, Matrix.one_mul]

theorem sectorConjugation_hermitian (g : SectorUnitary) (H : SectorMatrix)
    (hH : H.IsHermitian) : (sectorConjugation g H).IsHermitian := by
  change (sectorConjugation g H).conjTranspose=sectorConjugation g H
  simp only [sectorConjugation, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, hH.eq, Matrix.mul_assoc]

theorem sectorAdjointAdjugate_mul (M N : SectorMatrix) :
    sectorAdjointAdjugate (M*N)=sectorAdjointAdjugate M*sectorAdjointAdjugate N := by
  simp only [sectorAdjointAdjugate, Matrix.adjugate_mul_distrib, Matrix.conjTranspose_mul]

theorem sectorAdjointAdjugate_unitary (g : SectorUnitary)
    (hd : (g : SectorMatrix).det=1) :
    sectorAdjointAdjugate (g : SectorMatrix).conjTranspose=(g : SectorMatrix).conjTranspose := by
  have hdt : (g : SectorMatrix).conjTranspose.det=1 := by
    rw [Matrix.det_conjTranspose,hd]
    simp
  have h := congrArg (fun A : SectorMatrix => (g : SectorMatrix)*A)
    (Matrix.mul_adjugate (g : SectorMatrix).conjTranspose)
  have ha : (g : SectorMatrix).conjTranspose.adjugate=(g : SectorMatrix) := by
    simpa only [← Matrix.mul_assoc,su_right,Matrix.one_mul,hdt,one_smul,Matrix.mul_one] using h
  simp only [sectorAdjointAdjugate,ha]

theorem sectorPolarAdjugate_right (g : SectorUnitary)
    (hd : (g : SectorMatrix).det=1) (M N : SectorMatrix) :
    sectorPolarAdjugate (M*(g : SectorMatrix).conjTranspose)
      (N*(g : SectorMatrix).conjTranspose)=
      sectorPolarAdjugate M N*(g : SectorMatrix).conjTranspose := by
  rw [sectorPolarAdjugate,← Matrix.add_mul]
  simp only [sectorAdjointAdjugate_mul,sectorAdjointAdjugate_unitary g hd,
    sectorPolarAdjugate,Matrix.sub_mul]

theorem sector_right_gram (g : SectorUnitary) (M N : SectorMatrix) :
    (M*(g : SectorMatrix).conjTranspose).conjTranspose*
      (N*(g : SectorMatrix).conjTranspose)=sectorConjugation g (M.conjTranspose*N) := by
  simp only [Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose,
    sectorConjugation,Matrix.mul_assoc]

theorem sector_right_mixed (g : SectorUnitary) (M K : SectorMatrix) :
    (M*(g : SectorMatrix).conjTranspose)*
      ((sectorConjugation g K).trace • (1 : SectorMatrix)-sectorConjugation g K)=
      (M*(K.trace • (1 : SectorMatrix)-K))*(g : SectorMatrix).conjTranspose := by
  rw [sectorConjugation_trace]
  simp only [sectorConjugation_trace,sectorConjugation,Matrix.mul_sub,
    Matrix.sub_mul,Matrix.mul_smul,Matrix.smul_mul,Matrix.mul_one,
    Matrix.mul_assoc,su_cancel]

theorem sectorProductComplex_conjugation (g : SectorUnitary) (H M K N : SectorMatrix) :
    sectorProductComplex (sectorConjugation g H) (M*(g : SectorMatrix).conjTranspose)
      (sectorConjugation g K) (N*(g : SectorMatrix).conjTranspose)=
      sectorConjugation g (sectorProductComplex H M K N) := by
  simp only [sectorProductComplex,sector_right_gram,sectorConjugation_trace]
  simp only [sectorConjugation_add,sectorConjugation_sub,sectorConjugation_smul,
    sectorConjugation_mul,sectorConjugation_one]

theorem sectorProductHidden_conjugation (g : SectorUnitary)
    (hd : (g : SectorMatrix).det=1) (H M K N : SectorMatrix) :
    sectorProductHidden (sectorConjugation g H) (M*(g : SectorMatrix).conjTranspose)
      (sectorConjugation g K) (N*(g : SectorMatrix).conjTranspose)=
      sectorProductHidden H M K N*(g : SectorMatrix).conjTranspose := by
  simp only [sectorProductHidden,sector_right_mixed,sectorPolarAdjugate_right g hd,
    Matrix.add_mul,Matrix.smul_mul]

private theorem hiddenAlbert_add (M N : SectorMatrix) :
    hiddenAlbert (M+N)=hiddenAlbert M+hiddenAlbert N := by
  ext <;> simp [hiddenAlbert,hiddenOct]
  all_goals ring
private theorem hiddenAlbert_smul (a : ℝ) (M : SectorMatrix) :
    hiddenAlbert (a • M)=a • hiddenAlbert M := by
  ext <;> simp [hiddenAlbert,hiddenOct,smul_eq_mul,Complex.mul_re,Complex.mul_im]
  all_goals ring
private theorem matrixComplexCoordinates_add (H K : SectorMatrix) :
    matrixComplexCoordinates (H+K)=matrixComplexCoordinates H+matrixComplexCoordinates K := by
  simp [matrixComplexCoordinates]
private theorem matrixComplexCoordinates_smul (a : ℝ) (H : SectorMatrix) :
    matrixComplexCoordinates (a • H)=a • matrixComplexCoordinates H := by
  simp [matrixComplexCoordinates,smul_eq_mul,Complex.mul_re,Complex.mul_im]
private theorem sectorDecode_add (H M K N : SectorMatrix) :
    sectorDecode (H+K) (M+N)=sectorDecode H M+sectorDecode K N := by
  simp only [sectorDecode,matrixComplexCoordinates_add,map_add,hiddenAlbert_add]
  abel
private theorem sectorDecode_smul (a : ℝ) (H M : SectorMatrix) :
    sectorDecode (a • H) (a • M)=a • sectorDecode H M := by
  simp only [sectorDecode,matrixComplexCoordinates_smul,map_smul,hiddenAlbert_smul,smul_add]
private theorem sectorComplexMatrix_add (x y : Albert) :
    sectorComplexMatrix (x+y)=sectorComplexMatrix x+sectorComplexMatrix y := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sectorComplexMatrix,complexHermitianMatrix,map_add]
private theorem sectorComplexMatrix_smul (a : ℝ) (x : Albert) :
    sectorComplexMatrix (a • x)=a • sectorComplexMatrix x := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sectorComplexMatrix,complexHermitianMatrix,map_smul,smul_eq_mul]

def sectorUnitaryAction (g : SectorUnitary) (x : Albert) : Albert :=
  sectorDecode (sectorConjugation g (sectorComplexMatrix x))
    (hiddenMatrix x*(g : SectorMatrix).conjTranspose)

@[simp] theorem sectorUnitaryAction_complex (g : SectorUnitary) (x : Albert) :
    sectorComplexMatrix (sectorUnitaryAction g x)=sectorConjugation g (sectorComplexMatrix x) :=
  sectorComplexMatrix_decode _ _ (sectorConjugation_hermitian g _ (sectorComplexMatrix_isHermitian x))
@[simp] theorem sectorUnitaryAction_hidden (g : SectorUnitary) (x : Albert) :
    hiddenMatrix (sectorUnitaryAction g x)=hiddenMatrix x*(g : SectorMatrix).conjTranspose :=
  hiddenMatrix_decode _ _

def sectorUnitaryLinear (g : SectorUnitary) : Albert →ₗ[ℝ] Albert where
  toFun := sectorUnitaryAction g
  map_add' x y := by
    have hM : hiddenMatrix (x+y)=hiddenMatrix x+hiddenMatrix y := sectorHiddenLinear.map_add x y
    simp only [sectorUnitaryAction,sectorComplexMatrix_add,sectorConjugation_add,
      hM,Matrix.add_mul,sectorDecode_add]
  map_smul' a x := by
    have hM : hiddenMatrix (a • x)=a • hiddenMatrix x := sectorHiddenLinear.map_smul a x
    simp only [sectorUnitaryAction,sectorComplexMatrix_smul,sectorConjugation_real_smul,
      hM,Matrix.smul_mul,sectorDecode_smul,RingHom.id_apply]

private theorem sector_native_ext (x y : Albert)
    (hH : sectorComplexMatrix x=sectorComplexMatrix y) (hM : hiddenMatrix x=hiddenMatrix y) : x=y := by
  calc
    x = sectorDecode (sectorComplexMatrix x) (hiddenMatrix x) := (sectorDecode_encode x).symm
    _ = sectorDecode (sectorComplexMatrix y) (hiddenMatrix y) := by rw [hH,hM]
    _ = y := sectorDecode_encode y

@[simp] theorem sectorUnitaryAction_inverse (g : SectorUnitary) (x : Albert) :
    sectorUnitaryAction (star g) (sectorUnitaryAction g x)=x := by
  have hs : ((star g : SectorUnitary) : SectorMatrix)=(g : SectorMatrix).conjTranspose := rfl
  apply sector_native_ext
  · simp only [sectorUnitaryAction_complex,sectorConjugation]
    simp only [hs,Matrix.conjTranspose_conjTranspose]
    simp only [Matrix.mul_assoc,su_cancel,su_left,Matrix.mul_one]
  · simp only [sectorUnitaryAction_hidden]
    simp only [hs,Matrix.conjTranspose_conjTranspose]
    rw [Matrix.mul_assoc,su_left,Matrix.mul_one]

def sectorUnitaryEquiv (g : SectorUnitary) : Albert ≃ₗ[ℝ] Albert where
  toLinearMap := sectorUnitaryLinear g
  invFun := sectorUnitaryAction (star g)
  left_inv := sectorUnitaryAction_inverse g
  right_inv x := by
    have h := sectorUnitaryAction_inverse (star g) x
    rw [star_star] at h
    exact h

theorem sectorUnitaryAction_jordan (g : SectorUnitary)
    (hd : (g : SectorMatrix).det=1) (x y : Albert) :
    sectorUnitaryAction g (jordan x y)=jordan (sectorUnitaryAction g x) (sectorUnitaryAction g y) := by
  apply sector_native_ext
  · simp only [sectorUnitaryAction_complex,sectorComplexMatrix_jordan,
      sectorUnitaryAction_hidden,sectorProductComplex_conjugation]
  · simp only [sectorUnitaryAction_hidden,hiddenMatrix_jordan,
      sectorUnitaryAction_complex,sectorProductHidden_conjugation g hd]

theorem sectorUnitaryAction_trace (g : SectorUnitary) (x : Albert) :
    trace (sectorUnitaryAction g x)=trace x := by
  have h := sectorConjugation_trace g (sectorComplexMatrix x)
  rw [← sectorUnitaryAction_complex,trace_sectorComplexMatrix,trace_sectorComplexMatrix] at h
  exact_mod_cast h

/-- A constructed native automorphism; the only input restrictions are actual
unitarity and determinant one of the concrete complex matrix. -/
def sectorSU3Automorphism (g : SectorUnitary)
    (hd : (g : SectorMatrix).det=1) : CompactAutomorphism where
  equiv := sectorUnitaryEquiv g
  map_jordan := sectorUnitaryAction_jordan g hd
  map_trace := sectorUnitaryAction_trace g

theorem sectorUnitaryAction_det_hidden (g : SectorUnitary)
    (hd : (g : SectorMatrix).det=1) (x : Albert) :
    (hiddenMatrix (sectorUnitaryAction g x)).det=(hiddenMatrix x).det := by
  rw [sectorUnitaryAction_hidden,Matrix.det_mul,Matrix.det_conjTranspose,hd]
  simp

theorem sectorSU3_phi (g : SectorUnitary) (hd : (g : SectorMatrix).det=1) (x y z : Albert) :
    phi (sectorUnitaryAction g x) (sectorUnitaryAction g y) (sectorUnitaryAction g z)=phi x y z :=
  (sectorSU3Automorphism g hd).phi_map x y z

/-- Put the determinant phase in one diagonal entry; no cube root is chosen. -/
def sectorPhaseMatrix (u : SectorUnitary) : SectorMatrix :=
  Matrix.diagonal ![star (u : SectorMatrix).det,1,1]

def sectorPhaseUnitary (u : SectorUnitary) : SectorUnitary :=
  ⟨sectorPhaseMatrix u, by
    have hl := (Matrix.det_of_mem_unitary u.property).1
    have hr := (Matrix.det_of_mem_unitary u.property).2
    have hl' : (starRingEnd ℂ) (u : SectorMatrix).det*(u : SectorMatrix).det=1 := hl
    have hr' : (u : SectorMatrix).det*(starRingEnd ℂ) (u : SectorMatrix).det=1 := hr
    constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [sectorPhaseMatrix,Matrix.star_eq_conjTranspose,Matrix.mul_apply,
        Matrix.conjTranspose_apply,Matrix.diagonal_apply,Matrix.one_apply,
        Fin.sum_univ_three,hl,hr,hl',hr']⟩

theorem sectorPhaseUnitary_det (u : SectorUnitary) :
    (sectorPhaseUnitary u : SectorMatrix).det=star (u : SectorMatrix).det := by
  simp [sectorPhaseUnitary,sectorPhaseMatrix,Matrix.det_diagonal,Fin.prod_univ_three]

theorem sectorPhaseUnitary_diagonal (u : SectorUnitary) (a : Fin 3 → ℝ) :
    sectorConjugation (sectorPhaseUnitary u) (Matrix.diagonal (fun i => (a i : ℂ)))=
      Matrix.diagonal (fun i => (a i : ℂ)) := by
  have hl := (Matrix.det_of_mem_unitary u.property).1
  have hr := (Matrix.det_of_mem_unitary u.property).2
  have hl' : (starRingEnd ℂ) (u : SectorMatrix).det*(u : SectorMatrix).det=1 := hl
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sectorConjugation,sectorPhaseUnitary,sectorPhaseMatrix,
      Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.diagonal_apply,
      Fin.sum_univ_three]
  all_goals calc
    _ = ((starRingEnd ℂ) (u : SectorMatrix).det*(u : SectorMatrix).det)*(a 0 : ℂ) := by ring
    _ = (a 0 : ℂ) := by rw [hl']; simp

theorem sectorConjugation_comp (g h : SectorUnitary) (H : SectorMatrix) :
    sectorConjugation (g*h) H=sectorConjugation g (sectorConjugation h H) := by
  simp only [sectorConjugation,Submonoid.coe_mul,Matrix.conjTranspose_mul,Matrix.mul_assoc]

/-- Actual special-unitary diagonalization of every Hermitian matrix, including
zero and repeated spectra. The determinant phase correction fixes the diagonal. -/
theorem exists_sectorSU3_diagonal (H : SectorMatrix) (hH : H.IsHermitian) :
    ∃ g : SectorUnitary, (g : SectorMatrix).det=1 ∧
      sectorConjugation g H=Matrix.diagonal (fun i => (hH.eigenvalues i : ℂ)) := by
  let u : SectorUnitary := star hH.eigenvectorUnitary
  let d : SectorUnitary := sectorPhaseUnitary u
  have hu : sectorConjugation u H=Matrix.diagonal (fun i => (hH.eigenvalues i : ℂ)) := by
    have hs := hH.conjStarAlgAut_star_eigenvectorUnitary
    change sectorConjugation (star hH.eigenvectorUnitary) H =
      Matrix.diagonal (fun i => (hH.eigenvalues i : ℂ)) at hs
    exact hs
  refine ⟨d*u,?_,?_⟩
  · change ((d : SectorMatrix)*(u : SectorMatrix)).det=1
    rw [Matrix.det_mul]
    change (sectorPhaseUnitary u : SectorMatrix).det*(u : SectorMatrix).det=1
    rw [sectorPhaseUnitary_det]
    exact (Matrix.det_of_mem_unitary u.property).1
  · rw [sectorConjugation_comp,hu]
    exact sectorPhaseUnitary_diagonal u hH.eigenvalues

/-- Literal compact-sector inputs have no hidden coordinate, in the actual
sector equivalence rather than an assumed model conversion. -/
theorem hiddenMatrix_of_inComplex (x : Albert) (hx : InComplexSector x) : hiddenMatrix x=0 := by
  have h : complexAlbertLinear (complexCoordinatesLinear x)=x := complexProjection_eq_self x hx
  rw [← h]
  exact hiddenMatrix_complexAlbert _

theorem sectorUnitaryAction_inComplex (g : SectorUnitary) (x : Albert)
    (hx : InComplexSector x) : InComplexSector (sectorUnitaryAction g x) := by
  apply (complexSector_mem_iff _).mp
  refine ⟨matrixComplexCoordinates (sectorConjugation g (sectorComplexMatrix x)),?_⟩
  have hz : hiddenAlbert (0 : SectorMatrix)=0 := by
    ext <;> simp [hiddenAlbert,hiddenOct]
  simp [sectorUnitaryAction,hiddenMatrix_of_inComplex x hx,sectorDecode,hz]

/-- The same constructed native automorphism diagonalizes a fixed-sector first
input and keeps every other fixed-sector input inside that sector. -/
theorem exists_sectorSU3_native_diagonal (x : Albert) (hx : InComplexSector x) :
    ∃ g : SectorUnitary, (g : SectorMatrix).det=1 ∧ IsDiagonal (sectorUnitaryAction g x) := by
  obtain ⟨g,hd,hg⟩ := exists_sectorSU3_diagonal (sectorComplexMatrix x)
    (sectorComplexMatrix_isHermitian x)
  refine ⟨g,hd,?_⟩
  simp [sectorUnitaryAction,hg,hiddenMatrix_of_inComplex x hx,sectorDecode,
    matrixComplexCoordinates,complexAlbertLinear,complexAlbert,complexOct,
    hiddenAlbert,hiddenOct,IsDiagonal,Matrix.diagonal_apply]
  all_goals first | rfl | (ext <;> simp)

/-- Conjugation by a determinant-one unitary preserves every determinant,
without any hypothesis on the matrix being conjugated. -/
theorem sectorConjugation_det (g : SectorUnitary)
    (hd : (g : SectorMatrix).det=1) (H : SectorMatrix) :
    (sectorConjugation g H).det=H.det := by
  simp only [sectorConjugation,Matrix.det_mul,Matrix.det_conjTranspose,hd,star_one,one_mul,mul_one]

/-- Literal finite-coordinate binding of the diagonal factor coefficient to the
imaginary part of the ordinary complex commutator determinant. -/
theorem sector_commutator_diagonal_im (x y : Albert) (hx : IsDiagonal x) :
    (sectorComplexMatrix x*sectorComplexMatrix y-
      sectorComplexMatrix y*sectorComplexMatrix x).det.im=
      2*(x.d0-x.d1)*(x.d1-x.d2)*(x.d2-x.d0)*
        (complexPart y.o01*complexPart y.o12*star (complexPart y.o02)).im := by
  rcases hx with ⟨h01,h02,h12⟩
  simp [sectorComplexMatrix,complexHermitianMatrix,complexCoordinatesLinear,
    h01,h02,h12,complexPart,Matrix.det_fin_three,Matrix.mul_apply,
    Fin.sum_univ_three,Complex.mul_re,Complex.mul_im]
  ring

private theorem sector_diagonalAlbert_eq (x : Albert) (hx : IsDiagonal x) :
    diagonalAlbert x.d0 x.d1 x.d2=x := by
  apply Albert.ext <;> simp [diagonalAlbert,hx.1,hx.2.1,hx.2.2]
private theorem sector_complexAlbert_eq (x : Albert) (hx : InComplexSector x) :
    complexAlbert x.d0 x.d1 x.d2 (complexPart x.o01)
      (complexPart x.o02) (complexPart x.o12)=x := complexProjection_eq_self x hx

/-- Full fixed-complex-sector factor. The third native input is unrestricted;
its complex component, singular hidden matrices, and zero factors are included. -/
theorem phi_complex_sector_factor (x y z : Albert)
    (hx : InComplexSector x) (hy : InComplexSector y) :
    phi x y z=
      (sectorComplexMatrix x*sectorComplexMatrix y-
        sectorComplexMatrix y*sectorComplexMatrix x).det.im*(hiddenMatrix z).det.im := by
  obtain ⟨g,hd,hgx⟩ := exists_sectorSU3_native_diagonal x hx
  have hgy := sectorUnitaryAction_inComplex g y hy
  have hf := phi_diagonal_complex_factor
    (sectorUnitaryAction g x).d0 (sectorUnitaryAction g x).d1 (sectorUnitaryAction g x).d2
    (sectorUnitaryAction g y).d0 (sectorUnitaryAction g y).d1 (sectorUnitaryAction g y).d2
    (complexPart (sectorUnitaryAction g y).o01)
    (complexPart (sectorUnitaryAction g y).o02)
    (complexPart (sectorUnitaryAction g y).o12) (sectorUnitaryAction g z)
  rw [sector_diagonalAlbert_eq _ hgx,sector_complexAlbert_eq _ hgy] at hf
  have hc := sector_commutator_diagonal_im (sectorUnitaryAction g x) (sectorUnitaryAction g y) hgx
  have hdet :
      (sectorComplexMatrix (sectorUnitaryAction g x)*sectorComplexMatrix (sectorUnitaryAction g y)-
        sectorComplexMatrix (sectorUnitaryAction g y)*sectorComplexMatrix (sectorUnitaryAction g x)).det=
      (sectorComplexMatrix x*sectorComplexMatrix y-sectorComplexMatrix y*sectorComplexMatrix x).det := by
    rw [sectorUnitaryAction_complex,sectorUnitaryAction_complex,
      ← sectorConjugation_mul,← sectorConjugation_mul,← sectorConjugation_sub,
      sectorConjugation_det g hd]
  rw [sectorSU3_phi g hd,← hc,hdet,sectorUnitaryAction_det_hidden g hd] at hf
  exact hf

end
end Glennie
