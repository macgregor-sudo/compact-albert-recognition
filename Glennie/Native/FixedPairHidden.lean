module

public import Glennie.Theorems.FrameSaturation
public import Glennie.Compact.FlatBase
public import Glennie.Compact.Affine20.Relabel

@[expose] public section
namespace Glennie.NativeFixedPairHidden
open Glennie Glennie.Compact.FlatBase Glennie.Compact.Affine20
noncomputable section
set_option autoImplicit false

private theorem gram_phase_of_projections (r : Fin 3 → Albert) (hr : Frame r)
    (he : complexProjection (encoder r) = 0)
    (hsq : complexProjection (jordan (encoder r) (encoder r)) =
      (2/3 : ℝ) • (1 : Albert)) :
    (hiddenMatrix (encoder r)).conjTranspose * hiddenMatrix (encoder r) =
        Matrix.diagonal (fun _ => (1/3 : ℂ)) ∧
      (hiddenMatrix (encoder r)).det.re = 0 ∧
      (hiddenMatrix (encoder r)).det.im ^ 2 = 1/27 := by
  let M := hiddenMatrix (encoder r)
  let G := sectorColumnGram M
  let S := sectorFrobeniusSq M
  have hrep : hiddenAlbert M=encoder r := by
    have h := complex_hidden_decomposition (encoder r)
    simpa only [he,zero_add] using h
  have hS : S=1 := by
    have h := hiddenAlbert_norm M
    rw [hrep,frame_encoder_norm r hr] at h
    change 2=2*S at h
    linarith
  rw [← hrep,hidden_square_complexProjection] at hsq
  have h0 := congrArg Albert.d0 hsq
  have h1 := congrArg Albert.d1 hsq
  have h2 := congrArg Albert.d2 hsq
  change S-(G 0 0).re=(2/3 : ℝ)*1 at h0
  change S-(G 1 1).re=(2/3 : ℝ)*1 at h1
  change S-(G 2 2).re=(2/3 : ℝ)*1 at h2
  have h0r : (G 0 0).re=1/3 := by linarith
  have h1r : (G 1 1).re=1/3 := by linarith
  have h2r : (G 2 2).re=1/3 := by linarith
  have hh : G.IsHermitian := Matrix.isHermitian_conjTranspose_mul_self M
  have him (i : Fin 3) : (G i i).im=0 := by
    have h := congrArg Complex.im (hh.apply i i)
    simp only [Complex.star_def,Complex.conj_im] at h
    linarith
  have h00 : G 0 0=(1/3 : ℂ) := by apply Complex.ext <;> norm_num [h0r,him]
  have h11 : G 1 1=(1/3 : ℂ) := by apply Complex.ext <;> norm_num [h1r,him]
  have h22 : G 2 2=(1/3 : ℂ) := by apply Complex.ext <;> norm_num [h2r,him]
  have hs01 := congrArg (fun x : Albert => complexPart x.o01) hsq
  have hs02 := congrArg (fun x : Albert => complexPart x.o02) hsq
  have hs12 := congrArg (fun x : Albert => complexPart x.o12) hsq
  have h01 : G 0 1=0 := by
    apply neg_eq_zero.mp
    simpa [complexAlbert,complexOct,complexPart,unit,octScalar,Complex.ext_iff] using hs01
  have h02 : G 0 2=0 := by
    apply neg_eq_zero.mp
    simpa [complexAlbert,complexOct,complexPart,unit,octScalar,Complex.ext_iff] using hs02
  have h12 : G 1 2=0 := by
    apply neg_eq_zero.mp
    simpa [complexAlbert,complexOct,complexPart,unit,octScalar,Complex.ext_iff] using hs12
  have h10 : G 1 0=0 := by rw [← hh.apply 1 0,h01,star_zero]
  have h20 : G 2 0=0 := by rw [← hh.apply 2 0,h02,star_zero]
  have h21 : G 2 1=0 := by rw [← hh.apply 2 1,h12,star_zero]
  have hG : G=Matrix.diagonal (fun _ => (1/3 : ℂ)) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.diagonal,h00,h11,h22,h01,h02,h12,h10,h20,h21]
  have hnorm : Complex.normSq M.det=1/27 := by
    rw [← MatrixDetEstimate.determinant_gram_real]
    change G.det.re=1/27
    rw [hG,Matrix.det_diagonal]
    norm_num [Fin.prod_univ_three]
  have hreal : M.det.re=0 := by
    have h := frame_encoder_cubicNorm r hr
    rw [← hrep,hiddenAlbert_cubicNorm] at h
    linarith
  refine ⟨hG, hreal, ?_⟩
  change M.det.im^2=1/27
  simpa [Complex.normSq_apply,hreal,pow_two] using hnorm

/-- A genuine third frame over the original fixed pair with the actual flat triple
ledger has purely hidden encoder, scaled-unitary Gram, and two determinant phases. -/
theorem native_fixed_pair_hidden_gram_phase (r : Fin 3 → Albert) (hr : Frame r)
    (hu : UniformLedger flatFrameP flatFrameQ r) :
    complexProjection (encoder r) = 0 ∧
      (hiddenMatrix (encoder r)).conjTranspose * hiddenMatrix (encoder r) =
        Matrix.diagonal (fun _ => (1/3 : ℂ)) ∧
      (hiddenMatrix (encoder r)).det.re = 0 ∧
      (hiddenMatrix (encoder r)).det.im ^ 2 = 1/27 := by
  have hp : InComplexSector (encoder flatFrameP) := by
    rw [flatFrameP_encoder]
    simp [InComplexSector, OctInComplex, flatXN, octScalar]
  have hq : InComplexSector (encoder flatFrameQ) := by
    rw [flatFrameQ_encoder]
    simp [InComplexSector, OctInComplex, flatY1, octScalar, octI, quatI]
  have hpc (i : Fin 3) : InComplexSector (flatFrameP i) :=
    (complexSector_mem_iff _).mp
      (frame_in_complexSector flatFrameP flatFrameP_frame hp i)
  have hqc (i : Fin 3) : InComplexSector (flatFrameQ i) :=
    (complexSector_mem_iff _).mp
      (frame_in_complexSector flatFrameQ flatFrameQ_frame hq i)
  have he := uniformLedger_complexProjection_encoder flatFrameP flatFrameQ r
    flatFrameP_frame flatFrameQ_frame hr hu hpc hqc
  have hs := uniformLedger_complexProjection_encoder_square flatFrameP flatFrameQ r
    flatFrameP_frame flatFrameQ_frame hr hu hpc hqc
  exact ⟨he, gram_phase_of_projections r hr he hs⟩

/-- The complete original 54-entry fibre premise discharges the flat triple ledger;
no selected numerical evidence, hidden Gram, inverse or rank premise is supplied. -/
theorem native_fixed_pair_full54_hidden_gram_phase (r : Fin 3 → Albert) (hr : Frame r)
    (hL : ledger54 ![flatFrameP, flatFrameQ, r] =
      ledger54 ![flatFrameP, flatFrameQ, flatFrameR]) :
    complexProjection (encoder r) = 0 ∧
      (hiddenMatrix (encoder r)).conjTranspose * hiddenMatrix (encoder r) =
        Matrix.diagonal (fun _ => (1/3 : ℂ)) ∧
      (hiddenMatrix (encoder r)).det.re = 0 ∧
      (hiddenMatrix (encoder r)).det.im ^ 2 = 1/27 := by
  apply native_fixed_pair_hidden_gram_phase r hr
  intro i j k
  have h := congrArg (fun L : Ledger54 => L.1 i j k) hL
  change ledger flatFrameP flatFrameQ r i j k =
    ledger flatFrameP flatFrameQ flatFrameR i j k at h
  exact h.trans (flat_uniform i j k)

end
end Glennie.NativeFixedPairHidden
