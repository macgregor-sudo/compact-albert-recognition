module

public import Glennie.Sector
public import Glennie.Theorems.CubicNorm
public import Glennie.Theorems.FrameMixedGram
public import Glennie.Obligations

/- Resolution by arbitrary diagonal frame atoms, without a canonical permutation. -/

public section
namespace Glennie
noncomputable section

theorem diagonalAlbert_representation (x : Albert) (hx : IsDiagonal x) :
    x = diagonalAlbert x.d0 x.d1 x.d2 := by
  apply Albert.ext <;> simp [diagonalAlbert,hx.1,hx.2.1,hx.2.2]

theorem jordan_diagonalAlbert (a b c d e f : ℝ) :
    jordan (diagonalAlbert a b c) (diagonalAlbert d e f) =
      diagonalAlbert (a*d) (b*e) (c*f) := by
  ext <;> simp [diagonalAlbert,jordan_d0,jordan_d1,jordan_d2,
    jordan_o01,jordan_o02,jordan_o12,octDot_coordinates,octMul,octConj,
    octNormSq,Quaternion.normSq_def']

/-- Encoder polynomial recovery carries diagonalization to all frame atoms. -/
theorem frame_projectors_diagonal (p : Fin 3 → Albert) (hp : Frame p)
    (he : IsDiagonal (encoder p)) (i : Fin 3) : IsDiagonal (p i) := by
  have hs : IsDiagonal (jordan (encoder p) (encoder p)) := by
    rw [diagonalAlbert_representation (encoder p) he,jordan_diagonalAlbert]
    simp [IsDiagonal,diagonalAlbert]
  have h0 : IsDiagonal (p 0) := by
    rw [← frame_projector_first p hp]
    simp [IsDiagonal,hs.1,hs.2.1,hs.2.2,he.1,he.2.1,he.2.2]
  have h1 : IsDiagonal (p 1) := by
    rw [← frame_projector_middle p hp]
    simp [IsDiagonal,hs.1,hs.2.1,hs.2.2,unit,octScalar]
  have h2 : IsDiagonal (p 2) := by
    rw [← frame_projector_last p hp]
    simp [IsDiagonal,hs.1,hs.2.1,hs.2.2,he.1,he.2.1,he.2.2]
  fin_cases i <;> assumption

theorem diagonal_idempotent_U (p h : Albert) (hp : jordan p p = p)
    (hpd : IsDiagonal p) (hhd : IsDiagonal h) : U p h = jordan p h := by
  have h0 := congrArg Albert.d0 hp
  have h1 := congrArg Albert.d1 hp
  have h2 := congrArg Albert.d2 hp
  rw [diagonalAlbert_representation p hpd,jordan_diagonalAlbert] at h0 h1 h2
  change p.d0*p.d0 = p.d0 at h0
  change p.d1*p.d1 = p.d1 at h1
  change p.d2*p.d2 = p.d2 at h2
  rw [diagonalAlbert_representation p hpd,diagonalAlbert_representation h hhd,
    U_diagonal,jordan_diagonalAlbert]
  ext <;> simp [diagonalAlbert,pow_two,h0,h1,h2]

/-- Every actual diagonal frame resolves the full real diagonal sector. -/
theorem diagonal_frame_resolution (p : Fin 3 → Albert) (hp : Frame p)
    (hpd : ∀ i, IsDiagonal (p i)) (h : Albert) (hhd : IsDiagonal h) :
    h = ∑ i, inner (p i) h • p i := by
  have hi (i : Fin 3) : jordan (p i) h = inner (p i) h • p i := by
    rw [← diagonal_idempotent_U (p i) h (hp.idempotent i) (hpd i) hhd]
    exact traceOne_idempotent_U _ _ (hp.idempotent i) (hp.trace_one i)
  calc
    h = jordan (1 : Albert) h := (jordan_unit_left h).symm
    _ = jordan (p 0) h+jordan (p 1) h+jordan (p 2) h := by
      rw [← hp.sum_unit,jordan_add_left,jordan_add_left]
    _ = _ := by simp only [hi,Fin.sum_univ_three]

private theorem diagonal_test_inner (a b c : ℝ) (x : Albert) :
    inner (diagonalAlbert a b c) x = a*x.d0+b*x.d1+c*x.d2 := by
  simp [inner_coordinates,diagonalAlbert,octDot_coordinates]

/-- Uniform overlaps with any diagonal frame fix all three actual coordinates. -/
theorem diagonal_frame_uniform_coordinates (p : Fin 3 → Albert) (hp : Frame p)
    (hpd : ∀ i, IsDiagonal (p i)) (x : Albert)
    (hu : ∀ i, inner (p i) x = 1/3) : x.d0 = 1/3 ∧ x.d1 = 1/3 ∧ x.d2 = 1/3 := by
  have ht (a b c : ℝ) :
      inner (diagonalAlbert a b c) x = trace (diagonalAlbert a b c)/3 := by
    have hdiag : IsDiagonal (diagonalAlbert a b c) := by simp [IsDiagonal,diagonalAlbert]
    have hr := diagonal_frame_resolution p hp hpd (diagonalAlbert a b c) hdiag
    have hm : inner (p 0) (diagonalAlbert a b c)+inner (p 1) (diagonalAlbert a b c)+
        inner (p 2) (diagonalAlbert a b c) = trace (diagonalAlbert a b c) := by
      rw [← inner_add_left,← inner_add_left,hp.sum_unit,inner,jordan_unit_left]
    calc
      _ = inner (∑ i, inner (p i) (diagonalAlbert a b c) • p i) x :=
        congrArg (fun y => inner y x) hr
      _ = trace (diagonalAlbert a b c)/3 := by
        simp only [Fin.sum_univ_three,inner_add_left,inner_smul_left,hu]
        linarith
  have h0 := ht 1 0 0
  have h1 := ht 0 1 0
  have h2 := ht 0 0 1
  rw [diagonal_test_inner] at h0 h1 h2
  norm_num [trace,diagonalAlbert] at h0 h1 h2
  refine ⟨?_,?_,?_⟩ <;> linarith

/-- Frame encoders diagonalize with zero determinant and fixed discriminant square. -/
theorem diagonal_frame_encoder_cubic_zero (p : Fin 3 → Albert) (hp : Frame p)
    (he : IsDiagonal (encoder p)) :
    (encoder p).d0*(encoder p).d1*(encoder p).d2 = 0 := by
  have h := frame_encoder_cubicNorm p hp
  rw [diagonalAlbert_representation (encoder p) he,newtonCubicNorm_coordinates] at h
  simpa [diagonalAlbert,octNormSq,Quaternion.normSq_def',octMul,octConj,octRe] using h

theorem diagonal_frame_encoder_discriminant (p : Fin 3 → Albert) (hp : Frame p)
    (he : IsDiagonal (encoder p)) :
    (((encoder p).d0-(encoder p).d1)*((encoder p).d0-(encoder p).d2)*
      ((encoder p).d1-(encoder p).d2))^2 = 4 := by
  have ht : (encoder p).d0+(encoder p).d1+(encoder p).d2 = 0 :=
    frame_encoder_trace p hp
  have hn := frame_encoder_norm p hp
  rw [inner_self_coordinates] at hn
  simp only [he.1,he.2.1,he.2.2] at hn
  norm_num [octNormSq,Quaternion.normSq_def'] at hn
  rw [ScalarEstimates.discriminant_identity _ _ _ ht,
    diagonal_frame_encoder_cubic_zero p hp he,hn]
  norm_num

end
end Glennie
