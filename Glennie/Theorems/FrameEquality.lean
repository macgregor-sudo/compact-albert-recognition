module

public import Glennie.SectorEstimates
public import Glennie.Theorems.FrameSaturation

/- Both directions of the literal 27-entry equality criterion for native frames. -/

@[expose] public section
namespace Glennie
noncomputable section
set_option maxHeartbeats 2000000

theorem frame_bound : FrameBound := by
  intro p q r hp hq hr
  have h := phi_product_bound (encoder p) (encoder q) (encoder r) (frame_encoder_trace p hp)
  rw [frame_encoder_norm p hp,frame_encoder_norm q hq,frame_encoder_norm r hr] at h
  have ha : |phi (encoder p) (encoder q) (encoder r)|^2 =
      phi (encoder p) (encoder q) (encoder r)^2 := sq_abs _
  nlinarith [abs_nonneg (phi (encoder p) (encoder q) (encoder r))]

theorem diagonal_frame_equality (p q r : Fin 3 → Albert)
    (hp : Frame p) (hq : Frame q) (hr : Frame r)
    (hpd : IsDiagonal (encoder p)) (hqc : InComplexSector (encoder q)) :
    |phi (encoder p) (encoder q) (encoder r)|=4/27 ↔ UniformLedger p q r := by
  let x := encoder p
  let y := encoder q
  let z := encoder r
  let u := complexPart y.o01
  let v := complexPart y.o02
  let w := complexPart y.o12
  let V := (x.d0-x.d1)*(x.d1-x.d2)*(x.d2-x.d0)
  let t := (u*w*star v).im
  let D := (hiddenMatrix z).det.im
  have hpf : ∀ i, IsDiagonal (p i) := frame_projectors_diagonal p hp hpd
  have hpc : ∀ i, InComplexSector (p i) := fun i => diagonal_inComplex _ (hpf i)
  have hqf : ∀ j, InComplexSector (q j) := fun j =>
    (complexSector_mem_iff _).mp (frame_in_complexSector q hq hqc j)
  have hy : complexAlbert y.d0 y.d1 y.d2 u v w=y := complexAlbert_eq y hqc
  have hV : V^2=4 := by
    have h := diagonal_frame_encoder_discriminant p hp hpd
    change ((x.d0-x.d1)*(x.d0-x.d2)*(x.d1-x.d2))^2=4 at h
    calc
      _ = ((x.d0-x.d1)*(x.d0-x.d2)*(x.d1-x.d2))^2 := by dsimp [V]; ring
      _ = 4 := h
  have hphi : phi x y z=2*V*t*D := by
    rw [phi_of_diagonal_complex x y z hpd hqc]
    dsimp [V,t,D,u,v,w]
    ring
  constructor
  · intro heq
    have hsq : phi x y z^2=16/729 := by
      have h := congrArg (fun a : ℝ => a^2) heq
      rw [sq_abs] at h
      norm_num at h
      exact h
    have ht : t^2 ≤ 1/27 := by
      have h := complex_coefficient_bound y.d0 y.d1 y.d2 u v w
      rw [hy,frame_encoder_norm q hq] at h
      change 216*t^2 ≤ (2 : ℝ)^3 at h
      nlinarith
    have hd : D^2 ≤ 1/27 := by
      have h := hidden_determinant_bound z
      rw [frame_encoder_norm r hr] at h
      change 216*D^2 ≤ (2 : ℝ)^3 at h
      nlinarith
    have hprod : t^2*D^2=1/729 := by
      rw [hphi] at hsq
      have ha : (2*V*t*D)^2=4*V^2*t^2*D^2 := by ring
      rw [ha,hV] at hsq
      nlinarith
    have htEq : t^2=1/27 := by
      have h := mul_le_mul_of_nonneg_left hd (sq_nonneg t)
      nlinarith
    have hdEq : D^2=1/27 := by
      have h := mul_le_mul_of_nonneg_right ht (sq_nonneg D)
      nlinarith
    have hn : inner (complexAlbert y.d0 y.d1 y.d2 u v w)
        (complexAlbert y.d0 y.d1 y.d2 u v w)=2 := by
      rw [hy]
      exact frame_encoder_norm q hq
    obtain ⟨hy0,hy1,hy2,huN,hvN,hwN⟩ := fe_complex_saturation _ _ _ _ _ _ hn htEq
    have hys0 : (jordan y y).d0=2/3 := by
      rw [← hy,fe_complex_square_d0,hy0,huN,hvN]
      norm_num
    have hys1 : (jordan y y).d1=2/3 := by
      rw [← hy,fe_complex_square_d1,hy1,huN,hwN]
      norm_num
    have hys2 : (jordan y y).d2=2/3 := by
      rw [← hy,fe_complex_square_d2,hy2,hvN,hwN]
      norm_num
    have hqd := fe_encoder_atoms_diagonal q hq hy0 hy1 hy2 hys0 hys1 hys2
    have hov : ∀ i j, inner (p i) (q j)=1/3 := fun i j =>
      fe_diagonal_overlap _ _ (hpf i) (hp.trace_one i) (hqd j)
    obtain ⟨hz,hzs⟩ := fe_hidden_saturation z (frame_encoder_norm r hr) hdEq
    exact complex_pair_uniformLedger_of_projections p q r hpc hqf hov
      (frame_projector_complexProjections r hr hz hzs)
  · intro hu
    have hz := uniformLedger_complexProjection_encoder p q r hp hq hr hu hpc hqf
    have hzs := uniformLedger_complexProjection_encoder_square p q r hp hq hr hu hpc hqf
    have ht : t^2=1/27 := fe_uniform_complex_triangle p q r hp hq hr hu hpf hqc
    have hd : D^2=1/27 := fe_hidden_determinant_of_projections r hr hz hzs
    have hsq : phi x y z^2=16/729 := by
      rw [hphi]
      calc
        _ = 4*V^2*t^2*D^2 := by ring
        _ = 16/729 := by rw [hV,ht,hd]; norm_num
    have ha : |phi x y z|^2=phi x y z^2 := sq_abs _
    change |phi x y z|=4/27
    nlinarith [abs_nonneg (phi x y z)]

/-- Complete native frame equality, including every uniform ledger and every sign. -/
theorem frame_equality : FrameEquality := by
  intro p q r hp hq hr
  obtain ⟨g,hpd,hqc⟩ := universal_pair_reduction (encoder p) (encoder q)
  let P := fun i => g.equiv (p i)
  let Q := fun i => g.equiv (q i)
  let R := fun i => g.equiv (r i)
  have hP : Frame P := g.map_frame p hp
  have hQ : Frame Q := g.map_frame q hq
  have hR : Frame R := g.map_frame r hr
  have hPd : IsDiagonal (encoder P) := by
    dsimp only [P]
    rw [g.encoder_map]
    exact hpd
  have hQc : InComplexSector (encoder Q) := by
    dsimp only [Q]
    rw [g.encoder_map]
    exact hqc
  have h := diagonal_frame_equality P Q R hP hQ hR hPd hQc
  have hphi : phi (encoder P) (encoder Q) (encoder R)=
      phi (encoder p) (encoder q) (encoder r) := by
    dsimp only [P,Q,R]
    rw [g.encoder_map,g.encoder_map,g.encoder_map,g.phi_map]
  have hledger : UniformLedger P Q R ↔ UniformLedger p q r := by
    constructor
    · intro hl i j k
      have h := hl i j k
      dsimp only [P,Q,R] at h
      rwa [g.ledger_map] at h
    · intro hl i j k
      dsimp only [P,Q,R]
      rw [g.ledger_map]
      exact hl i j k
  rwa [hphi,hledger] at h

end
end Glennie
