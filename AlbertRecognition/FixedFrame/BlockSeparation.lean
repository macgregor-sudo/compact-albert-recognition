/- Finite native eigenvalue separation for the bounded fixed-frame gate.
-/
module

public import AlbertRecognition.FixedFrame.ReferenceBlocks

@[expose] public section
namespace AlbertRecognition.FixedFrame
noncomputable section
open Glennie

@[simp] private theorem octPair_zero : ((0, 0) : Octonion) = 0 := rfl

/-- Actual complementary diagonal curvature vanishes, on every native input. -/
theorem D_h0_h1_zero : D (h 0) (h 1) = 0 := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  rw [D_apply_native]
  apply Albert.ext
  all_goals simp [h, e, unit, jordan_d0, jordan_d1, jordan_d2,
    jordan_o01, jordan_o02, jordan_o12, octDot_coordinates,
    octMul, octConj, octPair_zero, smul_smul, smul_add, smul_sub, smul_eq_mul]
  all_goals norm_num <;> ring

/-- The distinguished h0 also commutes with the complementary slot12 action. -/
theorem D_h0_X12_zero (a : Octonion) : D (h 0) (X12 a) = 0 := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  rw [D_apply_native]
  apply Albert.ext
  all_goals simp [h, e, unit, X12, jordan_d0, jordan_d1, jordan_d2,
    jordan_o01, jordan_o02, jordan_o12, octDot_coordinates,
    octMul, octConj, octPair_zero, smul_smul, smul_add, smul_sub, smul_eq_mul]
  all_goals first
    | exact sub_self _
    | (solve | (norm_num <;> ring))
    | (apply Prod.ext <;> apply Quaternion.ext <;>
        simp [smul_eq_mul] <;> ring)

/-- Raw coordinate units have unit octDot norm; raw slots are not rescaled. -/
theorem octDot_basis_self (t : Fin 8) : octDot (octBasis t) (octBasis t) = 1 := by
  fin_cases t <;> norm_num [octBasis, octDot_coordinates, octNormSq, Quaternion.normSq_def',
    octScalar, qi, qj, qk]

theorem octBasis_imag_square (t : Fin 8) (ht : t ≠ 0) :
    octMul (octBasis t) (octBasis t) = octScalar (-1) := by
  fin_cases t <;> simp_all [octBasis]
  all_goals apply Prod.ext <;> apply Quaternion.ext <;>
    norm_num [octMul, octScalar, qi, qj, qk,
      Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul]

/-- Native brackets plus proved right alternativity give each J_t squared. -/
theorem spinJ_basis_square (t : Fin 8) (s : Spin) :
    spinJ (octBasis t) (spinJ (octBasis t) s) = -s := by
  rcases s with ⟨u,v⟩
  by_cases ht : t = 0
  · subst t
    simp
  · rw [spinJ_imag_apply _ (octBasis_conj_imag t ht),
      spinJ_imag_apply _ (octBasis_conj_imag t ht)]
    have hsquare (z : Octonion) :
        octMul (octMul z (octBasis t)) (octBasis t) = -z := by
      rw [octMul_right_alternative, octBasis_imag_square t ht, octMul_scalar_right]
      simp
    apply Prod.ext
    · exact hsquare u
    · exact hsquare v

/-- The literal eight-coordinate resolution, with every coefficient native. -/
theorem oct_basis_resolution (z : Octonion) :
    octDot (octBasis 0) z • octBasis 0 + octDot (octBasis 1) z • octBasis 1 +
      octDot (octBasis 2) z • octBasis 2 + octDot (octBasis 3) z • octBasis 3 +
      octDot (octBasis 4) z • octBasis 4 + octDot (octBasis 5) z • octBasis 5 +
      octDot (octBasis 6) z • octBasis 6 + octDot (octBasis 7) z • octBasis 7 = z := by
  have h := (oct_decompose z).symm
  simpa [octBasis, octDot_coordinates, octScalar, qi, qj, qk] using h

def frameSquare (a : Octonion) : Module.End ℝ V :=
  (frameAction a).comp (frameAction a)

/-- Literal eight-term sum of the squared native operators, without renormalization. -/
def frameSquareSum : Module.End ℝ V :=
  frameSquare (octBasis 0) + frameSquare (octBasis 1) +
    frameSquare (octBasis 2) + frameSquare (octBasis 3) +
    frameSquare (octBasis 4) + frameSquare (octBasis 5) +
    frameSquare (octBasis 6) + frameSquare (octBasis 7)

theorem frameSquare_h0 (a : Octonion) : frameSquare a (h 0) = 0 := by
  simp [frameSquare, frameAction_h0]

theorem frameSquare_d (t : Fin 8) :
    frameSquare (octBasis t) frameD = -(9/4 : ℝ) • frameD := by
  simp only [frameSquare, LinearMap.comp_apply, frameAction_d, map_smul,
    frameAction_X12, octDot_basis_self]
  module

theorem frameSquare_X12 (t : Fin 8) (z : Octonion) :
    frameSquare (octBasis t) (X12 z) =
      -(9/4 : ℝ) • X12 (octDot (octBasis t) z • octBasis t) := by
  simp only [frameSquare, LinearMap.comp_apply, frameAction_X12, map_smul,
    frameAction_d]
  module

theorem frameSquare_spin (t : Fin 8) (s : Spin) :
    frameSquare (octBasis t) (frameSpin s) = -(9/16 : ℝ) • frameSpin s := by
  simp only [frameSquare, LinearMap.comp_apply, frameAction_spin, map_smul,
    spinJ_basis_square, map_neg]
  module

theorem frameSquareSum_h0 : frameSquareSum (h 0) = 0 := by
  simp [frameSquareSum, frameSquare_h0]

theorem frameSquareSum_d : frameSquareSum frameD = -(18 : ℝ) • frameD := by
  simp only [frameSquareSum, LinearMap.add_apply, frameSquare_d]
  module

theorem frameSquareSum_X12 (z : Octonion) :
    frameSquareSum (X12 z) = -(9/4 : ℝ) • X12 z := by
  simp only [frameSquareSum, LinearMap.add_apply, frameSquare_X12]
  have h := congrArg (fun x : V => -(9/4 : ℝ) • x)
    (congrArg X12 (oct_basis_resolution z))
  simpa only [map_add, smul_add] using h

theorem frameSquareSum_spin (s : Spin) :
    frameSquareSum (frameSpin s) = -(9/2 : ℝ) • frameSpin s := by
  simp only [frameSquareSum, LinearMap.add_apply, frameSquare_spin]
  module

/-- Four actual rational eigenvalues, on the exact1+1+8+16 coordinates. -/
theorem frameSquareSum_frameEmbed (a b : ℝ) (z : Octonion) (s : Spin) :
    frameSquareSum (frameEmbed (a,b,z,s)) =
      frameEmbed (0,-18*b,-(9/4 : ℝ) • z,-(9/2 : ℝ) • s) := by
  rw [frameEmbed_eq, frameEmbed_eq]
  simp only [map_add, map_smul, frameSquareSum_h0, frameSquareSum_d,
    frameSquareSum_X12, frameSquareSum_spin, zero_smul, zero_add]
  module

theorem frameSquareSum_coordinates (x : V) :
    frameCoordinates (frameSquareSum x) =
      (0,-18*(frameCoordinates x).2.1,-(9/4 : ℝ) • (frameCoordinates x).2.2.1,
        -(9/2 : ℝ) • (frameCoordinates x).2.2.2) := by
  let c := frameCoordinates x
  have hx : frameEmbed (c.1,c.2.1,c.2.2.1,c.2.2.2) = x :=
    frameCoordinates.symm_apply_apply x
  calc
    frameCoordinates (frameSquareSum x) =
        frameCoordinates (frameSquareSum (frameEmbed (c.1,c.2.1,c.2.2.1,c.2.2.2))) :=
      congrArg (fun y : V => frameCoordinates (frameSquareSum y)) hx.symm
    _ = _ := by
      rw [frameSquareSum_frameEmbed]
      exact frameCoordinates.apply_symm_apply _

/-- Eigenvectors satisfy four literal coordinate equations. -/
theorem frame_eigen_equations (lambda : ℝ) (x : V)
    (hx : frameSquareSum x = lambda • x) :
    0 = lambda*(frameCoordinates x).1 ∧
      -18*(frameCoordinates x).2.1 = lambda*(frameCoordinates x).2.1 ∧
      -(9/4 : ℝ) • (frameCoordinates x).2.2.1 = lambda • (frameCoordinates x).2.2.1 ∧
      -(9/2 : ℝ) • (frameCoordinates x).2.2.2 = lambda • (frameCoordinates x).2.2.2 := by
  have h := congrArg frameCoordinates hx
  rw [frameSquareSum_coordinates, map_smul] at h
  exact ⟨congrArg (fun c : FrameCoordinates => c.1) h,
    congrArg (fun c : FrameCoordinates => c.2.1) h,
    congrArg (fun c : FrameCoordinates => c.2.2.1) h,
    congrArg (fun c : FrameCoordinates => c.2.2.2) h⟩

private theorem scalar_eigen_conflict {M : Type*} [AddCommGroup M] [Module ℝ M]
    (r s : ℝ) (hrs : r ≠ s) (x : M) (hx : r • x = s • x) : x = 0 := by
  have hzero : (r-s) • x = 0 := by rw [sub_smul, hx]; simp
  have h := congrArg (fun y : M => (r-s)⁻¹ • y) hzero
  simpa only [smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr hrs), one_smul, smul_zero] using h

def frameLambda : Fin 4 → ℝ := ![0,-18,-(9/4),-(9/2)]

def FrameBlock (k : Fin 4) (x : V) : Prop :=
  ![(frameCoordinates x).2.1 = 0 ∧ (frameCoordinates x).2.2.1 = 0 ∧
      (frameCoordinates x).2.2.2 = 0,
    (frameCoordinates x).1 = 0 ∧ (frameCoordinates x).2.2.1 = 0 ∧
      (frameCoordinates x).2.2.2 = 0,
    (frameCoordinates x).1 = 0 ∧ (frameCoordinates x).2.1 = 0 ∧
      (frameCoordinates x).2.2.2 = 0,
    (frameCoordinates x).1 = 0 ∧ (frameCoordinates x).2.1 = 0 ∧
      (frameCoordinates x).2.2.1 = 0] k

/-- The four eigenspaces are exactly the four concrete native coordinate blocks. -/
theorem frame_eigen_iff (k : Fin 4) (x : V) :
    frameSquareSum x = frameLambda k • x ↔ FrameBlock k x := by
  constructor
  · intro hx
    obtain ⟨ha,hb,hzv,hsv⟩ := frame_eigen_equations (frameLambda k) x hx
    have hz : (-(9/4 : ℝ)) • (frameCoordinates x).2.2.1 =
        frameLambda k • (frameCoordinates x).2.2.1 := by
      simpa only [neg_smul] using hzv
    have hs : (-(9/2 : ℝ)) • (frameCoordinates x).2.2.2 =
        frameLambda k • (frameCoordinates x).2.2.2 := by
      simpa only [neg_smul] using hsv
    fin_cases k
    · change -18*(frameCoordinates x).2.1 = (0 : ℝ)*(frameCoordinates x).2.1 at hb
      change (-(9/4 : ℝ)) • (frameCoordinates x).2.2.1 =
        (0 : ℝ) • (frameCoordinates x).2.2.1 at hz
      change (-(9/2 : ℝ)) • (frameCoordinates x).2.2.2 =
        (0 : ℝ) • (frameCoordinates x).2.2.2 at hs
      change (frameCoordinates x).2.1 = 0 ∧ (frameCoordinates x).2.2.1 = 0 ∧
        (frameCoordinates x).2.2.2 = 0
      refine ⟨by linarith, ?_, ?_⟩
      · exact scalar_eigen_conflict (M := Octonion) (-(9/4 : ℝ)) 0
          (by norm_num) (frameCoordinates x).2.2.1 hz
      · exact scalar_eigen_conflict (M := Spin) (-(9/2 : ℝ)) 0
          (by norm_num) (frameCoordinates x).2.2.2 hs
    · change 0 = (-18 : ℝ)*(frameCoordinates x).1 at ha
      change (-(9/4 : ℝ)) • (frameCoordinates x).2.2.1 =
        (-18 : ℝ) • (frameCoordinates x).2.2.1 at hz
      change (-(9/2 : ℝ)) • (frameCoordinates x).2.2.2 =
        (-18 : ℝ) • (frameCoordinates x).2.2.2 at hs
      change (frameCoordinates x).1 = 0 ∧ (frameCoordinates x).2.2.1 = 0 ∧
        (frameCoordinates x).2.2.2 = 0
      refine ⟨by linarith, ?_, ?_⟩
      · exact scalar_eigen_conflict (M := Octonion) (-(9/4 : ℝ)) (-18)
          (by norm_num) (frameCoordinates x).2.2.1 hz
      · exact scalar_eigen_conflict (M := Spin) (-(9/2 : ℝ)) (-18)
          (by norm_num) (frameCoordinates x).2.2.2 hs
    · change 0 = (-(9/4 : ℝ))*(frameCoordinates x).1 at ha
      change -18*(frameCoordinates x).2.1 = (-(9/4 : ℝ))*(frameCoordinates x).2.1 at hb
      change (-(9/2 : ℝ)) • (frameCoordinates x).2.2.2 =
        (-(9/4 : ℝ)) • (frameCoordinates x).2.2.2 at hs
      change (frameCoordinates x).1 = 0 ∧ (frameCoordinates x).2.1 = 0 ∧
        (frameCoordinates x).2.2.2 = 0
      refine ⟨by linarith, by linarith, ?_⟩
      exact scalar_eigen_conflict (M := Spin) (-(9/2 : ℝ)) (-(9/4 : ℝ))
        (by norm_num) (frameCoordinates x).2.2.2 hs
    · change 0 = (-(9/2 : ℝ))*(frameCoordinates x).1 at ha
      change -18*(frameCoordinates x).2.1 = (-(9/2 : ℝ))*(frameCoordinates x).2.1 at hb
      change (-(9/4 : ℝ)) • (frameCoordinates x).2.2.1 =
        (-(9/2 : ℝ)) • (frameCoordinates x).2.2.1 at hz
      change (frameCoordinates x).1 = 0 ∧ (frameCoordinates x).2.1 = 0 ∧
        (frameCoordinates x).2.2.1 = 0
      refine ⟨by linarith, by linarith, ?_⟩
      exact scalar_eigen_conflict (M := Octonion) (-(9/4 : ℝ)) (-(9/2 : ℝ))
        (by norm_num) (frameCoordinates x).2.2.1 hz
  · intro hx
    apply frameCoordinates.injective
    rw [frameSquareSum_coordinates, map_smul]
    fin_cases k
    · change (frameCoordinates x).2.1 = 0 ∧ (frameCoordinates x).2.2.1 = 0 ∧
        (frameCoordinates x).2.2.2 = 0 at hx
      obtain ⟨hb,hz,hs⟩ := hx
      change (0,-18*(frameCoordinates x).2.1,
          -(9/4 : ℝ) • (frameCoordinates x).2.2.1,
          -(9/2 : ℝ) • (frameCoordinates x).2.2.2) =
        ((0 : ℝ)*(frameCoordinates x).1,(0 : ℝ)*(frameCoordinates x).2.1,
          (0 : ℝ) • (frameCoordinates x).2.2.1,(0 : ℝ) • (frameCoordinates x).2.2.2)
      simp only [hb,hz,hs,mul_zero,zero_mul,zero_smul,smul_zero,neg_zero]
    · change (frameCoordinates x).1 = 0 ∧ (frameCoordinates x).2.2.1 = 0 ∧
        (frameCoordinates x).2.2.2 = 0 at hx
      obtain ⟨ha,hz,hs⟩ := hx
      change (0,-18*(frameCoordinates x).2.1,
          -(9/4 : ℝ) • (frameCoordinates x).2.2.1,
          -(9/2 : ℝ) • (frameCoordinates x).2.2.2) =
        ((-18 : ℝ)*(frameCoordinates x).1,(-18 : ℝ)*(frameCoordinates x).2.1,
          (-18 : ℝ) • (frameCoordinates x).2.2.1,(-18 : ℝ) • (frameCoordinates x).2.2.2)
      simp only [ha,hz,hs,mul_zero,smul_zero,neg_zero]
    · change (frameCoordinates x).1 = 0 ∧ (frameCoordinates x).2.1 = 0 ∧
        (frameCoordinates x).2.2.2 = 0 at hx
      obtain ⟨ha,hb,hs⟩ := hx
      change (0,-18*(frameCoordinates x).2.1,
          -(9/4 : ℝ) • (frameCoordinates x).2.2.1,
          -(9/2 : ℝ) • (frameCoordinates x).2.2.2) =
        ((-(9/4 : ℝ))*(frameCoordinates x).1,(-(9/4 : ℝ))*(frameCoordinates x).2.1,
          (-(9/4 : ℝ)) • (frameCoordinates x).2.2.1,
          (-(9/4 : ℝ)) • (frameCoordinates x).2.2.2)
      simp only [ha,hb,hs,mul_zero,smul_zero,neg_zero,neg_smul]
    · change (frameCoordinates x).1 = 0 ∧ (frameCoordinates x).2.1 = 0 ∧
        (frameCoordinates x).2.2.1 = 0 at hx
      obtain ⟨ha,hb,hz⟩ := hx
      change (0,-18*(frameCoordinates x).2.1,
          -(9/4 : ℝ) • (frameCoordinates x).2.2.1,
          -(9/2 : ℝ) • (frameCoordinates x).2.2.2) =
        ((-(9/2 : ℝ))*(frameCoordinates x).1,(-(9/2 : ℝ))*(frameCoordinates x).2.1,
          (-(9/2 : ℝ)) • (frameCoordinates x).2.2.1,
          (-(9/2 : ℝ)) • (frameCoordinates x).2.2.2)
      simp only [ha,hb,hz,mul_zero,smul_zero,neg_zero,neg_smul]

/-- An arbitrary linear operator commuting with all8 native actions commutes
with their literal squared sum. No metric or self-adjointness premise is used. -/
theorem frameSquareSum_commutes (G : Module.End ℝ V)
    (hG : ∀ t : Fin 8, G.comp (frameAction (octBasis t)) =
      (frameAction (octBasis t)).comp G) :
    G.comp frameSquareSum = frameSquareSum.comp G := by
  have hs (t : Fin 8) (x : V) :
      G (frameSquare (octBasis t) x) = frameSquare (octBasis t) (G x) := by
    have h : ∀ y : V, G (frameAction (octBasis t) y) =
        frameAction (octBasis t) (G y) := by
      intro y
      exact LinearMap.congr_fun (hG t) y
    change G (frameAction (octBasis t) (frameAction (octBasis t) x)) =
      frameAction (octBasis t) (frameAction (octBasis t) (G x))
    rw [h, h]
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply, frameSquareSum, LinearMap.add_apply, map_add, hs]

/-- Abstract linear eigenvector preservation, proved before specializing the
closed native eight-square operator. No spectral or metric premise is assumed. -/
private theorem linear_commutant_preserves_eigenvector {M : Type*}
    [AddCommGroup M] [Module ℝ M] (G T : Module.End ℝ M)
    (hGT : G.comp T = T.comp G) (lambda : ℝ) (x : M)
    (hx : T x = lambda • x) : T (G x) = lambda • G x := by
  have h := LinearMap.congr_fun hGT x
  change G (T x) = T (G x) at h
  rw [hx, map_smul] at h
  exact h.symm

section FrameBlockPreservation

/- Keep the proved closed operator opaque only during this final proof's
elaboration; its definition and kernel-level body are unchanged. -/
attribute [local irreducible] frameSquareSum

/-- Finite block separation for every arbitrary real-linear commutant. -/
theorem frame_commutant_preserves_blocks (G : Module.End ℝ V)
    (hG : ∀ t : Fin 8, G.comp (frameAction (octBasis t)) =
      (frameAction (octBasis t)).comp G) (k : Fin 4) (x : V)
    (hx : FrameBlock k x) : FrameBlock k (G x) := by
  set_option backward.isDefEq.respectTransparency true in
    with_reducible
      apply (frame_eigen_iff k (G x)).mp
      exact @linear_commutant_preserves_eigenvector V inferInstance inferInstance
        G frameSquareSum (frameSquareSum_commutes G hG) (frameLambda k) x
        ((frame_eigen_iff k x).mpr hx)

end FrameBlockPreservation

end
end AlbertRecognition.FixedFrame
