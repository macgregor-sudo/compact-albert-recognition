/- Native h0 scalar blocks for the bounded unrestricted cubic gate.
-/
module

public import AlbertRecognition.JacobiBridge

@[expose] public section
namespace AlbertRecognition.FixedFrame
noncomputable section
open Glennie

private theorem oct_domain_linear_ext {M : Type*} [AddCommMonoid M] [Module ℝ M]
    (f g : Octonion →ₗ[ℝ] M)
    (h : ∀ t : Fin 8, f (octBasis t) = g (octBasis t)) : f = g := by
  apply LinearMap.ext
  intro z
  rw [oct_decompose z]
  simp only [map_add, map_smul, h]

/-- The actual ordered spin-coordinate projection, a real-linear map. -/
def frameSpinProjection : V →ₗ[ℝ] Spin :=
  (LinearMap.snd ℝ Octonion Spin).comp
    ((LinearMap.snd ℝ ℝ (Octonion × Spin)).comp
      ((LinearMap.snd ℝ ℝ (ℝ × Octonion × Spin)).comp frameCoordinates.toLinearMap))

@[simp] theorem frameSpinProjection_apply (x : V) :
    frameSpinProjection x = (frameCoordinates x).2.2.2 := rfl

@[simp] theorem frameSpinProjection_frameSpin (s : Spin) :
    frameSpinProjection (frameSpin s) = s := by
  rcases s with ⟨u,v⟩
  change (((frameSpin (u,v) : V) : Albert).o01,
    ((frameSpin (u,v) : V) : Albert).o02) = (u,v)
  simp [frameSpin, X01, X02]

theorem frameSpin_injective : Function.Injective frameSpin := by
  intro s t h
  have h' := congrArg frameSpinProjection h
  simpa only [frameSpinProjection_frameSpin] using h'

private theorem frameBlock_h0 : FrameBlock 0 (h 0) := by
  apply (frame_eigen_iff 0 (h 0)).mp
  simpa [frameLambda] using frameSquareSum_h0

private theorem frameBlock_d : FrameBlock 1 frameD := by
  apply (frame_eigen_iff 1 frameD).mp
  simpa [frameLambda] using frameSquareSum_d

private theorem frameBlock_spin (s : Spin) : FrameBlock 3 (frameSpin s) := by
  apply (frame_eigen_iff 3 (frameSpin s)).mp
  simpa [frameLambda] using frameSquareSum_spin s

/-- One-dimensional block coefficient read from the actual rational coordinates. -/
theorem frame_commutant_h0_scalar (G : Module.End ℝ V)
    (hG : ∀ t : Fin 8, G.comp (frameAction (octBasis t)) =
      (frameAction (octBasis t)).comp G) :
    G (h 0) = (frameCoordinates (G (h 0))).1 • h 0 := by
  have hp := frame_commutant_preserves_blocks G hG 0 (h 0) frameBlock_h0
  change (frameCoordinates (G (h 0))).2.1 = 0 ∧
    (frameCoordinates (G (h 0))).2.2.1 = 0 ∧
    (frameCoordinates (G (h 0))).2.2.2 = 0 at hp
  obtain ⟨hb,hz,hs⟩ := hp
  have hd := frame_decompose (G (h 0))
  rw [hb,hz,hs] at hd
  simpa only [zero_smul, map_zero, add_zero] using hd

theorem frame_commutant_d_scalar (G : Module.End ℝ V)
    (hG : ∀ t : Fin 8, G.comp (frameAction (octBasis t)) =
      (frameAction (octBasis t)).comp G) :
    G frameD = (frameCoordinates (G frameD)).2.1 • frameD := by
  have hp := frame_commutant_preserves_blocks G hG 1 frameD frameBlock_d
  change (frameCoordinates (G frameD)).1 = 0 ∧
    (frameCoordinates (G frameD)).2.2.1 = 0 ∧
    (frameCoordinates (G frameD)).2.2.2 = 0 at hp
  obtain ⟨ha,hz,hs⟩ := hp
  have hd := frame_decompose (G frameD)
  rw [ha,hz,hs] at hd
  simpa only [zero_smul, map_zero, zero_add, add_zero] using hd

/-- The actual d-to-slot arrows force the same scalar on all eight slot directions. -/
theorem frame_commutant_X12_scalar (G : Module.End ℝ V)
    (hG : ∀ t : Fin 8, G.comp (frameAction (octBasis t)) =
      (frameAction (octBasis t)).comp G)
    (b : ℝ) (hd : G frameD = b • frameD) (z : Octonion) :
    G (X12 z) = b • X12 z := by
  have hb (t : Fin 8) : G (X12 (octBasis t)) = b • X12 (octBasis t) := by
    have h := LinearMap.congr_fun (hG t) frameD
    change G (frameAction (octBasis t) frameD) =
      frameAction (octBasis t) (G frameD) at h
    rw [frameAction_d, map_smul, hd, map_smul, frameAction_d] at h
    have h' := congrArg (fun v : V => (2/3 : ℝ) • v) h
    have hl : (2/3 : ℝ)*(3/2) = 1 := by norm_num
    have hr : (2/3 : ℝ)*(b*(3/2)) = b := by ring
    simpa only [smul_smul, hl, hr, one_smul] using h'
  have heq : G.comp X12 = b • X12 := oct_domain_linear_ext _ _ hb
  exact LinearMap.congr_fun heq z

/-- Native spin restriction; the support claim is separately proved from preservation. -/
def nativeSpinRestriction (G : Module.End ℝ V) : Module.End ℝ Spin :=
  frameSpinProjection.comp (G.comp frameSpin)

theorem frame_commutant_spin_reconstruct (G : Module.End ℝ V)
    (hG : ∀ t : Fin 8, G.comp (frameAction (octBasis t)) =
      (frameAction (octBasis t)).comp G) (s : Spin) :
    G (frameSpin s) = frameSpin (nativeSpinRestriction G s) := by
  have hp := frame_commutant_preserves_blocks G hG 3 (frameSpin s) (frameBlock_spin s)
  change (frameCoordinates (G (frameSpin s))).1 = 0 ∧
    (frameCoordinates (G (frameSpin s))).2.1 = 0 ∧
    (frameCoordinates (G (frameSpin s))).2.2.1 = 0 at hp
  obtain ⟨ha,hb,hz⟩ := hp
  have hd := frame_decompose (G (frameSpin s))
  rw [ha,hb,hz] at hd
  simpa only [zero_smul, zero_add, map_zero, nativeSpinRestriction,
    LinearMap.comp_apply, frameSpinProjection_apply] using hd

/-- The actual3/4 spin coefficient cancels; the restricted operator commutes J_t. -/
theorem nativeSpinRestriction_commutes (G : Module.End ℝ V)
    (hG : ∀ t : Fin 8, G.comp (frameAction (octBasis t)) =
      (frameAction (octBasis t)).comp G) (t : Fin 8) :
    (nativeSpinRestriction G).comp (spinJ (octBasis t)) =
      (spinJ (octBasis t)).comp (nativeSpinRestriction G) := by
  apply LinearMap.ext
  intro s
  apply frameSpin_injective
  have hscaled :
      (3/4 : ℝ) • frameSpin (nativeSpinRestriction G (spinJ (octBasis t) s)) =
        (3/4 : ℝ) • frameSpin (spinJ (octBasis t) (nativeSpinRestriction G s)) := by
    calc
      (3/4 : ℝ) • frameSpin (nativeSpinRestriction G (spinJ (octBasis t) s)) =
          G (frameAction (octBasis t) (frameSpin s)) := by
        rw [frameAction_spin, map_smul, frame_commutant_spin_reconstruct G hG]
      _ = frameAction (octBasis t) (G (frameSpin s)) :=
        LinearMap.congr_fun (hG t) (frameSpin s)
      _ = (3/4 : ℝ) • frameSpin (spinJ (octBasis t) (nativeSpinRestriction G s)) := by
        rw [frame_commutant_spin_reconstruct G hG, frameAction_spin]
  have h := congrArg (fun v : V => (4/3 : ℝ) • v) hscaled
  have hc : (4/3 : ℝ)*(3/4) = 1 := by norm_num
  simpa only [LinearMap.comp_apply, smul_smul, hc, one_smul] using h

/-- Native16D scalar commutant transfers back to the actual spin embedding. -/
theorem frame_commutant_spin_scalar (G : Module.End ℝ V)
    (hG : ∀ t : Fin 8, G.comp (frameAction (octBasis t)) =
      (frameAction (octBasis t)).comp G) :
    ∃ c : ℝ, ∀ s : Spin, G (frameSpin s) = c • frameSpin s := by
  obtain ⟨c,hc⟩ := spin_commutant_scalar (nativeSpinRestriction G)
    (nativeSpinRestriction_commutes G hG)
  refine ⟨c, ?_⟩
  intro s
  rw [frame_commutant_spin_reconstruct G hG, hc]
  exact map_smul frameSpin c s

/-- Three scalar blocks for any arbitrary real-linear native commutant. -/
theorem frame_commutant_scalar_blocks (G : Module.End ℝ V)
    (hG : ∀ t : Fin 8, G.comp (frameAction (octBasis t)) =
      (frameAction (octBasis t)).comp G) :
    ∃ a b c : ℝ, G (h 0) = a • h 0 ∧ G frameD = b • frameD ∧
      (∀ z : Octonion, G (X12 z) = b • X12 z) ∧
      (∀ s : Spin, G (frameSpin s) = c • frameSpin s) := by
  let a := (frameCoordinates (G (h 0))).1
  let b := (frameCoordinates (G frameD)).2.1
  have ha : G (h 0) = a • h 0 := frame_commutant_h0_scalar G hG
  have hb : G frameD = b • frameD := frame_commutant_d_scalar G hG
  obtain ⟨c,hc⟩ := frame_commutant_spin_scalar G hG
  exact ⟨a,b,c,ha,hb,frame_commutant_X12_scalar G hG b hb,hc⟩

/-- Concrete unrestricted-cubic consequence; only the original Jacobi kernel
hypothesis is supplied. No reference invariance or self-adjointness is assumed. -/
theorem h0_scalar_blocks_of_A_q_zero (B : SymmetricCubic)
    (hB : A (q referenceCubic) B = 0) :
    ∃ a b c : ℝ, KB B (h 0) (h 0) = a • h 0 ∧
      KB B (h 0) frameD = b • frameD ∧
      (∀ z : Octonion, KB B (h 0) (X12 z) = b • X12 z) ∧
      (∀ s : Spin, KB B (h 0) (frameSpin s) = c • frameSpin s) := by
  apply frame_commutant_scalar_blocks (KB B (h 0))
  intro t
  apply LinearMap.ext
  intro x
  exact h0_frame_action_intertwines_of_A_q_zero B hB (octBasis t) x

end
end AlbertRecognition.FixedFrame
