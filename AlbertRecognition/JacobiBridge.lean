/- Universal Jacobi bridge for an unrestricted symmetric cubic.
The wedge cancellation is derived from the actual metric-raised KB, and the
concrete frame step uses native reference vanishing identities.  This is an
algebraic prerequisite, not the log-Hessian/Levi-Civita recognition endpoint. -/
module

public import AlbertRecognition.FixedFrame.BlockSeparation

@[expose] public section
namespace AlbertRecognition
noncomputable section

@[simp] theorem operatorComm_apply (P Q : V →ₗ[ℝ] V) (v : V) :
    operatorComm P Q v = P (Q v) - Q (P v) := rfl

@[simp] theorem operatorComm_zero_right (P : V →ₗ[ℝ] V) :
    operatorComm P 0 = 0 := by
  apply LinearMap.ext
  intro v
  simp only [operatorComm_apply, LinearMap.zero_apply, map_zero, sub_self]

theorem operatorComm_add_right (P Q R : V →ₗ[ℝ] V) :
    operatorComm P (Q + R) = operatorComm P Q + operatorComm P R := by
  apply LinearMap.ext
  intro v
  simp only [operatorComm_apply, LinearMap.add_apply, map_add]
  module

theorem operatorComm_swap (P Q : V →ₗ[ℝ] V) :
    operatorComm P Q = -operatorComm Q P := by
  apply LinearMap.ext
  intro v
  simp only [operatorComm_apply, LinearMap.neg_apply, neg_sub]

theorem wedge_swap (x y : V) : wedge x y = -wedge y x := by
  apply LinearMap.ext
  intro v
  change gA y v • x - gA x v • y = -(gA x v • y - gA y v • x)
  exact (neg_sub _ _).symm

/-- Total cubic symmetry cancels the entire wedge Jacobi term.  KB symmetry
and self-adjointness are the derived metric-dual identities, not hypotheses. -/
theorem A_wedge_eq_zero (B : SymmetricCubic) : A wedge B = 0 := by
  funext x y z
  apply LinearMap.ext
  intro v
  change
    ((KB B x) (gA z v • y - gA y v • z) -
      (gA z (KB B x v) • y - gA y (KB B x v) • z)) +
    ((KB B y) (gA x v • z - gA z v • x) -
      (gA x (KB B y v) • z - gA z (KB B y v) • x)) +
    ((KB B z) (gA y v • x - gA x v • y) -
      (gA y (KB B z v) • x - gA x (KB B z v) • y)) = 0
  simp only [map_sub, map_smul]
  rw [← KB_selfadjoint B x z v, ← KB_selfadjoint B x y v,
    ← KB_selfadjoint B y x v, ← KB_selfadjoint B y z v,
    ← KB_selfadjoint B z y v, ← KB_selfadjoint B z x v]
  rw [KB_comm B x y, KB_comm B x z, KB_comm B y z]
  module

/-- The actual cyclic commutator is additive in its reference tensor. -/
theorem A_add_target (T U : V → V → (V →ₗ[ℝ] V)) (B : SymmetricCubic) :
    A (fun x y => T x y + U x y) B = A T B + A U B := by
  funext x y z
  simp only [A, operatorComm_add_right, Pi.add_apply]
  module

/-- Adding the wedge term does not change the Jacobi equation on any cubic. -/
theorem A_D_eq_A_q (B : SymmetricCubic) :
    A D B = A (q referenceCubic) B := by
  change A (fun x y => wedge x y + q referenceCubic x y) B = _
  rw [A_add_target, A_wedge_eq_zero, zero_add]

theorem A_D_zero_of_A_q_zero (B : SymmetricCubic)
    (hB : A (q referenceCubic) B = 0) : A D B = 0 := by
  rw [A_D_eq_A_q]
  exact hB

theorem D_swap (x y : V) : D y x = -D x y := by
  unfold D q
  rw [wedge_swap y x, operatorComm_swap (KB referenceCubic y) (KB referenceCubic x)]
  module

/-- A pointwise reduction of the actual Jacobi equation.  The concrete frame
corollary below discharges both vanishing identities from native multiplication. -/
theorem commutes_of_A_D_zero_of_vanishing (B : SymmetricCubic)
    (hB : A D B = 0) (x y z : V)
    (hxy : D x y = 0) (hxz : D x z = 0) :
    operatorComm (KB B x) (D y z) = 0 := by
  have hzx : D z x = 0 := by rw [D_swap, hxz, neg_zero]
  have hcyclic : A D B x y z = 0 := congrArg (fun F => F x y z) hB
  simpa only [A, hzx, hxy, operatorComm_zero_right, zero_add, add_zero] using hcyclic

namespace FixedFrame

/-- The unrestricted unknown's h0 operator commutes with every actual native
frameAction.  The only input is the literal reference-q Jacobi kernel equation. -/
theorem h0_frame_commutes_of_A_q_zero (B : SymmetricCubic)
    (hB : A (q referenceCubic) B = 0) (a : Glennie.Octonion) :
    operatorComm (KB B (h 0)) (frameAction a) = 0 := by
  exact commutes_of_A_D_zero_of_vanishing B (A_D_zero_of_A_q_zero B hB)
    (h 0) (h 1) (X12 a) D_h0_h1_zero (D_h0_X12_zero a)

/-- Application form used by the subsequent native block-commutant argument. -/
theorem h0_frame_action_intertwines_of_A_q_zero (B : SymmetricCubic)
    (hB : A (q referenceCubic) B = 0) (a : Glennie.Octonion) (v : V) :
    KB B (h 0) (frameAction a v) = frameAction a (KB B (h 0) v) := by
  have hcomm := congrArg (fun P : V →ₗ[ℝ] V => P v)
    (h0_frame_commutes_of_A_q_zero B hB a)
  change KB B (h 0) (frameAction a v) - frameAction a (KB B (h 0) v) = 0 at hcomm
  exact sub_eq_zero.mp hcomm

/-- The actual unknown h0 operator preserves all four native eigenspace blocks.
The block-separation premise is discharged by its derived eight commutations. -/
theorem h0_frame_blocks_preserved_of_A_q_zero (B : SymmetricCubic)
    (hB : A (q referenceCubic) B = 0) (k : Fin 4) (v : V)
    (hv : FrameBlock k v) : FrameBlock k (KB B (h 0) v) := by
  apply frame_commutant_preserves_blocks (KB B (h 0)) ?_ k v hv
  intro t
  apply LinearMap.ext
  intro x
  exact h0_frame_action_intertwines_of_A_q_zero B hB (octBasis t) x

end FixedFrame
end
end AlbertRecognition
