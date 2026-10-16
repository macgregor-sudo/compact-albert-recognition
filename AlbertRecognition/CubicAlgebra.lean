/- Native arbitrary-cubic scaling and universal associative commutator Jacobi.
-/
module

public import AlbertRecognition.CubicOperators
public import Mathlib.Tactic.NoncommRing

@[expose] public section
namespace AlbertRecognition
noncomputable section

theorem symmetricCubic_eq_of_form_eq {B C : SymmetricCubic}
    (hform : B.form = C.form) : B = C := by
  cases B
  cases C
  cases hform
  rfl

/-- Literal real scaling of a genuine symmetric trilinear form. -/
def scalarCubic (r : ℝ) (B : SymmetricCubic) : SymmetricCubic where
  form := r • B.form
  swap12 x y z := congrArg (fun a : ℝ => r * a) (B.swap12 x y z)
  swap23 x y z := congrArg (fun a : ℝ => r * a) (B.swap23 x y z)

@[simp] theorem scalarCubic_form (r : ℝ) (B : SymmetricCubic) (x y z : V) :
    (scalarCubic r B).form x y z = r * B.form x y z := rfl

theorem scalarCubic_one (B : SymmetricCubic) : scalarCubic 1 B = B := by
  apply symmetricCubic_eq_of_form_eq
  exact one_smul ℝ B.form

/-- Raising the index with the same trace/3 metric commutes with real scaling. -/
theorem KB_scalarCubic (r : ℝ) (B : SymmetricCubic) :
    KB (scalarCubic r B) = r • KB B := by
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  apply metricDual.injective
  apply LinearMap.ext
  intro z
  change gA (KB (scalarCubic r B) x y) z = gA (r • KB B x y) z
  rw [KB_pairing, scalarCubic_form, gA_smul_left, KB_pairing]

/-- Pure associative-ring Jacobi, before native endomorphism specialization. -/
private theorem associative_commutator_jacobi {R : Type*} [Ring R] (P Q S : R) :
    P * (Q * S - S * Q) - (Q * S - S * Q) * P +
      (Q * (S * P - P * S) - (S * P - P * S) * Q) +
      (S * (P * Q - Q * P) - (P * Q - Q * P) * S) = 0 := by
  noncomm_ring

/-- Jacobi in the actual associative algebra of real linear endomorphisms. -/
theorem operatorComm_jacobi (P Q R : Module.End ℝ V) :
    operatorComm P (operatorComm Q R) + operatorComm Q (operatorComm R P) +
      operatorComm R (operatorComm P Q) = 0 := by
  apply LinearMap.ext
  intro v
  simp only [operatorComm, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.comp_apply, map_sub, LinearMap.zero_apply]
  abel

section SelfJacobi

/- Keep index raising opaque during specialization only; its definition and
kernel body remain unchanged. -/
attribute [local irreducible] KB

/-- Every genuine cubic satisfies Jacobi for its own q, without a Jordan premise. -/
theorem A_q_self (B : SymmetricCubic) : A (q B) B = 0 := by
  set_option backward.isDefEq.respectTransparency true in
    with_reducible
      funext x y z
      simpa only [A, q, Pi.zero_apply] using operatorComm_jacobi (KB B x) (KB B y) (KB B z)

end SelfJacobi

/-- Quadratic scaling for the literal native commutator tensor. -/
theorem q_scalarCubic (r : ℝ) (B : SymmetricCubic) :
    q (scalarCubic r B) = r^2 • q B := by
  funext x y
  apply LinearMap.ext
  intro z
  change operatorComm (KB (scalarCubic r B) x) (KB (scalarCubic r B) y) z =
    r^2 • operatorComm (KB B x) (KB B y) z
  rw [KB_scalarCubic]
  change (r • KB B x) ((r • KB B y) z) -
    (r • KB B y) ((r • KB B x) z) =
      r^2 • ((KB B x) ((KB B y) z) - (KB B y) ((KB B x) z))
  simp only [LinearMap.smul_apply, map_smul, smul_smul, pow_two]
  module

/-- The Jacobi constraint is linear in the unrestricted unknown cubic. -/
theorem A_scalarCubic (T : V → V → Module.End ℝ V) (r : ℝ)
    (B : SymmetricCubic) : A T (scalarCubic r B) = r • A T B := by
  funext x y z
  apply LinearMap.ext
  intro w
  rw [A, KB_scalarCubic]
  change (r • KB B x) (T y z w) - T y z ((r • KB B x) w) +
    ((r • KB B y) (T z x w) - T z x ((r • KB B y) w)) +
    ((r • KB B z) (T x y w) - T x y ((r • KB B z) w)) =
      r • (((KB B x) (T y z w) - T y z (KB B x w)) +
        ((KB B y) (T z x w) - T z x (KB B y w)) +
        ((KB B z) (T x y w) - T x y (KB B z w)))
  simp only [LinearMap.smul_apply, map_smul]
  module

/-- The actual kernel-line property, expressed in native trilinear forms. -/
def NativeKernelLine (C : SymmetricCubic) : Prop :=
  ∀ B : SymmetricCubic, A (q C) B = 0 ↔ ∃ r : ℝ, B = scalarCubic r C

end
end AlbertRecognition
