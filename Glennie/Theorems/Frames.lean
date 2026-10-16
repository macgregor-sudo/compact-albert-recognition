module

public import Glennie.Native.AlgebraLaws
public import Glennie.Theorems.ScalarEstimates
public import Mathlib.Tactic.Module

/- Native frame encoder and marginal identities, without spectral assumptions. -/

public section

namespace Glennie
noncomputable section

theorem frame_encoder_trace (p : Fin 3 → Albert) (hp : Frame p) :
    trace (encoder p) = 0 := by
  simp [encoder, hp.trace_one]

theorem frame_encoder_square (p : Fin 3 → Albert) (hp : Frame p) :
    jordan (encoder p) (encoder p) = p 2 + p 0 := by
  simp [encoder, jordan_sub_left, jordan_sub_right, hp.idempotent,
    hp.orthogonal 2 0 (by decide), hp.orthogonal 0 2 (by decide)]

theorem frame_encoder_cube (p : Fin 3 → Albert) (hp : Frame p) :
    jordan (encoder p) (jordan (encoder p) (encoder p)) = encoder p := by
  rw [frame_encoder_square p hp]
  simp only [encoder, jordan_sub_left, jordan_add_right, hp.idempotent,
    hp.orthogonal 2 0 (by decide), hp.orthogonal 0 2 (by decide),
    sub_zero, zero_sub]
  abel

theorem frame_encoder_norm (p : Fin 3 → Albert) (hp : Frame p) :
    inner (encoder p) (encoder p) = 2 := by
  rw [inner, frame_encoder_square p hp, trace_add, hp.trace_one, hp.trace_one]
  norm_num

theorem frame_projector_first (p : Fin 3 → Albert) (hp : Frame p) :
    (1 / 2 : ℝ) • (jordan (encoder p) (encoder p) - encoder p) = p 0 := by
  rw [frame_encoder_square p hp]
  unfold encoder
  module

theorem frame_projector_middle (p : Fin 3 → Albert) (hp : Frame p) :
    1 - jordan (encoder p) (encoder p) = p 1 := by
  rw [frame_encoder_square p hp, ← hp.sum_unit]
  abel

theorem frame_projector_last (p : Fin 3 → Albert) (hp : Frame p) :
    (1 / 2 : ℝ) • (jordan (encoder p) (encoder p) + encoder p) = p 2 := by
  rw [frame_encoder_square p hp]
  unfold encoder
  module

theorem ledger_cyclic (p q r : Fin 3 → Albert) (i j k : Fin 3) :
    ledger p q r i j k = ledger q r p j k i := by
  change inner (jordan (p i) (q j)) (r k) = inner (jordan (q j) (r k)) (p i)
  rw [inner_jordan_associative, inner_comm]

theorem ledger_last_marginal (p q r : Fin 3 → Albert) (hr : Frame r) (i j : Fin 3) :
    (∑ k, ledger p q r i j k) = inner (p i) (q j) := by
  simp only [Fin.sum_univ_three, ledger]
  rw [← trace_add, ← trace_add, ← jordan_add_right, ← jordan_add_right,
    hr.sum_unit, jordan_unit_right]
  rfl

theorem uniformLedger_pair_overlap (p q r : Fin 3 → Albert)
    (hr : Frame r) (hu : UniformLedger p q r) (i j : Fin 3) :
    inner (p i) (q j) = 1 / 3 := by
  rw [← ledger_last_marginal p q r hr i j]
  simp only [UniformLedger] at hu
  simp [hu, Fin.sum_univ_three]
  norm_num

theorem uniformLedger_cyclic (p q r : Fin 3 → Albert)
    (hu : UniformLedger p q r) : UniformLedger q r p := by
  intro j k i
  rw [← ledger_cyclic]
  exact hu i j k

theorem uniformLedger_encoders_orthogonal (p q r : Fin 3 → Albert)
    (hr : Frame r) (hu : UniformLedger p q r) :
    inner (encoder p) (encoder q) = 0 := by
  simp only [encoder, inner_sub_left, inner_sub_right,
    uniformLedger_pair_overlap p q r hr hu]
  norm_num

theorem ledger_total (p q r : Fin 3 → Albert)
    (hp : Frame p) (hq : Frame q) (hr : Frame r) :
    (∑ i, ∑ j, ∑ k, ledger p q r i j k) = 3 := by
  have hi (i : Fin 3) : (∑ j, inner (p i) (q j)) = trace (p i) := by
    simp only [Fin.sum_univ_three, inner]
    rw [← trace_add, ← trace_add, ← jordan_add_right, ← jordan_add_right,
      hq.sum_unit, jordan_unit_right]
  simp only [ledger_last_marginal p q r hr, hi, hp.trace_one, Fin.sum_univ_three]
  norm_num

theorem frame_encoder_inner_bounds (p q : Fin 3 → Albert)
    (hp : Frame p) (hq : Frame q) :
    -2 ≤ inner (encoder p) (encoder q) ∧ inner (encoder p) (encoder q) ≤ 2 := by
  have hplus := inner_self_nonneg (encoder p + encoder q)
  have hminus := inner_self_nonneg (encoder p - encoder q)
  simp only [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
    frame_encoder_norm p hp, frame_encoder_norm q hq] at hplus hminus
  rw [inner_comm (encoder q) (encoder p)] at hplus hminus
  constructor <;> linarith

theorem frame_gram_determinant_formula (p q r : Fin 3 → Albert)
    (hp : Frame p) (hq : Frame q) (hr : Frame r) :
    (gram (encoder p) (encoder q) (encoder r)).det =
      8 - 2 * (inner (encoder p) (encoder q) ^ 2 +
        inner (encoder p) (encoder r) ^ 2 + inner (encoder q) (encoder r) ^ 2) +
      2 * inner (encoder p) (encoder q) * inner (encoder p) (encoder r) *
        inner (encoder q) (encoder r) := by
  rw [Matrix.det_fin_three]
  simp [gram, triple, traceless, frame_encoder_trace p hp, frame_encoder_trace q hq,
    frame_encoder_trace r hr, frame_encoder_norm p hp, frame_encoder_norm q hq,
    frame_encoder_norm r hr, inner_comm (encoder q) (encoder p),
    inner_comm (encoder r) (encoder p), inner_comm (encoder r) (encoder q)]
  ring

theorem frame_gram_determinant_le_eight (p q r : Fin 3 → Albert)
    (hp : Frame p) (hq : Frame q) (hr : Frame r) :
    (gram (encoder p) (encoder q) (encoder r)).det ≤ 8 := by
  rw [frame_gram_determinant_formula p q r hp hq hr]
  obtain ⟨ha0, ha1⟩ := frame_encoder_inner_bounds p q hp hq
  exact ScalarEstimates.gram_det_le_eight _ _ _ ha0 ha1

theorem frame_gram_determinant_eq_eight_iff (p q r : Fin 3 → Albert)
    (hp : Frame p) (hq : Frame q) (hr : Frame r) :
    (gram (encoder p) (encoder q) (encoder r)).det = 8 ↔
      inner (encoder p) (encoder q) = 0 ∧ inner (encoder p) (encoder r) = 0 ∧
        inner (encoder q) (encoder r) = 0 := by
  rw [frame_gram_determinant_formula p q r hp hq hr]
  obtain ⟨ha0, ha1⟩ := frame_encoder_inner_bounds p q hp hq
  exact ScalarEstimates.gram_det_eq_eight_iff _ _ _ ha0 ha1

end
end Glennie
