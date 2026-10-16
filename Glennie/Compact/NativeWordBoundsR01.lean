/- Generic bounded native words and frame-amplitude square bounds.
   This is algebraic cone/order semantics, with no physical implementation claim. -/
module
public import Glennie.NativeQuadraticPositiveR01
public import Glennie.Theorems.Frames
public import Glennie.Compact.PositiveFilterAlgebraR01

@[expose] public section
namespace Glennie.Compact.NativeWordBoundsR01
open Glennie Glennie.NativeSquareConeR01 Glennie.NativeQuadraticPositiveR01
open Glennie.Compact.OperationalPhi Glennie.Compact.PositiveFilterAlgebraR01
noncomputable section
set_option autoImplicit false

theorem idempotent_complement_positive (p : Albert) (hp : jordan p p = p) :
    Positive ((1 : Albert) - p) := by
  apply positive_idempotent
  simp only [jordan_sub_left, jordan_sub_right, jordan_unit_left,
    jordan_unit_right, hp]
  module

theorem frame_amplitude_eq (p : Fin 3 → Albert) (hp : Frame p) (s : Bool) :
    amplitude (encoder p) s = (if s then p 0 else p 2) + (1 / 2 : ℝ) • p 1 := by
  cases s <;> simp [amplitude, halfAmplitude, encoder, ← hp.sum_unit] <;> module

theorem frame_amplitude_positive (p : Fin 3 → Albert) (hp : Frame p) (s : Bool) :
    Positive (amplitude (encoder p) s) := by
  rw [frame_amplitude_eq p hp]
  apply positive_add
  · cases s <;> exact positive_idempotent _ (hp.idempotent _)
  · exact positive_smul _ _ (by norm_num) (positive_idempotent _ (hp.idempotent 1))

theorem frame_amplitude_square (p : Fin 3 → Albert) (hp : Frame p) (s : Bool) :
    jordan (amplitude (encoder p) s) (amplitude (encoder p) s) =
      (if s then p 0 else p 2) + (1 / 4 : ℝ) • p 1 := by
  rw [frame_amplitude_eq p hp]
  cases s
  · simp only [Bool.false_eq_true, ite_false, jordan_add_left, jordan_add_right,
      jordan_smul_left, jordan_smul_right, hp.idempotent,
      hp.orthogonal 2 1 (by decide), hp.orthogonal 1 2 (by decide)]
    module
  · simp only [ite_true, jordan_add_left, jordan_add_right,
      jordan_smul_left, jordan_smul_right, hp.idempotent,
      hp.orthogonal 0 1 (by decide), hp.orthogonal 1 0 (by decide)]
    module

theorem frame_amplitude_square_complement (p : Fin 3 → Albert) (hp : Frame p)
    (s : Bool) :
    (1 : Albert) - jordan (amplitude (encoder p) s) (amplitude (encoder p) s) =
      (if s then p 2 else p 0) + (3 / 4 : ℝ) • p 1 := by
  rw [frame_amplitude_square p hp, ← hp.sum_unit]
  cases s <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> module

theorem frame_amplitude_square_le (p : Fin 3 → Albert) (hp : Frame p) (s : Bool) :
    Positive ((1 : Albert) - jordan (amplitude (encoder p) s)
      (amplitude (encoder p) s)) := by
  rw [frame_amplitude_square_complement p hp]
  apply positive_add
  · cases s <;> exact positive_idempotent _ (hp.idempotent _)
  · exact positive_smul _ _ (by norm_num) (positive_idempotent _ (hp.idempotent 1))

/-- The signed encoder also meets the needed square bound. -/
theorem frame_encoder_square_le (p : Fin 3 → Albert) (hp : Frame p) :
    Positive ((1 : Albert) - jordan (encoder p) (encoder p)) := by
  rw [frame_projector_middle p hp]
  exact positive_idempotent _ (hp.idempotent 1)

/-- Leftmost amplitude is applied last; the empty word is the identity. -/
def applyWord : List Albert → Albert → Albert
  | [], x => x
  | a :: as, x => U a (applyWord as x)

theorem applyWord_positive_trace_le (as : List Albert) :
    (∀ a ∈ as, Positive ((1 : Albert) - jordan a a)) →
    ∀ x : Albert, Positive x →
      Positive (applyWord as x) ∧ trace (applyWord as x) ≤ trace x := by
  induction as with
  | nil =>
    intro ha x hx
    exact ⟨hx, le_rfl⟩
  | cons a as ih =>
    intro ha x hx
    have ht := ih (fun b hb => ha b (List.mem_cons_of_mem a hb)) x hx
    have hu := U_positive_trace_le a (applyWord as x) ht.1
      (ha a (by simp))
    exact ⟨hu.1, hu.2.trans ht.2⟩

/-- State is a trace-one idempotent; effect can be any idempotent.
The map assumptions are only native square bounds on the listed amplitudes. -/
theorem idempotent_word_pairing_bounds (as : List Albert)
    (ha : ∀ a ∈ as, Positive ((1 : Albert) - jordan a a))
    (e p : Albert) (he : jordan e e = e) (hp : jordan p p = p)
    (ht : trace p = 1) :
    0 ≤ inner e (applyWord as p) ∧ inner e (applyWord as p) ≤ 1 := by
  have hw := applyWord_positive_trace_le as ha p (positive_idempotent p hp)
  exact effect_pairing_bounds e (applyWord as p) (positive_idempotent e he)
    (idempotent_complement_positive e he) hw.1 (by simpa [ht] using hw.2)

/-- Native primitive-overlap bounds require no separate nonnegative-overlap premise. -/
theorem traceOne_idempotent_overlap_bounds (e p : Albert)
    (he : jordan e e = e) (hp : jordan p p = p) (ht : trace p = 1) :
    0 ≤ inner e p ∧ inner e p ≤ 1 := by
  exact idempotent_word_pairing_bounds [] (by simp) e p he hp ht

end
end Glennie.Compact.NativeWordBoundsR01
