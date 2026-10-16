module
public import Glennie.Compact.NativeWordBoundsR01
public import Glennie.Compact.PositiveWord16DefinitionR01

/- Native square-cone bounds for each actual 16-label evaluation.
   This does not construct a physical filter or sampling protocol. -/
@[expose] public section
namespace Glennie.Compact.PositiveWord16BoundsR01
open Glennie Glennie.NativeSquareConeR01
open Glennie.Compact.PositiveFilterAlgebraR01
open Glennie.Compact.PositiveWordLayersR01
open Glennie.Compact.PositiveWordEndpointR01
open Glennie.Compact.PositiveWord16DefinitionR01
open Glennie.Compact.NativeWordBoundsR01
noncomputable section
set_option autoImplicit false

def amplitudes (p q r : Fin 3 → Albert) (o l : Bool) : List Albert :=
  if o then [encoder p, encoder q, encoder r, amplitude (encoder p) l]
  else [encoder q, encoder p, encoder r, amplitude (encoder p) l]

private theorem uLinear_apply (w v : Albert) :
    uLinear w v = U w v := rfl

private theorem filterLinear_apply (w : Albert) (l : Bool) (v : Albert) :
    filterLinear w l v = filter w l v := rfl

theorem word_eq_applyWord (p q r : Fin 3 → Albert) (v : Albert) (o l : Bool) :
    word (encoder p) (encoder q) (encoder r) v o l =
      applyWord (amplitudes p q r o l) v := by
  cases o <;> simp only [word, wordLinear, outerLinear, amplitudes,
    Bool.false_eq_true, ite_false, ite_true, LinearMap.comp_apply,
    uLinear_apply, filterLinear_apply, filter, applyWord]

theorem amplitudes_square_bound (p q r : Fin 3 → Albert)
    (hp : Frame p) (hq : Frame q) (hr : Frame r) (o l : Bool) :
    ∀ b ∈ amplitudes p q r o l,
      Positive ((1 : Albert) - jordan b b) := by
  intro b hb
  cases o <;> simp [amplitudes] at hb
  all_goals rcases hb with rfl | rfl | rfl | rfl
  all_goals first
    | exact frame_encoder_square_le p hp
    | exact frame_encoder_square_le q hq
    | exact frame_encoder_square_le r hr
    | exact frame_amplitude_square_le p hp l

theorem endpoint_idempotent (p : Fin 3 → Albert) (hp : Frame p) (s : Bool) :
    jordan (endpoint p s) (endpoint p s) = endpoint p s := by
  cases s <;> simp [endpoint, hp.idempotent]

theorem endpoint_trace_one (p : Fin 3 → Albert) (hp : Frame p) (s : Bool) :
    trace (endpoint p s) = 1 := by
  cases s <;> simp [endpoint, hp.trace_one]

theorem evaluation_bounds (p q r : Fin 3 → Albert)
    (hp : Frame p) (hq : Frame q) (hr : Frame r) (a : Label16) :
    0 ≤ evaluation p q r a ∧ evaluation p q r a ≤ 1 := by
  rcases a with ⟨o, l, k, j⟩
  simp only [evaluation]
  rw [word_eq_applyWord]
  exact idempotent_word_pairing_bounds (amplitudes p q r o l)
    (amplitudes_square_bound p q r hp hq hr o l)
    (endpoint r k) (endpoint q j)
    (endpoint_idempotent r hr k) (endpoint_idempotent q hq j)
    (endpoint_trace_one q hq j)

end
end Glennie.Compact.PositiveWord16BoundsR01
