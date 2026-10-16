module

public import Glennie.Theorems.Frames
public import Glennie.Compact.Affine20.Relabel
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases

/- The explicitly ordered traceless Q family of the three native frame encoders.
   This is a native formula binding, not an invariant-ring generation theorem. -/

@[expose] public section

namespace Glennie.Compact.NativeQFamilyLedger

open Glennie Glennie.Compact.Affine20
open scoped BigOperators

noncomputable section

def spectralSum (p : Fin 3 → Albert) (a : Fin 3 → ℝ) : Albert :=
  ∑ i, a i • p i

theorem inner_spectralSum (p q : Fin 3 → Albert) (a b : Fin 3 → ℝ) :
    inner (spectralSum p a) (spectralSum q b) =
      ∑ i, ∑ j, (a i * b j) * inner (p i) (q j) := by
  simp [spectralSum, Fin.sum_univ_three, inner_add_left, inner_add_right,
    inner_smul_left, inner_smul_right]
  ring

theorem ledger_spectralSum (p q r : Fin 3 → Albert)
    (a b c : Fin 3 → ℝ) :
    trace (jordan (jordan (spectralSum p a) (spectralSum q b))
      (spectralSum r c)) =
      ∑ i, ∑ j, ∑ k, (a i * b j * c k) * ledger p q r i j k := by
  simp [spectralSum, Fin.sum_univ_three, ledger, jordan_add_left, jordan_add_right,
    jordan_smul_left, jordan_smul_right, trace_add, trace_smul]
  ring

def framePower (p : Fin 3 → Albert) (s : Fin 2) : Albert :=
  if s = 0 then encoder p else jordan (encoder p) (encoder p)

def encoderWeight (s : Fin 2) (i : Fin 3) : ℝ :=
  if s = 0 then (![-1, 0, 1] : Fin 3 → ℝ) i
  else (![1, 0, 1] : Fin 3 → ℝ) i

theorem framePower_spectralSum (p : Fin 3 → Albert) (hp : Frame p)
    (s : Fin 2) :
    framePower p s = spectralSum p (encoderWeight s) := by
  fin_cases s
  · simp [framePower, spectralSum, encoderWeight, Fin.sum_univ_three, encoder]
    abel
  · simp [framePower, spectralSum, encoderWeight, Fin.sum_univ_three,
      frame_encoder_square p hp]
    abel

theorem framePower_inner_ledger (T : Triple)
    (hT : ∀ a, Frame (T a)) (u v : Fin 3) (s t : Fin 2) :
    inner (framePower (T u) s) (framePower (T v) t) =
      ∑ i, ∑ j, (encoderWeight s i * encoderWeight t j) *
        inner (T u i) (T v j) := by
  rw [framePower_spectralSum _ (hT u) s,
    framePower_spectralSum _ (hT v) t]
  exact inner_spectralSum _ _ _ _

theorem framePower_triple_ledger (T : Triple)
    (hT : ∀ a, Frame (T a)) (s t u : Fin 2) :
    trace (jordan (jordan (framePower (T 0) s) (framePower (T 1) t))
      (framePower (T 2) u)) =
      ∑ i, ∑ j, ∑ k,
        (encoderWeight s i * encoderWeight t j * encoderWeight u k) *
          (ledger54 T).1 i j k := by
  rw [framePower_spectralSum _ (hT 0) s,
    framePower_spectralSum _ (hT 1) t,
    framePower_spectralSum _ (hT 2) u]
  simpa only [ledger54_C] using ledger_spectralSum (T 0) (T 1) (T 2)
    (encoderWeight s) (encoderWeight t) (encoderWeight u)

def qSingle (T : Triple) (v : Fin 3) (s : Fin 2) : ℝ :=
  inner (framePower (T v) 0) (framePower (T v) s)

def qPair (T : Triple) (v w : Fin 3) (s t : Fin 2) : ℝ :=
  inner (framePower (T v) s) (framePower (T w) t)

def qTriple (T : Triple) (s t u : Fin 2) : ℝ :=
  trace (jordan (jordan (framePower (T 0) s) (framePower (T 1) t))
    (framePower (T 2) u))

/-- The 26 traceless script values in exact order: six single powers, four values
for each of (x,y), (y,z), (z,x), and eight left-bracketed triple values. -/
def q26 (T : Triple) : Fin 26 → ℝ := ![
  qSingle T 0 0, qSingle T 0 1, qSingle T 1 0, qSingle T 1 1,
  qSingle T 2 0, qSingle T 2 1,
  qPair T 0 1 0 0, qPair T 0 1 0 1, qPair T 0 1 1 0, qPair T 0 1 1 1,
  qPair T 1 2 0 0, qPair T 1 2 0 1, qPair T 1 2 1 0, qPair T 1 2 1 1,
  qPair T 2 0 0 0, qPair T 2 0 0 1, qPair T 2 0 1 0, qPair T 2 0 1 1,
  qTriple T 0 0 0, qTriple T 0 0 1, qTriple T 0 1 0, qTriple T 0 1 1,
  qTriple T 1 0 0, qTriple T 1 0 1, qTriple T 1 1 0, qTriple T 1 1 1]

theorem qSingle_frame (T : Triple) (hT : ∀ v, Frame (T v))
    (v : Fin 3) (s : Fin 2) : qSingle T v s = if s = 0 then 2 else 0 := by
  fin_cases s
  · simpa [qSingle, framePower] using frame_encoder_norm (T v) (hT v)
  · change inner (encoder (T v))
        (jordan (encoder (T v)) (encoder (T v))) = 0
    change trace (jordan (encoder (T v))
      (jordan (encoder (T v)) (encoder (T v)))) = 0
    rw [frame_encoder_cube (T v) (hT v)]
    exact frame_encoder_trace (T v) (hT v)

theorem qPair_xy_ledger (T : Triple) (hT : ∀ v, Frame (T v))
    (s t : Fin 2) : qPair T 0 1 s t =
      ∑ i, ∑ j, (encoderWeight s i * encoderWeight t j) *
        (ledger54 T).2.1 i j := by
  simpa only [qPair, ledger54_P] using framePower_inner_ledger T hT 0 1 s t

theorem qPair_yz_ledger (T : Triple) (hT : ∀ v, Frame (T v))
    (s t : Fin 2) : qPair T 1 2 s t =
      ∑ j, ∑ k, (encoderWeight s j * encoderWeight t k) *
        (ledger54 T).2.2.1 j k := by
  simpa only [qPair, ledger54_Q] using framePower_inner_ledger T hT 1 2 s t

theorem qPair_zx_ledger (T : Triple) (hT : ∀ v, Frame (T v))
    (s t : Fin 2) : qPair T 2 0 s t =
      ∑ k, ∑ i, (encoderWeight s k * encoderWeight t i) *
        (ledger54 T).2.2.2 k i := by
  simpa only [qPair, ledger54_R] using framePower_inner_ledger T hT 2 0 s t

theorem qTriple_ledger (T : Triple) (hT : ∀ v, Frame (T v))
    (s t u : Fin 2) : qTriple T s t u =
      ∑ i, ∑ j, ∑ k,
        (encoderWeight s i * encoderWeight t j * encoderWeight u k) *
          (ledger54 T).1 i j k := by
  exact framePower_triple_ledger T hT s t u

/-- Equal complete ordered-frame ledgers yield equal native script-ordered Q26
values. This is the one-way binding; no invariant-ring generation is used. -/
theorem q26_eq_of_ledger54_eq (T S : Triple)
    (hT : ∀ v, Frame (T v)) (hS : ∀ v, Frame (S v))
    (h : ledger54 T = ledger54 S) : q26 T = q26 S := by
  have hs (v : Fin 3) (s : Fin 2) : qSingle T v s = qSingle S v s := by
    rw [qSingle_frame T hT, qSingle_frame S hS]
  have hxy (s t : Fin 2) : qPair T 0 1 s t = qPair S 0 1 s t := by
    rw [qPair_xy_ledger T hT, qPair_xy_ledger S hS, h]
  have hyz (s t : Fin 2) : qPair T 1 2 s t = qPair S 1 2 s t := by
    rw [qPair_yz_ledger T hT, qPair_yz_ledger S hS, h]
  have hzx (s t : Fin 2) : qPair T 2 0 s t = qPair S 2 0 s t := by
    rw [qPair_zx_ledger T hT, qPair_zx_ledger S hS, h]
  have htr (s t u : Fin 2) : qTriple T s t u = qTriple S s t u := by
    rw [qTriple_ledger T hT, qTriple_ledger S hS, h]
  funext n
  fin_cases n <;> simp [q26, hs, hxy, hyz, hzx, htr]

private def momentWeight (r i : Fin 3) : ℝ :=
  if r = 0 then 1 else if r = 1 then encoderWeight 0 i else encoderWeight 1 i

private def frameMoment (p : Fin 3 → Albert) (r : Fin 3) : Albert :=
  if r = 0 then 1 else if r = 1 then framePower p 0 else framePower p 1

private theorem frameMoment_spectralSum (p : Fin 3 → Albert) (hp : Frame p)
    (r : Fin 3) :
    frameMoment p r = spectralSum p (momentWeight r) := by
  fin_cases r
  · simp [frameMoment, momentWeight, spectralSum, Fin.sum_univ_three,
      ← hp.sum_unit]
  · change framePower p 0 = spectralSum p (momentWeight 1)
    have hw : momentWeight 1 = encoderWeight 0 := by
      funext i
      norm_num [momentWeight]
    rw [hw]
    exact framePower_spectralSum p hp 0
  · change framePower p 1 = spectralSum p (momentWeight 2)
    have hw : momentWeight 2 = encoderWeight 1 := by
      funext i
      norm_num [momentWeight]
    rw [hw]
    exact framePower_spectralSum p hp 1

private theorem frameMoment_trace (p : Fin 3 → Albert) (hp : Frame p)
    (r : Fin 3) :
    trace (frameMoment p r) =
      if r = 0 then 3 else if r = 1 then 0 else 2 := by
  fin_cases r
  · simp [frameMoment]
  · simpa [frameMoment, framePower] using frame_encoder_trace p hp
  · simpa [frameMoment, framePower, inner] using frame_encoder_norm p hp

private theorem frameMoment_pos (p : Fin 3 → Albert) (r : Fin 3)
    (hr : r ≠ 0) :
    frameMoment p r = framePower p (if r = 1 then 0 else 1) := by
  fin_cases r <;> simp_all [frameMoment]

private def moment2 (p q : Fin 3 → Albert) (r s : Fin 3) : ℝ :=
  inner (frameMoment p r) (frameMoment q s)

private theorem moment2_eq_of_pos_data
    (p q p' q' : Fin 3 → Albert)
    (hp : Frame p) (hq : Frame q) (hp' : Frame p') (hq' : Frame q')
    (hpos : ∀ a b : Fin 2, inner (framePower p a) (framePower q b) =
      inner (framePower p' a) (framePower q' b))
    (r s : Fin 3) :
    moment2 p q r s = moment2 p' q' r s := by
  by_cases hr : r = 0
  · subst r
    change inner 1 (frameMoment q s) = inner 1 (frameMoment q' s)
    rw [inner_unit_left, inner_unit_left]
    rw [frameMoment_trace q hq s, frameMoment_trace q' hq' s]
  · by_cases hs : s = 0
    · subst s
      change inner (frameMoment p r) 1 = inner (frameMoment p' r) 1
      rw [inner_unit_right, inner_unit_right]
      rw [frameMoment_trace p hp r, frameMoment_trace p' hp' r]
    · simp only [moment2]
      rw [frameMoment_pos p r hr, frameMoment_pos q s hs,
        frameMoment_pos p' r hr, frameMoment_pos q' s hs]
      exact hpos _ _

private def moment3 (T : Triple) (r s t : Fin 3) : ℝ :=
  trace (jordan (jordan (frameMoment (T 0) r) (frameMoment (T 1) s))
    (frameMoment (T 2) t))

private theorem moment3_first_zero (T : Triple) (s t : Fin 3) :
    moment3 T 0 s t = moment2 (T 1) (T 2) s t := by
  simp [moment3, moment2, frameMoment, inner, jordan_unit_left]

private theorem moment3_middle_zero (T : Triple) (r t : Fin 3) :
    moment3 T r 0 t = moment2 (T 2) (T 0) t r := by
  change trace (jordan (jordan (frameMoment (T 0) r) 1)
    (frameMoment (T 2) t)) =
    trace (jordan (frameMoment (T 2) t) (frameMoment (T 0) r))
  rw [jordan_unit_right, jordan_comm]

private theorem moment3_last_zero (T : Triple) (r s : Fin 3) :
    moment3 T r s 0 = moment2 (T 0) (T 1) r s := by
  simp [moment3, moment2, frameMoment, inner, jordan_unit_right]

private theorem qPair_xy_eq_of_q26_eq (T S : Triple) (h : q26 T = q26 S)
    (a b : Fin 2) : qPair T 0 1 a b = qPair S 0 1 a b := by
  fin_cases a <;> fin_cases b
  · simpa [q26] using congrFun h (6 : Fin 26)
  · simpa [q26] using congrFun h (7 : Fin 26)
  · simpa [q26] using congrFun h (8 : Fin 26)
  · simpa [q26] using congrFun h (9 : Fin 26)

private theorem qPair_yz_eq_of_q26_eq (T S : Triple) (h : q26 T = q26 S)
    (a b : Fin 2) : qPair T 1 2 a b = qPair S 1 2 a b := by
  fin_cases a <;> fin_cases b
  · simpa [q26] using congrFun h (10 : Fin 26)
  · simpa [q26] using congrFun h (11 : Fin 26)
  · simpa [q26] using congrFun h (12 : Fin 26)
  · simpa [q26] using congrFun h (13 : Fin 26)

private theorem qPair_zx_eq_of_q26_eq (T S : Triple) (h : q26 T = q26 S)
    (a b : Fin 2) : qPair T 2 0 a b = qPair S 2 0 a b := by
  fin_cases a <;> fin_cases b
  · simpa [q26] using congrFun h (14 : Fin 26)
  · simpa [q26] using congrFun h (15 : Fin 26)
  · simpa [q26] using congrFun h (16 : Fin 26)
  · simpa [q26] using congrFun h (17 : Fin 26)

private theorem qTriple_eq_of_q26_eq (T S : Triple) (h : q26 T = q26 S)
    (a b c : Fin 2) : qTriple T a b c = qTriple S a b c := by
  fin_cases a <;> fin_cases b <;> fin_cases c
  · simpa [q26] using congrFun h (18 : Fin 26)
  · simpa [q26] using congrFun h (19 : Fin 26)
  · simpa [q26] using congrFun h (20 : Fin 26)
  · simpa [q26] using congrFun h (21 : Fin 26)
  · simpa [q26] using congrFun h (22 : Fin 26)
  · simpa [q26] using congrFun h (23 : Fin 26)
  · simpa [q26] using congrFun h (24 : Fin 26)
  · simpa [q26] using congrFun h (25 : Fin 26)

private theorem moment3_eq_of_q26_eq (T S : Triple)
    (hT : ∀ a, Frame (T a)) (hS : ∀ a, Frame (S a))
    (h : q26 T = q26 S) (r s t : Fin 3) :
    moment3 T r s t = moment3 S r s t := by
  have hxy : ∀ a b, moment2 (T 0) (T 1) a b =
      moment2 (S 0) (S 1) a b :=
    moment2_eq_of_pos_data _ _ _ _ (hT 0) (hT 1) (hS 0) (hS 1)
      (qPair_xy_eq_of_q26_eq T S h)
  have hyz : ∀ a b, moment2 (T 1) (T 2) a b =
      moment2 (S 1) (S 2) a b :=
    moment2_eq_of_pos_data _ _ _ _ (hT 1) (hT 2) (hS 1) (hS 2)
      (qPair_yz_eq_of_q26_eq T S h)
  have hzx : ∀ a b, moment2 (T 2) (T 0) a b =
      moment2 (S 2) (S 0) a b :=
    moment2_eq_of_pos_data _ _ _ _ (hT 2) (hT 0) (hS 2) (hS 0)
      (qPair_zx_eq_of_q26_eq T S h)
  by_cases hr : r = 0
  · subst r
    rw [moment3_first_zero, moment3_first_zero]
    exact hyz s t
  · by_cases hs : s = 0
    · subst s
      rw [moment3_middle_zero, moment3_middle_zero]
      exact hzx t r
    · by_cases ht : t = 0
      · subst t
        rw [moment3_last_zero, moment3_last_zero]
        exact hxy r s
      · simp only [moment3]
        rw [frameMoment_pos (T 0) r hr, frameMoment_pos (T 1) s hs,
          frameMoment_pos (T 2) t ht,
          frameMoment_pos (S 0) r hr, frameMoment_pos (S 1) s hs,
          frameMoment_pos (S 2) t ht]
        exact qTriple_eq_of_q26_eq T S h _ _ _

private def weighted1 (f : Fin 3 → ℝ) (r : Fin 3) : ℝ :=
  ∑ i, momentWeight r i * f i

private theorem weighted1_ext (f g : Fin 3 → ℝ)
    (h : ∀ r, weighted1 f r = weighted1 g r) : f = g := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  norm_num [weighted1, momentWeight, encoderWeight, Fin.sum_univ_three] at h0 h1 h2
  have hf0 : f 0 = g 0 := by linarith
  have hf1 : f 1 = g 1 := by linarith
  have hf2 : f 2 = g 2 := by linarith
  funext i
  fin_cases i
  · simpa using hf0
  · simpa using hf1
  · simpa using hf2

private def weighted3 (C : Fin 3 → Fin 3 → Fin 3 → ℝ)
    (r s t : Fin 3) : ℝ :=
  ∑ i, ∑ j, ∑ k, (momentWeight r i * momentWeight s j * momentWeight t k) *
    C i j k

private theorem weighted3_as_nested (C : Fin 3 → Fin 3 → Fin 3 → ℝ)
    (r s t : Fin 3) :
    weighted3 C r s t =
      weighted1 (fun i => weighted1 (fun j => weighted1 (C i j) t) s) r := by
  simp [weighted3, weighted1, Finset.mul_sum, mul_assoc]

private theorem weighted3_ext (C D : Fin 3 → Fin 3 → Fin 3 → ℝ)
    (h : ∀ r s t, weighted3 C r s t = weighted3 D r s t) : C = D := by
  have hi (i s t : Fin 3) :
      weighted1 (fun j => weighted1 (C i j) t) s =
        weighted1 (fun j => weighted1 (D i j) t) s := by
    have h' := weighted1_ext
      (fun i => weighted1 (fun j => weighted1 (C i j) t) s)
      (fun i => weighted1 (fun j => weighted1 (D i j) t) s)
      (fun r => by
        rw [← weighted3_as_nested, ← weighted3_as_nested]
        exact h r s t)
    exact congrFun h' i
  have hj (i j t : Fin 3) :
      weighted1 (C i j) t = weighted1 (D i j) t := by
    exact congrFun (weighted1_ext
      (fun j => weighted1 (C i j) t)
      (fun j => weighted1 (D i j) t)
      (fun s => hi i s t)) j
  funext i j
  exact weighted1_ext (C i j) (D i j) (fun t => hj i j t)

private theorem moment3_weighted3 (T : Triple) (hT : ∀ a, Frame (T a))
    (r s t : Fin 3) :
    moment3 T r s t = weighted3 (ledger54 T).1 r s t := by
  unfold moment3
  rw [frameMoment_spectralSum (T 0) (hT 0) r,
    frameMoment_spectralSum (T 1) (hT 1) s,
    frameMoment_spectralSum (T 2) (hT 2) t]
  simpa only [weighted3, ledger54_C] using
    ledger_spectralSum (T 0) (T 1) (T 2)
      (momentWeight r) (momentWeight s) (momentWeight t)

private theorem ledger54_Q_first_marginal (T : Triple) (hT : ∀ a, Frame (T a))
    (j k : Fin 3) :
    (ledger54 T).2.2.1 j k = ∑ i, (ledger54 T).1 i j k := by
  rw [ledger54_Q]
  rw [← ledger_last_marginal (T 1) (T 2) (T 0) (hT 0) j k]
  simp only [ledger54_C]
  apply Finset.sum_congr rfl
  intro i _
  exact (ledger_cyclic (T 0) (T 1) (T 2) i j k).symm

private theorem ledger54_R_middle_marginal (T : Triple) (hT : ∀ a, Frame (T a))
    (k i : Fin 3) :
    (ledger54 T).2.2.2 k i = ∑ j, (ledger54 T).1 i j k := by
  rw [ledger54_R]
  rw [← ledger_last_marginal (T 2) (T 0) (T 1) (hT 1) k i]
  simp only [ledger54_C]
  apply Finset.sum_congr rfl
  intro j _
  calc
    ledger (T 2) (T 0) (T 1) k i j =
        ledger (T 0) (T 1) (T 2) i j k := by
          rw [ledger_cyclic]
    _ = _ := rfl

/-- On two ordered native frame triples, equality of the exact script-ordered
Q26 family recovers all 27 triple cells and all three pair blocks. -/
theorem ledger54_eq_of_q26_eq (T S : Triple)
    (hT : ∀ a, Frame (T a)) (hS : ∀ a, Frame (S a))
    (h : q26 T = q26 S) : ledger54 T = ledger54 S := by
  have hC : (ledger54 T).1 = (ledger54 S).1 :=
    weighted3_ext _ _ (fun r s t => by
      rw [← moment3_weighted3 T hT r s t,
        ← moment3_weighted3 S hS r s t]
      exact moment3_eq_of_q26_eq T S hT hS h r s t)
  refine Prod.ext hC (Prod.ext ?_ (Prod.ext ?_ ?_))
  · funext i j
    calc
      (ledger54 T).2.1 i j = ∑ k, (ledger54 T).1 i j k := by
        simpa only [ledger54_P, ledger54_C] using
          (ledger_last_marginal (T 0) (T 1) (T 2) (hT 2) i j).symm
      _ = ∑ k, (ledger54 S).1 i j k := by rw [hC]
      _ = (ledger54 S).2.1 i j := by
        simpa only [ledger54_P, ledger54_C] using
          ledger_last_marginal (S 0) (S 1) (S 2) (hS 2) i j
  · funext j k
    rw [ledger54_Q_first_marginal T hT, ledger54_Q_first_marginal S hS, hC]
  · funext k i
    rw [ledger54_R_middle_marginal T hT, ledger54_R_middle_marginal S hS, hC]

/-- The finite Q26 and full54 ledgers carry exactly the same equality data
for ordered native frames, with no invariant-ring or orbit premise. -/
theorem q26_eq_iff_ledger54_eq (T S : Triple)
    (hT : ∀ a, Frame (T a)) (hS : ∀ a, Frame (S a)) :
    q26 T = q26 S ↔ ledger54 T = ledger54 S := by
  constructor
  · exact ledger54_eq_of_q26_eq T S hT hS
  · exact q26_eq_of_ledger54_eq T S hT hS

end
end Glennie.Compact.NativeQFamilyLedger
