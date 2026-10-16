/- First-frame reversal, its chart-coordinate involution, and the oddness and continuity of Phi.

  * `revTriple T`: frame 0 read through the transposition (0 2), frames 1 and 2 unchanged.
    `revLedger`: the matching transposition of the first index of the C block, of the first
    index of P and of the second index of R. `ledger54_revTriple` is the naturality
    statement; it is a reduction, not a transport of the `ledgerAct` machinery, so
    nothing here depends on `Affine20.ledgerAct` or on `Affine20.relabel_ledger`.
  * `revLedger_revLedger`, `revLedger_inDomain`, `revLedger_affine`, then
    `tau := encode20 ∘ revLedger ∘ decode20` with `tau_tau`, `involutive_tau`, `tau_encode20`
    and `continuous_tau`.
  * `frame_swap`, `frame_revTriple`: a frame read through a permutation is a frame. This is the
    `hvalidReverse` input of the `RobustBranchReversal.reversalSection_valid` (:65).
  * `phiOf`, `encoder_revTriple_zero`, `phiOf_revTriple`: Phi is odd under the reversal, through
    the `BasicLaws.phi_smul_first` (BasicLaws.lean) at the scalar -1.
    `negPhiOf_revTriple` is the same fact in the shape
    `RobustBranchReversal.reversalSection_negative` (:52) takes at `phi := fun T => -phiOf T`,
    which is how the POSITIVE sign of the reversed section is obtained.
  * `continuous_U`, `continuous_phi3`, `continuous_phiOf`, `continuous_negPhiOf`,
    `continuous_revTriple`: the `hreverse` and sign-shrink continuity inputs, through 
    `Compactness.continuous_jordan` (Compactness.lean) and
    `Compactness.continuous_native_inner` (:41).

WHAT CANNOT BE INSTANTIATED, STATED PLAINLY. `RobustBranchReversal.reversalSection_ledger` (:40),
and hence `two_sections_of_reversal` (:92), take
`hledgerReverse : ∀ x, ledger (reverse x) = tau (ledger x)`, quantified over ALL of X. At
`X := Triple`, `ledger := fun T => encode20 (ledger54 T)` and this `tau`, that hypothesis is
FALSE: `tau (encode20 L) = encode20 (revLedger L)` needs `InDomain L` (it runs through
`Affine20.decode_encode`, Chart.lean), and the 54-entry ledger of an arbitrary triple is not
in the affine domain. This construction uses the lemmas whose hypotheses do hold universally
(`reversalDomain_isOpen` :77, `flat_mem_reversalDomain` :34, `reversalSection_continuousOn` :81,
`reversalSection_negative` :52, `reversalSection_valid` :65) and proves the ledger conjunct
natively in three lines, where the frame hypothesis is in hand. The alternative — instantiating
the whole of `two_sections_of_reversal` at the subtype `{T : Triple // ∀ a, Frame (T a)}` — does
work, but it makes the output subtype-valued; the section construction here uses the bare
triple domain.

No inverse-function, rank or section statement is made here. -/
module

public import Glennie.Compact.ChartTransfer
public import Glennie.Compactness
public import Glennie.BasicLaws
public import Mathlib.Logic.Equiv.Basic
public import Mathlib.Topology.Constructions
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Linarith

@[expose] public section

namespace Glennie.Compact.Sections

open Glennie.Compact.Affine20 Glennie.Compact.ChartTransfer

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

/-! ## The transposition (0 2) of Fin 3 -/

theorem swap02_zero : (Equiv.swap (0 : Fin 3) 2) 0 = 2 :=
  Equiv.swap_apply_left 0 2

theorem swap02_one : (Equiv.swap (0 : Fin 3) 2) 1 = 1 :=
  Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)

theorem swap02_two : (Equiv.swap (0 : Fin 3) 2) 2 = 0 :=
  Equiv.swap_apply_right 0 2

/-! ## First-frame reversal of a triple -/

/-- The first frame read through the transposition (0 2); frames 1 and 2 unchanged. -/
def revTriple (T : Triple) : Triple :=
  ![fun i => T 0 (Equiv.swap (0 : Fin 3) 2 i), T 1, T 2]

theorem revTriple_zero (T : Triple) :
    revTriple T 0 = fun i => T 0 (Equiv.swap (0 : Fin 3) 2 i) := rfl

theorem revTriple_one (T : Triple) : revTriple T 1 = T 1 := rfl

theorem revTriple_two (T : Triple) : revTriple T 2 = T 2 := rfl

theorem revTriple_revTriple (T : Triple) : revTriple (revTriple T) = T := by
  funext a i
  rcases fin3_cases a with rfl | rfl | rfl
  · show revTriple T 0 (Equiv.swap (0 : Fin 3) 2 i) = T 0 i
    rw [revTriple_zero]
    show T 0 (Equiv.swap (0 : Fin 3) 2 (Equiv.swap (0 : Fin 3) 2 i)) = T 0 i
    rw [Equiv.swap_apply_self]
  · rfl
  · rfl

/-! ## The matching involution of the 54 raw ledger entries -/

/-- The transposition (0 2) applied to the first C index, the first P index and the second
R index. -/
def revLedger (L : Ledger54) : Ledger54 :=
  (fun i j k => L.1 (Equiv.swap (0 : Fin 3) 2 i) j k,
    fun i j => L.2.1 (Equiv.swap (0 : Fin 3) 2 i) j,
    L.2.2.1,
    fun k i => L.2.2.2 k (Equiv.swap (0 : Fin 3) 2 i))

theorem revLedger_C (L : Ledger54) (i j k : Fin 3) :
    (revLedger L).1 i j k = L.1 (Equiv.swap (0 : Fin 3) 2 i) j k := rfl

theorem revLedger_P (L : Ledger54) (i j : Fin 3) :
    (revLedger L).2.1 i j = L.2.1 (Equiv.swap (0 : Fin 3) 2 i) j := rfl

theorem revLedger_Q (L : Ledger54) (j k : Fin 3) :
    (revLedger L).2.2.1 j k = L.2.2.1 j k := rfl

theorem revLedger_R (L : Ledger54) (k i : Fin 3) :
    (revLedger L).2.2.2 k i = L.2.2.2 k (Equiv.swap (0 : Fin 3) 2 i) := rfl

/-- Naturality: reversing the triple applies `revLedger` to its 54 raw entries. -/
theorem ledger54_revTriple (T : Triple) :
    ledger54 (revTriple T) = revLedger (ledger54 T) := by
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
  · funext i j k
    show trace (jordan (jordan (T 0 (Equiv.swap (0 : Fin 3) 2 i)) (T 1 j)) (T 2 k)) =
      trace (jordan (jordan (T 0 (Equiv.swap (0 : Fin 3) 2 i)) (T 1 j)) (T 2 k))
    rfl
  · funext i j
    show inner (T 0 (Equiv.swap (0 : Fin 3) 2 i)) (T 1 j) =
      inner (T 0 (Equiv.swap (0 : Fin 3) 2 i)) (T 1 j)
    rfl
  · funext j k
    show inner (T 1 j) (T 2 k) = inner (T 1 j) (T 2 k)
    rfl
  · funext k i
    show inner (T 2 k) (T 0 (Equiv.swap (0 : Fin 3) 2 i)) =
      inner (T 2 k) (T 0 (Equiv.swap (0 : Fin 3) 2 i))
    rfl

theorem revLedger_revLedger (L : Ledger54) : revLedger (revLedger L) = L := by
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
  · funext i j k
    show L.1 (Equiv.swap (0 : Fin 3) 2 (Equiv.swap (0 : Fin 3) 2 i)) j k = L.1 i j k
    rw [Equiv.swap_apply_self]
  · funext i j
    show L.2.1 (Equiv.swap (0 : Fin 3) 2 (Equiv.swap (0 : Fin 3) 2 i)) j = L.2.1 i j
    rw [Equiv.swap_apply_self]
  · rfl
  · funext k i
    show L.2.2.2 k (Equiv.swap (0 : Fin 3) 2 (Equiv.swap (0 : Fin 3) 2 i)) = L.2.2.2 k i
    rw [Equiv.swap_apply_self]

theorem revLedger_inDomain {L : Ledger54} (hL : InDomain L) : InDomain (revLedger L) where
  P_row i := by
    simp only [revLedger_P]
    exact hL.P_row (Equiv.swap (0 : Fin 3) 2 i)
  P_col j := by
    simp only [revLedger_P, swap02_zero, swap02_one, swap02_two]
    linarith [hL.P_col j]
  Q_row j := by
    simp only [revLedger_Q]
    exact hL.Q_row j
  Q_col k := by
    simp only [revLedger_Q]
    exact hL.Q_col k
  R_row k := by
    simp only [revLedger_R, swap02_zero, swap02_one, swap02_two]
    linarith [hL.R_row k]
  R_col i := by
    simp only [revLedger_R]
    exact hL.R_col (Equiv.swap (0 : Fin 3) 2 i)
  C_k i j := by
    simp only [revLedger_C, revLedger_P]
    exact hL.C_k (Equiv.swap (0 : Fin 3) 2 i) j
  C_i j k := by
    simp only [revLedger_C, revLedger_Q, swap02_zero, swap02_one, swap02_two]
    linarith [hL.C_i j k]
  C_j k i := by
    simp only [revLedger_C, revLedger_R]
    exact hL.C_j k (Equiv.swap (0 : Fin 3) 2 i)

theorem revLedger_affine : AffineComb revLedger := by
  intro x y t
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
  · funext i j k
    simp only [revLedger_C, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub,
      Prod.smul_fst, Prod.smul_snd, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul] <;> ring
  · funext i j
    simp only [revLedger_P, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub,
      Prod.smul_fst, Prod.smul_snd, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul] <;> ring
  · funext j k
    simp only [revLedger_Q, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub,
      Prod.smul_fst, Prod.smul_snd, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul] <;> ring
  · funext k i
    simp only [revLedger_R, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub,
      Prod.smul_fst, Prod.smul_snd, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul] <;> ring

/-! ## The chart involution -/

/-- The reversal read on the twenty chart coordinates. -/
def tau (b : Fin 20 → ℝ) : Fin 20 → ℝ := encode20 (revLedger (decode20 b))

theorem tau_apply (b : Fin 20 → ℝ) : tau b = encode20 (revLedger (decode20 b)) := rfl

theorem tau_encode20 (L : Ledger54) (hL : InDomain L) :
    tau (encode20 L) = encode20 (revLedger L) := by
  rw [tau_apply, decode_encode L hL]

theorem tau_tau (b : Fin 20 → ℝ) : tau (tau b) = b := by
  rw [tau_apply b, tau_encode20 _ (revLedger_inDomain (decode20_inDomain b)),
    revLedger_revLedger, encode20_decode20]

theorem involutive_tau : Function.Involutive tau := tau_tau

theorem affineComb_tau : AffineComb tau :=
  AffineComb.comp (f := decode20) (g := fun L => encode20 (revLedger L))
    (AffineComb.comp (f := revLedger) (g := encode20) encode20_affine revLedger_affine)
    decode20_affine

theorem continuous_tau : Continuous tau :=
  AffineComb.continuous20 affineComb_tau

/-! ## Frames and Phi under the reversal -/

theorem frame_swap {p : Fin 3 → Albert} (hp : Frame p) :
    Frame (fun i => p (Equiv.swap (0 : Fin 3) 2 i)) where
  trace_one i := hp.trace_one (Equiv.swap (0 : Fin 3) 2 i)
  idempotent i := hp.idempotent (Equiv.swap (0 : Fin 3) 2 i)
  orthogonal i j hij :=
    hp.orthogonal (Equiv.swap (0 : Fin 3) 2 i) (Equiv.swap (0 : Fin 3) 2 j)
      ((Equiv.swap (0 : Fin 3) 2).injective.ne hij)
  sum_unit := by
    show p (Equiv.swap (0 : Fin 3) 2 0) + p (Equiv.swap (0 : Fin 3) 2 1) +
      p (Equiv.swap (0 : Fin 3) 2 2) = 1
    rw [swap02_zero, swap02_one, swap02_two, ← hp.sum_unit]
    abel

theorem frame_revTriple (T : Triple) (hT : ∀ a : Fin 3, Frame (T a)) (a : Fin 3) :
    Frame (revTriple T a) := by
  rcases fin3_cases a with rfl | rfl | rfl
  · rw [revTriple_zero]
    exact frame_swap (hT 0)
  · rw [revTriple_one]
    exact hT 1
  · rw [revTriple_two]
    exact hT 2

/-- Phi of a triple, read off its three encoders. -/
def phiOf (T : Triple) : ℝ := phi (encoder (T 0)) (encoder (T 1)) (encoder (T 2))

theorem phiOf_apply (T : Triple) :
    phiOf T = phi (encoder (T 0)) (encoder (T 1)) (encoder (T 2)) := rfl

theorem encoder_revTriple_zero (T : Triple) :
    encoder (revTriple T 0) = -encoder (T 0) := by
  show T 0 (Equiv.swap (0 : Fin 3) 2 2) - T 0 (Equiv.swap (0 : Fin 3) 2 0) = -(T 0 2 - T 0 0)
  rw [swap02_two, swap02_zero]
  abel

theorem phiOf_revTriple (T : Triple) : phiOf (revTriple T) = -phiOf T := by
  have h0 : encoder (revTriple T 0) = (-1 : ℝ) • encoder (T 0) := by
    rw [encoder_revTriple_zero, neg_one_smul]
  have h1 : encoder (revTriple T 1) = encoder (T 1) := by rw [revTriple_one]
  have h2 : encoder (revTriple T 2) = encoder (T 2) := by rw [revTriple_two]
  simp only [phiOf_apply]
  rw [h0, h1, h2, phi_smul_first]
  ring

/-- The shape `RobustBranchReversal.reversalSection_negative` (:52) takes, at
`phi := fun T => -phiOf T`: instantiating it there turns the reversed section's sign POSITIVE. -/
theorem negPhiOf_revTriple (T : Triple) :
    (fun X : Triple => -phiOf X) (revTriple T) = -((fun X : Triple => -phiOf X) T) := by
  show -phiOf (revTriple T) = -(-phiOf T)
  rw [phiOf_revTriple]

/-! ## Continuity of Phi -/

theorem continuous_U : Continuous fun p : Albert × Albert => U p.1 p.2 := by
  have h12 : Continuous fun p : Albert × Albert => jordan p.1 p.2 := continuous_jordan
  have hp11 : Continuous fun p : Albert × Albert => (p.1, p.1) :=
    continuous_fst.prodMk continuous_fst
  have h11 : Continuous fun p : Albert × Albert => jordan p.1 p.1 := by
    simpa only [Function.comp_def] using continuous_jordan.comp hp11
  have hp1 : Continuous fun p : Albert × Albert => (p.1, jordan p.1 p.2) :=
    continuous_fst.prodMk h12
  have h1 : Continuous fun p : Albert × Albert => jordan p.1 (jordan p.1 p.2) :=
    by simpa only [Function.comp_def] using continuous_jordan.comp hp1
  have hp2 : Continuous fun p : Albert × Albert => (jordan p.1 p.1, p.2) :=
    h11.prodMk continuous_snd
  have h2 : Continuous fun p : Albert × Albert => jordan (jordan p.1 p.1) p.2 := by
    simpa only [Function.comp_def] using continuous_jordan.comp hp2
  have hU : (fun p : Albert × Albert => U p.1 p.2) =
      fun p : Albert × Albert =>
        jordan p.1 (jordan p.1 p.2) + jordan p.1 (jordan p.1 p.2) -
          jordan (jordan p.1 p.1) p.2 := by
    funext p
    simp only [U, two_smul]
  rw [hU]
  exact (h1.add h1).sub h2

theorem continuous_phi3 :
    Continuous fun p : Albert × Albert × Albert => phi p.1 p.2.1 p.2.2 := by
  have cx : Continuous fun p : Albert × Albert × Albert => p.1 := continuous_fst
  have cy : Continuous fun p : Albert × Albert × Albert => p.2.1 :=
    continuous_fst.comp continuous_snd
  have cz : Continuous fun p : Albert × Albert × Albert => p.2.2 :=
    continuous_snd.comp continuous_snd
  have hpyz : Continuous fun p : Albert × Albert × Albert => (p.2.1, p.2.2) :=
    cy.prodMk cz
  have hyz : Continuous fun p : Albert × Albert × Albert => U p.2.1 p.2.2 := by
    simpa only [Function.comp_def] using continuous_U.comp hpyz
  have hpxz : Continuous fun p : Albert × Albert × Albert => (p.1, p.2.2) :=
    cx.prodMk cz
  have hxz : Continuous fun p : Albert × Albert × Albert => U p.1 p.2.2 := by
    simpa only [Function.comp_def] using continuous_U.comp hpxz
  have hpA : Continuous fun p : Albert × Albert × Albert => (p.1, U p.2.1 p.2.2) :=
    cx.prodMk hyz
  have hA : Continuous fun p : Albert × Albert × Albert => U p.1 (U p.2.1 p.2.2) := by
    simpa only [Function.comp_def] using continuous_U.comp hpA
  have hpB : Continuous fun p : Albert × Albert × Albert => (p.2.1, U p.1 p.2.2) :=
    cy.prodMk hxz
  have hB : Continuous fun p : Albert × Albert × Albert => U p.2.1 (U p.1 p.2.2) := by
    simpa only [Function.comp_def] using continuous_U.comp hpB
  have hpJ : Continuous fun p : Albert × Albert × Albert => (p.1, p.2.1) :=
    cx.prodMk cy
  have hJ : Continuous fun p : Albert × Albert × Albert => jordan p.1 p.2.1 := by
    simpa only [Function.comp_def] using continuous_jordan.comp hpJ
  have hpC : Continuous fun p : Albert × Albert × Albert => (p.2.2, jordan p.1 p.2.1) :=
    cz.prodMk hJ
  have hC : Continuous fun p : Albert × Albert × Albert => U p.2.2 (jordan p.1 p.2.1) := by
    simpa only [Function.comp_def] using continuous_U.comp hpC
  have hphi : (fun p : Albert × Albert × Albert => phi p.1 p.2.1 p.2.2) =
      fun p : Albert × Albert × Albert =>
        inner (U p.1 (U p.2.1 p.2.2) - U p.2.1 (U p.1 p.2.2))
          (U p.2.2 (jordan p.1 p.2.1)) := by
    funext p
    simp only [phi]
  rw [hphi]
  have hpPhi : Continuous fun p : Albert × Albert × Albert =>
      (U p.1 (U p.2.1 p.2.2) - U p.2.1 (U p.1 p.2.2),
        U p.2.2 (jordan p.1 p.2.1)) := (hA.sub hB).prodMk hC
  simpa only [Function.comp_def] using continuous_native_inner.comp hpPhi

theorem continuous_encoder_slot (a : Fin 3) :
    Continuous fun T : Triple => encoder (T a) := by
  have h2 : Continuous fun T : Triple => T a 2 :=
    continuous_apply_apply (ρ := fun (_ _ : Fin 3) => Albert) a (2 : Fin 3)
  have h0 : Continuous fun T : Triple => T a 0 :=
    continuous_apply_apply (ρ := fun (_ _ : Fin 3) => Albert) a (0 : Fin 3)
  change Continuous fun T : Triple => T a 2 - T a 0
  exact h2.sub h0

theorem continuous_phiOf : Continuous phiOf := by
  have hp : Continuous fun T : Triple =>
      (encoder (T 0), encoder (T 1), encoder (T 2)) :=
    (continuous_encoder_slot 0).prodMk
      ((continuous_encoder_slot 1).prodMk (continuous_encoder_slot 2))
  change Continuous fun T : Triple => phi (encoder (T 0)) (encoder (T 1)) (encoder (T 2))
  simpa only [Function.comp_def] using continuous_phi3.comp hp

theorem continuous_negPhiOf : Continuous fun T : Triple => -phiOf T :=
  continuous_phiOf.neg

theorem continuous_revTriple : Continuous fun T : Triple => revTriple T := by
  refine continuous_pi fun a => continuous_pi fun i => ?_
  rcases fin3_cases a with rfl | rfl | rfl
  · exact (continuous_apply (Equiv.swap (0 : Fin 3) 2 i)).comp (continuous_apply (0 : Fin 3))
  · exact (continuous_apply i).comp (continuous_apply (1 : Fin 3))
  · exact (continuous_apply i).comp (continuous_apply (2 : Fin 3))

end
end Glennie.Compact.Sections
