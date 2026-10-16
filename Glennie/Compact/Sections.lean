/- Continuous local sections of the ledger map.

The inverse function theorem is applied to `cRow (ledger54 (movedTriple T s))`,
which is `FlowFamily.rowLedger T s` (`ChartTransfer.cRow_ledger54_movedTriple`).
The result is transported to the `encode20` chart by `rowsOf`, `chartVec`, and
`chartVec_rowsOf`. The certified Jacobian `FlowFamily.jacobianEntry`
(FlowFamily.lean) and `Rank20Certificate.det_JQ_ne_zero`
(Rank20Certificate.lean) concern the twenty selected C cells.
The two-section assembly uses `Glennie.Theorems.RobustBranchReversal`;
`reversalSection_negative` (:52) at `phi := fun T => -phiOf T` gives the positive sign.

WHAT THIS MODULE PROVES.
  * `hasStrictFDerivAt_cRow_ledger54_movedTriple`: the strict derivative, restated for
    the composite ledger map.
  * `exists_section_of_equiv`: the inverse function theorem on those twenty coordinates. INPUT:
    an invertibility witness for the derivative, in the form supplied by
    (`Rank20.rank20_of_bridge`, Rank20Reduction.lean), as an explicit hypothesis, assumed
    nowhere. OUTPUT: an open neighbourhood of the chart point of T in the bare space
    `Fin 20 -> R`, and a continuous section of frame triples with
    `encode20 (ledger54 (sec b)) = b`.
  * `exists_signed_section_of_equiv`: the neighbourhood shrunk so that Phi stays strictly
    negative.
  * `flat_two_sections`: at the flat base, ONE invertibility witness gives BOTH sections. The
    second is `RobustBranchReversal.reversalSection revTriple tau sec`; the chart involution
    `tau` fixes the flat chart point because the reversed flat triple has the identical 54
    entries (FlatBase `flat_uniform` :272, `flatRev_uniform` :276, `uniform_pair_blocks` :281).
  * `flat_two_sections_of_bridge`: the same conclusion from the entrywise bridge
    `jacobianEntry flatBase r n = JQ r n`.

`flatBase` is `![flatFrameP, flatFrameQ, flatFrameR]` in slot order.
The relabelling gate is `Affine20.relabel_gates` (Affine20.lean) and
`dense_avoids` (:343); this module proves neither relabel avoidance nor inequivalence.

Code guidance. The inverse function theorem's `OpenPartialHomeomorph` carries two
`Classical.choose` terms (FDeriv.lean-123). `exists_section_of_equiv` first
generalizes it to a variable `Psi` with the three needed facts. `InDomain`
obligations use named lemmas, and ledger component equalities use `show X = X`
and per-component rewrites (see Sections/Reversal.lean).
-/
module

public import Glennie.Compact.Sections.Reversal
public import Glennie.Compact.Rank20Reduction
public import Glennie.Compact.FlatBase
public import Glennie.Theorems.RobustBranchReversal
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
public import Mathlib.Topology.ContinuousOn
public import Mathlib.Topology.OpenPartialHomeomorph.Defs
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Order.OrderClosed
public import Mathlib.Tactic.NormNum

@[expose] public section

namespace Glennie.Compact.Sections

open Glennie.Compact.Affine20 Glennie.Compact.NativeDictionary Glennie.Compact.FlowFamily
  Glennie.Compact.ChartTransfer Glennie.Compact.FlatBase Glennie.Compact.Rank20
  Glennie.Compact.Rank20Certificate Glennie.RobustBranchCore

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## Continuity of the moved atoms -/

/-- The coordinate decoding as a continuous linear map. -/
def decodeCLM : (Fin 27 → ℝ) →L[ℝ] Albert :=
  LinearMap.toContinuousLinearMap extEquiv.toLinearMap

theorem decodeCLM_apply (c : Fin 27 → ℝ) : decodeCLM c = extEquiv c := rfl

/-- Every atom of the moved triple depends continuously on the twenty flow parameters. -/
theorem continuous_movedTriple_atom (T : Triple) (a i : Fin 3) :
    Continuous fun s : Fin 20 → ℝ => movedTriple T s a i := by
  have h : Continuous fun s : Fin 20 → ℝ =>
      extEquiv.symm (movedFrame contextDirection contextDirection_isJordanDerivation
        contextDirection_traceFree T a s i) :=
    continuous_movedFrame_coord contextDirection contextDirection_isJordanDerivation
      contextDirection_traceFree T a i
  have h2 : Continuous fun s : Fin 20 → ℝ =>
      decodeCLM (extEquiv.symm (movedFrame contextDirection
        contextDirection_isJordanDerivation contextDirection_traceFree T a s i)) :=
    decodeCLM.continuous.comp h
  simp only [decodeCLM_apply, LinearEquiv.apply_symm_apply] at h2
  show Continuous fun s : Fin 20 → ℝ =>
    movedFrame contextDirection contextDirection_isJordanDerivation
      contextDirection_traceFree T a s i
  exact h2

/-! ## The inverse function theorem on `cRow (ledger54 (movedTriple T s))` -/

/-- The strict derivative of `FlowFamily.rowLedger` (FlowFamily.lean), restated for
the composite C-row ledger map. -/
theorem hasStrictFDerivAt_cRow_ledger54_movedTriple (T : Triple)
    (e : (Fin 20 → ℝ) ≃L[ℝ] (Fin 20 → ℝ))
    (he : (e : (Fin 20 → ℝ) →L[ℝ] (Fin 20 → ℝ)) = rowLedgerDeriv T) :
    HasStrictFDerivAt (fun s : Fin 20 → ℝ => cRow (ledger54 (movedTriple T s)))
      (e : (Fin 20 → ℝ) →L[ℝ] (Fin 20 → ℝ)) 0 := by
  have hfun : (fun s : Fin 20 → ℝ => cRow (ledger54 (movedTriple T s))) = rowLedger T :=
    funext fun s => cRow_ledger54_movedTriple T s
  rw [hfun]
  exact hasStrictFDerivAt_rowLedger_of_equiv T e he

/-- The chart point of T is recovered from the twenty rows at the base point of the family. -/
theorem rowsOf_chart_base (T : Triple) (hT : ∀ a : Fin 3, Frame (T a)) :
    rowsOf (encode20 (ledger54 T)) = rowLedger T 0 := by
  have h := rowsOf_encode20_movedTriple T hT 0
  rw [movedTriple_zero] at h
  exact h

/-- The local section of the ledger map, indexed by chart coordinates.
The invertibility of the strict derivative is an explicit hypothesis, in exactly the
form `Rank20.rank20_of_bridge` (Rank20Reduction.lean) delivers it; nothing about rank or
determinants is assumed here. -/
theorem exists_section_of_equiv (T : Triple) (hT : ∀ a : Fin 3, Frame (T a))
    (e : (Fin 20 → ℝ) ≃L[ℝ] (Fin 20 → ℝ))
    (he : (e : (Fin 20 → ℝ) →L[ℝ] (Fin 20 → ℝ)) = rowLedgerDeriv T) :
    ∃ W : Set (Fin 20 → ℝ), IsOpen W ∧ encode20 (ledger54 T) ∈ W ∧
      ∃ sec : (Fin 20 → ℝ) → Triple,
        ContinuousOn sec W ∧
        sec (encode20 (ledger54 T)) = T ∧
        (∀ b ∈ W, ∀ a : Fin 3, Frame (sec b a)) ∧
        (∀ b ∈ W, encode20 (ledger54 (sec b)) = b) := by
  have hd : HasStrictFDerivAt (rowLedger T) (e : (Fin 20 → ℝ) →L[ℝ] (Fin 20 → ℝ)) 0 :=
    hasStrictFDerivAt_rowLedger_of_equiv T e he
  -- Generalize the inverse-function-theorem term containing `Classical.choose` before using it.
  obtain ⟨Psi, hcoe, hsrc, htgt⟩ :
      ∃ Psi : OpenPartialHomeomorph (Fin 20 → ℝ) (Fin 20 → ℝ),
        (Psi : (Fin 20 → ℝ) → (Fin 20 → ℝ)) = rowLedger T ∧
          (0 : Fin 20 → ℝ) ∈ Psi.source ∧ rowLedger T 0 ∈ Psi.target :=
    ⟨hd.toOpenPartialHomeomorph (rowLedger T), hd.toOpenPartialHomeomorph_coe,
      hd.mem_toOpenPartialHomeomorph_source, hd.image_mem_toOpenPartialHomeomorph_target⟩
  have hb0 : rowsOf (encode20 (ledger54 T)) = rowLedger T 0 := rowsOf_chart_base T hT
  have hleft : Psi.symm (rowLedger T 0) = 0 := by
    have h := Psi.left_inv hsrc
    rw [hcoe] at h
    exact h
  have hright : ∀ b : Fin 20 → ℝ, b ∈ Psi.target → rowLedger T (Psi.symm b) = b := by
    intro b hb
    have h := Psi.right_inv hb
    rw [hcoe] at h
    exact h
  have hsigma : ContinuousOn (fun b : Fin 20 → ℝ => Psi.symm (rowsOf b))
      (rowsOf ⁻¹' Psi.target) :=
    Psi.continuousOn_symm.comp' continuous_rowsOf.continuousOn (fun b hb => hb)
  refine ⟨rowsOf ⁻¹' Psi.target, Psi.open_target.preimage continuous_rowsOf, ?_,
    fun b => movedTriple T (Psi.symm (rowsOf b)), ?_, ?_, ?_, ?_⟩
  · show rowsOf (encode20 (ledger54 T)) ∈ Psi.target
    rw [hb0]
    exact htgt
  · refine continuousOn_pi' fun a => continuousOn_pi' fun i => ?_
    exact (continuous_movedTriple_atom T a i).comp_continuousOn' hsigma
  · show movedTriple T (Psi.symm (rowsOf (encode20 (ledger54 T)))) = T
    rw [hb0, hleft, movedTriple_zero]
  · intro b _ a
    exact movedTriple_frame T hT (Psi.symm (rowsOf b)) a
  · intro b hb
    show encode20 (ledger54 (movedTriple T (Psi.symm (rowsOf b)))) = b
    rw [encode20_movedTriple_eq_chartVec T hT, hright (rowsOf b) hb, chartVec_rowsOf]

/-- The same section, on a neighbourhood shrunk so that Phi stays strictly negative. -/
theorem exists_signed_section_of_equiv (T : Triple) (hT : ∀ a : Fin 3, Frame (T a))
    (e : (Fin 20 → ℝ) ≃L[ℝ] (Fin 20 → ℝ))
    (he : (e : (Fin 20 → ℝ) →L[ℝ] (Fin 20 → ℝ)) = rowLedgerDeriv T)
    (hneg : phiOf T < 0) :
    ∃ W : Set (Fin 20 → ℝ), IsOpen W ∧ encode20 (ledger54 T) ∈ W ∧
      ∃ sec : (Fin 20 → ℝ) → Triple,
        ContinuousOn sec W ∧
        (∀ b ∈ W, ∀ a : Fin 3, Frame (sec b a)) ∧
        (∀ b ∈ W, encode20 (ledger54 (sec b)) = b) ∧
        (∀ b ∈ W, phiOf (sec b) < 0) := by
  obtain ⟨W, hWopen, hmem, sec, hcont, hbase, hframes, hledger⟩ :=
    exists_section_of_equiv T hT e he
  have hphi : ContinuousOn (fun b : Fin 20 → ℝ => phiOf (sec b)) W :=
    continuous_phiOf.comp_continuousOn' hcont
  refine ⟨W ∩ (fun b : Fin 20 → ℝ => phiOf (sec b)) ⁻¹' Set.Iio 0,
    hphi.isOpen_inter_preimage hWopen isOpen_Iio, ⟨hmem, ?_⟩, sec,
    hcont.mono Set.inter_subset_left, ?_, ?_, ?_⟩
  · show phiOf (sec (encode20 (ledger54 T))) ∈ Set.Iio (0 : ℝ)
    rw [hbase]
    exact hneg
  · intro b hb a
    exact hframes b hb.1 a
  · intro b hb
    exact hledger b hb.1
  · intro b hb
    exact hb.2

/-! ## The flat base -/

/-- The flat base triple of FlatBase, in slot order. -/
def flatBase : Triple := ![flatFrameP, flatFrameQ, flatFrameR]

theorem flatBase_zero : flatBase 0 = flatFrameP := rfl

theorem flatBase_one : flatBase 1 = flatFrameQ := rfl

theorem flatBase_two : flatBase 2 = flatFrameR := rfl

theorem flatBase_frames : ∀ a : Fin 3, Frame (flatBase a) := by
  intro a
  rcases fin3_cases a with rfl | rfl | rfl
  · rw [flatBase_zero]
    exact flatFrameP_frame
  · rw [flatBase_one]
    exact flatFrameQ_frame
  · rw [flatBase_two]
    exact flatFrameR_frame

theorem phiOf_flatBase : phiOf flatBase = -4 / 27 := by
  rw [phiOf_apply, flatBase_zero, flatBase_one, flatBase_two]
  exact flat_phi

/-- `FlatBase.reverseFrame` (FlatBase.lean) is the transposition (0 2) of the index. -/
theorem reverseFrame_eq_swap (p : Fin 3 → Albert) :
    reverseFrame p = fun i => p (Equiv.swap (0 : Fin 3) 2 i) := by
  funext i
  rcases fin3_cases i with rfl | rfl | rfl
  · show p 2 = p (Equiv.swap (0 : Fin 3) 2 0)
    rw [swap02_zero]
  · show p 1 = p (Equiv.swap (0 : Fin 3) 2 1)
    rw [swap02_one]
  · show p 0 = p (Equiv.swap (0 : Fin 3) 2 2)
    rw [swap02_two]

theorem revTriple_flatBase_zero : revTriple flatBase 0 = flatFramePRev := by
  have h : revTriple flatBase 0 = fun i => flatFrameP (Equiv.swap (0 : Fin 3) 2 i) := by
    rw [revTriple_zero, flatBase_zero]
  rw [h, flatFramePRev_eq_reverse, reverseFrame_eq_swap]

/-- The reversed flat triple has the SAME complete 54-entry ledger as the flat triple: all 27
triple traces 1/9 and all 27 pair overlaps 1/3. This is why one invertibility witness suffices
for both sections. -/
theorem ledger54_revTriple_flatBase :
    ledger54 (revTriple flatBase) = ledger54 flatBase := by
  have hpRev : ∀ i j : Fin 3, inner (flatFramePRev i) (flatFrameQ j) = 1 / 3 := fun i j =>
    (uniform_pair_blocks flatFramePRev flatFrameQ flatFrameR flatFramePRev_frame
      flatFrameQ_frame flatFrameR_frame flatRev_uniform i j).1
  have hpBase : ∀ i j : Fin 3, inner (flatFrameP i) (flatFrameQ j) = 1 / 3 := fun i j =>
    (uniform_pair_blocks flatFrameP flatFrameQ flatFrameR flatFrameP_frame
      flatFrameQ_frame flatFrameR_frame flat_uniform i j).1
  have hrRev : ∀ k i : Fin 3, inner (flatFrameR k) (flatFramePRev i) = 1 / 3 := fun k i =>
    (uniform_pair_blocks flatFramePRev flatFrameQ flatFrameR flatFramePRev_frame
      flatFrameQ_frame flatFrameR_frame flatRev_uniform k i).2.2
  have hrBase : ∀ k i : Fin 3, inner (flatFrameR k) (flatFrameP i) = 1 / 3 := fun k i =>
    (uniform_pair_blocks flatFrameP flatFrameQ flatFrameR flatFrameP_frame
      flatFrameQ_frame flatFrameR_frame flat_uniform k i).2.2
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
  · funext i j k
    show ledger (revTriple flatBase 0) (revTriple flatBase 1) (revTriple flatBase 2) i j k =
      ledger (flatBase 0) (flatBase 1) (flatBase 2) i j k
    rw [revTriple_flatBase_zero, revTriple_one, revTriple_two, flatBase_zero, flatBase_one,
      flatBase_two, flatRev_uniform i j k, flat_uniform i j k]
  · funext i j
    show inner (revTriple flatBase 0 i) (revTriple flatBase 1 j) =
      inner (flatBase 0 i) (flatBase 1 j)
    rw [revTriple_flatBase_zero, revTriple_one, flatBase_zero, flatBase_one, hpRev i j,
      hpBase i j]
  · funext j k
    show inner (revTriple flatBase 1 j) (revTriple flatBase 2 k) =
      inner (flatBase 1 j) (flatBase 2 k)
    rw [revTriple_one, revTriple_two]
  · funext k i
    show inner (revTriple flatBase 2 k) (revTriple flatBase 0 i) =
      inner (flatBase 2 k) (flatBase 0 i)
    rw [revTriple_flatBase_zero, revTriple_two, flatBase_zero, flatBase_two, hrRev k i,
      hrBase k i]

/-- Hence the chart involution fixes the flat chart point. -/
theorem tau_flatChart :
    tau (encode20 (ledger54 flatBase)) = encode20 (ledger54 flatBase) := by
  rw [tau_encode20 (ledger54 flatBase) (ledger54_inDomain flatBase flatBase_frames),
    ← ledger54_revTriple, ledger54_revTriple_flatBase]

/-! ## The headline: two opposite-sign sections from one invertibility witness

The open domain, the base point, the continuity, the frame validity and the positive sign come
from `Glennie.Theorems.RobustBranchReversal`: `reversalDomain_isOpen` (:77),
`flat_mem_reversalDomain` (:34), `reversalSection_continuousOn` (:81),
`reversalSection_valid` (:65) and `reversalSection_negative` (:52), the last instantiated at
`phi := fun T => -phiOf T` so that it delivers the POSITIVE sign.

The ledger conjunct is proved NATIVELY here and NOT by `reversalSection_ledger` (:40). That
lemma's hypothesis `hledgerReverse : forall x, ledger (reverse x) = tau (ledger x)` is
quantified over ALL of X, and at `X := Triple`, `ledger := fun T => encode20 (ledger54 T)` it is
FALSE: `tau (encode20 L) = encode20 (revLedger L)` needs `InDomain L` (Sections/Reversal.lean
`tau_encode20`, which runs through `Affine20.decode_encode`, Chart.lean), and the 54-entry
ledger of an arbitrary triple is not in the affine domain. The naturality does hold for triples
of frames, and that is exactly where it is used below, in three rewrites. See the note at the
head of Sections/Reversal.lean. -/
theorem flat_two_sections (e : (Fin 20 → ℝ) ≃L[ℝ] (Fin 20 → ℝ))
    (he : (e : (Fin 20 → ℝ) →L[ℝ] (Fin 20 → ℝ)) = rowLedgerDeriv flatBase) :
    ∃ V : Set (Fin 20 → ℝ), IsOpen V ∧ encode20 (ledger54 flatBase) ∈ V ∧
      ∃ secPos secNeg : (Fin 20 → ℝ) → Triple,
        ContinuousOn secPos V ∧ ContinuousOn secNeg V ∧
        (∀ b ∈ V, ∀ a : Fin 3, Frame (secPos b a)) ∧
        (∀ b ∈ V, ∀ a : Fin 3, Frame (secNeg b a)) ∧
        (∀ b ∈ V, encode20 (ledger54 (secPos b)) = b) ∧
        (∀ b ∈ V, encode20 (ledger54 (secNeg b)) = b) ∧
        (∀ b ∈ V, 0 < phiOf (secPos b)) ∧
        (∀ b ∈ V, phiOf (secNeg b) < 0) := by
  obtain ⟨W, hWopen, hmem, sec, hcont, hframes, hledger, hsign⟩ :=
    exists_signed_section_of_equiv flatBase flatBase_frames e he
      (by rw [phiOf_flatBase]; norm_num)
  have hpos : ∀ b ∈ W, 0 < (fun X : Triple => -phiOf X) (sec b) := by
    intro b hb
    show 0 < -phiOf (sec b)
    exact neg_pos.mpr (hsign b hb)
  refine ⟨reversalDomain tau W, reversalDomain_isOpen tau continuous_tau W hWopen,
    flat_mem_reversalDomain tau W (encode20 (ledger54 flatBase)) hmem tau_flatChart,
    reversalSection revTriple tau sec, sec,
    reversalSection_continuousOn revTriple tau continuous_revTriple continuous_tau W sec hcont,
    hcont.mono (fun b hb => hb.1), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact reversalSection_valid (fun X : Triple => ∀ a : Fin 3, Frame (X a)) revTriple tau
      (fun X hX => frame_revTriple X hX) W sec hframes
  · intro b hb
    exact hframes b hb.1
  · intro b hb
    show encode20 (ledger54 (revTriple (sec (tau b)))) = b
    rw [ledger54_revTriple,
      ← tau_encode20 (ledger54 (sec (tau b)))
        (ledger54_inDomain (sec (tau b)) (hframes (tau b) hb.2)),
      hledger (tau b) hb.2, tau_tau]
  · intro b hb
    exact hledger b hb.1
  · intro b hb
    have h := reversalSection_negative (fun X : Triple => -phiOf X) revTriple tau
      negPhiOf_revTriple W sec hpos b hb
    show 0 < phiOf (revTriple (sec (tau b)))
    exact neg_lt_zero.mp h
  · intro b hb
    exact hsign b hb.1

/-- The same conclusion from the entrywise Jacobian bridge at the flat base. -/
theorem flat_two_sections_of_bridge
    (hbridge : ∀ r n : Fin 20, jacobianEntry flatBase r n = JQ r n) :
    ∃ V : Set (Fin 20 → ℝ), IsOpen V ∧ encode20 (ledger54 flatBase) ∈ V ∧
      ∃ secPos secNeg : (Fin 20 → ℝ) → Triple,
        ContinuousOn secPos V ∧ ContinuousOn secNeg V ∧
        (∀ b ∈ V, ∀ a : Fin 3, Frame (secPos b a)) ∧
        (∀ b ∈ V, ∀ a : Fin 3, Frame (secNeg b a)) ∧
        (∀ b ∈ V, encode20 (ledger54 (secPos b)) = b) ∧
        (∀ b ∈ V, encode20 (ledger54 (secNeg b)) = b) ∧
        (∀ b ∈ V, 0 < phiOf (secPos b)) ∧
        (∀ b ∈ V, phiOf (secNeg b) < 0) := by
  obtain ⟨e, he⟩ := rank20_of_bridge flatBase hbridge
  exact flat_two_sections e he

end
end Glennie.Compact.Sections
