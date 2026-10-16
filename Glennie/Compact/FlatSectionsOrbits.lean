/- The analytic and algebraic descriptions of the flat-base fibre.

`Glennie.Compact.NativeFlatSections.native_flat_two_sections_full54` gives two continuous
sections over an open neighbourhood V of the flat base's encoded ledger. Both invert the
full 54-entry ledger, with Phi > 0 and Phi < 0 respectively. This construction uses the
rank-20 Jacobian bridge.

`Glennie.Compact.FlatOrbit` identifies the flat-base fibre with two disjoint
compact-automorphism orbits, each exactly one sign sheet of Phi. The fibre is the
level set |Phi| = 4/27; this classification is bridge-free.

At the flat base, the analytic section values represent the two algebraic orbit
components and together represent the entire fibre. The sign and orbit labels agree.
`Sections.flatBase` and `FrameTopology.flatBaseTriple` are definitionally equal;
the first-frame and third-frame reversals have equal orbits by `FlatOrbit`.

No novelty is claimed. The two-orbit statement concerns ORDERED triples. `FlatOrbit`
also proves that the fibre is one class modulo the 1296 outcome relabellings:
`encoder p = p 2 - p 0` sees only outcomes 0 and 2, so Phi is not a relabelling invariant
even up to sign.

The orbit identification here is restricted to the flat base. The sections are local
in the ledger, but this module asserts no nearby orbit classification, stabilizer,
orbit dimension, or number of automorphisms realizing a given fibre element. -/
module

public import Glennie.Compact.NativeFlatSections
public import Glennie.Compact.FlatOrbit

@[expose] public section

namespace Glennie.Compact.FlatSectionsOrbits

open Glennie Glennie.Compact.FlatBase Glennie.Compact.Affine20
open Glennie.Compact.FrameTopology Glennie.Compact.FlatOrbit
open Glennie.Compact.Sections

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-! ## 1. The two flat base triples are one triple

`Glennie.Compact.Sections.flatBase` and
`Glennie.Compact.FrameTopology.flatBaseTriple` are both
`![flatFrameP, flatFrameQ, flatFrameR]` over the same `FlatBase` frames.
They are definitionally equal. This identity connects the analytic statement over
the first representative to the algebraic statement over the second. -/

/-- The sections' base triple and the classification's base triple are equal. -/
theorem flatBase_eq_flatBaseTriple :
    Glennie.Compact.Sections.flatBase = flatBaseTriple := rfl

/-- Hence their ledgers agree. -/
theorem ledger54_flatBase_eq :
    ledger54 Glennie.Compact.Sections.flatBase = ledger54 flatBaseTriple := by
  rw [flatBase_eq_flatBaseTriple]

/-! ## 2. A section value at the base point lands in the fibre

The sections invert the ledger map through the 20-parameter chart, so at the base
point they return a triple whose ledger is `decode20 (encode20 (ledger54 flatBase))`.
The chart inverts on the ledger of any triple of genuine frames
(`Glennie.Compact.Affine20.decode_encode_frames`, `Affine20/Chart.lean`), so that
is the flat ledger itself, on all 54 entries and not merely on the 20 chart
coordinates. That last point is what makes the membership real rather than a
coincidence of the chart. -/

/-- The chart round trip at the flat base, written out. -/
theorem decode_encode_flatBase :
    decode20 (encode20 (ledger54 Glennie.Compact.Sections.flatBase)) =
      ledger54 flatBaseTriple := by
  rw [decode_encode_frames Glennie.Compact.Sections.flatBase
        Glennie.Compact.Sections.flatBase_frames, ledger54_flatBase_eq]

/-- Any frame triple whose ledger is the decoded base chart point is in the fibre. -/
theorem mem_flatFibre_of_ledger_eq {T : Triple}
    (hT : ∀ a : Fin 3, Glennie.Frame (T a))
    (hL : ledger54 T =
      decode20 (encode20 (ledger54 Glennie.Compact.Sections.flatBase))) :
    T ∈ flatFibre := by
  refine ⟨hT, ?_⟩
  rw [hL, decode_encode_flatBase]

/-! ## 3. The sign of Phi picks the sheet

`FlatOrbit.flat_fibre_eq_abs_phi` says a fibre member has `|Phi| = 4/27`, and
`autOrbit_flatBase_eq` / `autOrbit_flatBaseRev3_eq` say each orbit is exactly one
signed sheet. So on the fibre the SIGN of Phi decides the orbit outright. -/

/-- A fibre member with negative Phi is in the first orbit. -/
theorem mem_autOrbit_flatBase_of_phi_neg {T : Triple}
    (hmem : T ∈ flatFibre) (hp : Glennie.Compact.Sections.phiOf T < 0) :
    T ∈ autOrbit flatBaseTriple := by
  have habs : |Glennie.phi (Glennie.encoder (T 0)) (Glennie.encoder (T 1))
      (Glennie.encoder (T 2))| = 4 / 27 := by
    rw [flat_fibre_eq_abs_phi] at hmem
    exact hmem.2
  have hlt : Glennie.phi (Glennie.encoder (T 0)) (Glennie.encoder (T 1))
      (Glennie.encoder (T 2)) < 0 := by
    rw [Glennie.Compact.Sections.phiOf_apply] at hp
    exact hp
  rw [autOrbit_flatBase_eq]
  refine ⟨hmem, ?_⟩
  rw [abs_of_neg hlt] at habs
  linarith

/-- A fibre member with positive Phi is in the second orbit. -/
theorem mem_autOrbit_flatBaseRev3_of_phi_pos {T : Triple}
    (hmem : T ∈ flatFibre) (hp : 0 < Glennie.Compact.Sections.phiOf T) :
    T ∈ autOrbit flatBaseRev3 := by
  have habs : |Glennie.phi (Glennie.encoder (T 0)) (Glennie.encoder (T 1))
      (Glennie.encoder (T 2))| = 4 / 27 := by
    rw [flat_fibre_eq_abs_phi] at hmem
    exact hmem.2
  have hgt : 0 < Glennie.phi (Glennie.encoder (T 0)) (Glennie.encoder (T 1))
      (Glennie.encoder (T 2)) := by
    rw [Glennie.Compact.Sections.phiOf_apply] at hp
    exact hp
  rw [autOrbit_flatBaseRev3_eq]
  refine ⟨hmem, ?_⟩
  rw [abs_of_pos hgt] at habs
  linarith

/-! ## 4. The capstone

The two sections, evaluated at the flat base point, represent the two orbits,
and the whole fibre is their union. The first conjuncts give
`native_flat_two_sections_full54`; the final six identify the section values
with the orbit representatives. -/

/-- THE JOIN. The two analytic branches at the flat base ARE the two algebraic orbit
components of the flat-base fibre: each section value lies in one orbit, generates
that orbit, the two orbits are disjoint, and their union is the entire 54-entry
fibre. -/
theorem flat_sections_are_the_two_orbits :
    ∃ V : Set (Fin 20 → ℝ), IsOpen V ∧
      encode20 (ledger54 Glennie.Compact.Sections.flatBase) ∈ V ∧
      ∃ secPos secNeg : (Fin 20 → ℝ) → Triple,
        ContinuousOn secPos V ∧ ContinuousOn secNeg V ∧
        (∀ b ∈ V, ∀ a : Fin 3, Glennie.Frame (secPos b a)) ∧
        (∀ b ∈ V, ∀ a : Fin 3, Glennie.Frame (secNeg b a)) ∧
        (∀ b ∈ V, encode20 (ledger54 (secPos b)) = b) ∧
        (∀ b ∈ V, encode20 (ledger54 (secNeg b)) = b) ∧
        (∀ b ∈ V, ledger54 (secPos b) = decode20 b) ∧
        (∀ b ∈ V, ledger54 (secNeg b) = decode20 b) ∧
        (∀ b ∈ V, 0 < Glennie.Compact.Sections.phiOf (secPos b)) ∧
        (∀ b ∈ V, Glennie.Compact.Sections.phiOf (secNeg b) < 0) ∧
        secNeg (encode20 (ledger54 Glennie.Compact.Sections.flatBase)) ∈
          autOrbit flatBaseTriple ∧
        secPos (encode20 (ledger54 Glennie.Compact.Sections.flatBase)) ∈
          autOrbit flatBaseRev3 ∧
        autOrbit (secNeg (encode20 (ledger54 Glennie.Compact.Sections.flatBase))) =
          autOrbit flatBaseTriple ∧
        autOrbit (secPos (encode20 (ledger54 Glennie.Compact.Sections.flatBase))) =
          autOrbit flatBaseRev3 ∧
        flatFibre =
          autOrbit (secNeg (encode20 (ledger54 Glennie.Compact.Sections.flatBase))) ∪
            autOrbit (secPos (encode20 (ledger54 Glennie.Compact.Sections.flatBase))) ∧
        Disjoint
          (autOrbit (secNeg (encode20 (ledger54 Glennie.Compact.Sections.flatBase))))
          (autOrbit (secPos (encode20 (ledger54 Glennie.Compact.Sections.flatBase)))) := by
  obtain ⟨V, hV, hbase, secPos, secNeg, hcP, hcN, hfP, hfN, heP, heN, hlP, hlN,
    hpP, hpN⟩ := Glennie.Compact.NativeFlatSections.native_flat_two_sections_full54
  have hNmem :
      secNeg (encode20 (ledger54 Glennie.Compact.Sections.flatBase)) ∈ flatFibre :=
    mem_flatFibre_of_ledger_eq (hfN _ hbase) (hlN _ hbase)
  have hPmem :
      secPos (encode20 (ledger54 Glennie.Compact.Sections.flatBase)) ∈ flatFibre :=
    mem_flatFibre_of_ledger_eq (hfP _ hbase) (hlP _ hbase)
  have hNorb := mem_autOrbit_flatBase_of_phi_neg hNmem (hpN _ hbase)
  have hPorb := mem_autOrbit_flatBaseRev3_of_phi_pos hPmem (hpP _ hbase)
  have hNeq := autOrbit_eq_of_mem hNorb
  have hPeq := autOrbit_eq_of_mem hPorb
  refine ⟨V, hV, hbase, secPos, secNeg, hcP, hcN, hfP, hfN, heP, heN, hlP, hlN,
    hpP, hpN, hNorb, hPorb, hNeq, hPeq, ?_, ?_⟩
  · rw [hNeq, hPeq]
    exact flat_fibre_eq_two_orbits
  · rw [hNeq, hPeq]
    exact flat_orbits_disjoint

/-! ## 5. The same statement with the sections' own reversal

The sections are built on the FIRST-frame reversal `flatBaseRevP`, while the
classification is stated with the THIRD-frame reversal `flatBaseRev3`. They are
different triples in the same orbit, which `FlatOrbit` records as
`autOrbit_flatBaseRevP_eq_autOrbit_flatBaseRev3`. So the capstone can be read with
either representative, and this corollary says so explicitly rather than leaving a
reader to wonder whether the two halves are talking about the same component. -/

/-- The second orbit may equally be named by the sections' own first-frame reversal. -/
theorem flat_fibre_eq_two_orbits_revP :
    flatFibre = autOrbit flatBaseTriple ∪ autOrbit flatBaseRevP := by
  rw [autOrbit_flatBaseRevP_eq_autOrbit_flatBaseRev3]
  exact flat_fibre_eq_two_orbits

/-! ## 6. The sections' own reversal

`flatBaseRevP` is the first-frame reversal defined in `FlatOrbit`; the sections use
`Glennie.Compact.Sections.revTriple`. Their identification follows from
`flatFramePRev_eq_reverse`, which turns the reversed first frame into
`reverseFrame flatFrameP`, and `reverseFrame_eq_swap`, which identifies `reverseFrame`
with precomposition by (0 2). This is exactly the action of `revTriple` on slot 0,
leaving slots 1 and 2 unchanged. -/

/-- The reversed first frame is precomposition of the first frame with the
transposition (0 2). Two rewrites of closed terms let the triple-level proof
avoid case analysis on explicit `Albert` terms. -/
theorem flatFramePRev_eq_swap_flatFrameP :
    flatFramePRev = fun i => flatFrameP (Equiv.swap (0 : Fin 3) 2 i) := by
  rw [flatFramePRev_eq_reverse, reverseFrame_eq_swap]

/-- The classification's first-frame reversal IS the sections' `revTriple` of the flat
base. Both sides are ordered triples and nothing is quotiented. Slots 1 and 2 agree
definitionally, so a single rewrite in slot 0 closes it. -/
theorem flatBaseRevP_eq_revTriple_flatBase :
    flatBaseRevP = revTriple Glennie.Compact.Sections.flatBase := by
  show (![flatFramePRev, flatFrameQ, flatFrameR] : Triple)
      = ![fun i => flatFrameP (Equiv.swap (0 : Fin 3) 2 i), flatFrameQ, flatFrameR]
  rw [flatFramePRev_eq_swap_flatFrameP]

/-- The fibre decomposition using the sections' own reversal. This statement
still uses `flatBaseTriple`; the next uses only the sections' representative triples. -/
theorem flat_fibre_eq_two_orbits_revTriple :
    flatFibre = autOrbit flatBaseTriple ∪
      autOrbit (revTriple Glennie.Compact.Sections.flatBase) := by
  rw [← flatBaseRevP_eq_revTriple_flatBase]
  exact flat_fibre_eq_two_orbits_revP

/-- The decomposition with the sections' representative triples: `Sections.flatBase`
and its `revTriple`. The definitions `flatFibre` and `autOrbit` still come from
`FlatOrbit`. The identity `flatBase_eq_flatBaseTriple` is `rfl`, so this is the
preceding proposition with definitionally equal representatives. -/
theorem flat_fibre_eq_two_orbits_sections :
    flatFibre = autOrbit Glennie.Compact.Sections.flatBase ∪
      autOrbit (revTriple Glennie.Compact.Sections.flatBase) :=
  flat_fibre_eq_two_orbits_revTriple

end
end Glennie.Compact.FlatSectionsOrbits
