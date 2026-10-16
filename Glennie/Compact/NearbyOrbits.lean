/- WHAT THIS MODULE PROVES, AND UNDER WHAT.

  `nearby_fibres_two_orbits` takes TWO EXPLICIT NAMED HYPOTHESES and gives the full target:
  an open neighbourhood of the flat chart point over which every full 54-entry fibre is
  exactly the disjoint union of the two section orbits.

  The hypotheses are `LocalOrbitCompleteness flatBaseTriple` and
  `LocalOrbitCompleteness flatBaseRev3`. They are named hypotheses in the style of
  `FlatOrbit.LocalFlatRigidity` (FlatOrbit.lean) and `Rank20.rank20_of_bridge`'s `hT`
  premise (Rank20Reduction.lean). They are NOT proved here, NOT weakened, NOT axioms, and
  there is no `sorry` and no `native_decide` anywhere in this file.

WHAT IS PROVED UNCONDITIONALLY HERE, with nothing assumed.

  * Section 1. The 20-coordinate fibre and the 54-entry fibre are the same set of frame
    triples. `fibre20_subset_fibre54` holds for every chart point with no hypothesis at all;
    the reverse needs one known member, which the sections supply.
  * Section 3. `phi_bounded_away_near_flat`: there is a neighbourhood of the flat ledger
    value on which every frame triple has |Phi| > 1/27. This is a real step, not
    bookkeeping: without it a Phi = 0 member could sit in a nearby fibre, and such a member
    would lie in NEITHER orbit, so the target would be false as stated.
  * Section 4. `localOrbitCompleteness_mapAtoms`: the hypothesis is a property of the ORBIT,
    not of the point. So instantiating at the two representatives already covers every
    triple the transport in section 5 reaches.
  * Section 7. `localOrbitCompleteness_of_localSlice`: the open-mapping form of the
    dimension count implies the hypothesis. This gives an alternative sufficient condition
    for local orbit completeness.

WHY THE HYPOTHESIS IS NOT `FlatOrbit.LocalFlatRigidity`, which already exists.

  Two deliberate differences, each argued in the docstring of `LocalOrbitCompleteness`.

  (1) The Phi-EQUALITY hypothesis is DROPPED. `LocalFlatRigidity` asks for same ledger AND
      equal Phi. On the FLAT fibre |Phi| = 4/27, so there "equal Phi" and "same sign" are
      the same condition. On a NEARBY fibre, `LocalFlatRigidity` alone does not identify a sign sheet
      with one Phi level. Phi is NOT a function of the ledger
      (the flat ledger carries both -4/27 and +4/27 -- `phi_flatBase` :396 and
      `phi_flatBaseRev3` :403 over one ledger by `ledger54_flatBaseRev3` :429). From the
      Phi-equality version one gets only "each Phi level inside the fibre is one orbit",
      with no bound on the number of levels. THAT IS NOT ENOUGH FOR THE TARGET. Anyone
      deriving the target from `LocalFlatRigidity` as printed has made an error.
  (2) The statement is localised at ONE base triple. With the Phi condition dropped, any
      open set containing BOTH representatives would make the statement FALSE: they share a
      ledger and are not automorphism related. Section 5 recovers the two-sided version by
      intersecting the two local sets with {Phi < 0} and {Phi > 0}, which is cheap and
      unconditional.

NO SECTION IS EVER DIFFERENTIATED. `native_flat_two_sections_full54` is an
existential over two arbitrary functions whose only regularity clause is `ContinuousOn`.
Their uses here are frame validity, continuity, ledger equalities, and Phi sign inequalities;
no derivative of a section is taken.
Continuity shrinks the chart neighbourhood once, using `ContinuousOn.isOpen_inter_preimage`
-- the same move `Sections.exists_signed_section_of_equiv` makes at Sections.lean. The orbits of the section values are
identified with the two components by the sign of Phi plus local uniqueness. All smoothness
is quarantined inside `LocalSlice`, which is stated on `ChartTransfer.movedTriple`
(ChartTransfer.lean), a named function with a strict Frechet derivative
(`Sections.hasStrictFDerivAt_cRow_ledger54_movedTriple`, Sections.lean). That is the
actual smooth chart, and it is where 20 + 52 = 72 would be cashed.

RELABELLINGS STAY SEPARATE. Every statement here is about ORDERED triples and about the
DIAGONAL action `mapAtoms g T a i = g.equiv (T a i)` (Relabel.lean), one automorphism on
all nine atoms. `relabelTriple`, `Relabel`, `ledgerAct` and `Affine20.act20` occur in NO
definition, statement or proof below -- the only places those names appear in this file are
this header and the docstrings, which is what a search will show. The reason the care is needed:
`flatBaseRev3` is a single outcome transposition inside the third frame applied to
`flatBaseTriple` (`FlatOrbit.relabelTriple_flatBaseTriple_third` :613), so modulo the 1296
outcome relabellings the flat fibre is ONE class (`flat_fibre_eq_single_relabel_class` :676).
Quotienting would change the count from two to one; that does not weaken the theorem, it
deletes it, because the one bit IS the distinction between the two. `orbits_distinct_at_flat`
below is the printed guard. The relabelling gates (`Affine20.isOpen_moved`,
`dense_moved`, `relabel_gates`, `dense_avoids`) are the natural-looking tools for shrinking a
neighbourhood and are deliberately NOT used: shrinking with them would make the
neighbourhood relabelling-saturated and quietly merge the sheets. Shrinking here uses only
Phi sign and section continuity.

"Product automorphisms", in the target's phrasing, must mean the DIAGONAL action. It must not
mean the frame-wise product group: the ledger is invariant under the diagonal action
(`ledger54_map`) and demonstrably not under the frame-wise one -- the whole rank-20 result is
the statement that frame-wise motion moves twenty ledger coordinates invertibly. Under the
frame-wise group a fibre is not a union of orbits at all.

CONVENTIONS. flatXN = diag(1,0,-1) (FlatBase.lean);
encoder p = p 2 - p 0 (Native.lean); Phi = -4/27 at the ORIGINAL flat ordered triple
(FlatOrbit.phi_flatBase :396). The second representative here is `flatBaseRev3`, the
THIRD-frame reversal, matching `flat_fibre_eq_two_orbits`. `flatBaseRevP` -- the FIRST-frame
reversal, built on the different convention `flatFramePRev := projectorFrame witnessX` -- is
named in this header only and occurs in no definition, statement or proof, so that convention
cannot leak in. `octConj` does not appear and no sign
is corrected anywhere: the two signs come from two separate triples.
`CompactAutomorphism.comp g h` means "first h, then g" (Automorphism.lean); the
conjugation calculation is lifted from `FlatOrbit.nearby_fibre_rigidity_of_local` rather than
rewritten, so that convention cannot drift either.

NO NOVELTY IS CLAIMED. The level-set and orbit description of a
frame-triple fibre may well be classical for H3(K).

Code guidance. `phiOf_apply` bridges `phiOf` to the written-out
`phi (encoder ...)` by `rfl`. Membership `T ∈ autOrbit S` unfolds to
`∃ k, mapAtoms k S = T`. `FlatSectionsOrbits.decode_encode_flatBase`,
`ledger54_flatBase_eq`, and `flatBase_eq_flatBaseTriple` identify the base chart point.
`Set.mem_preimage` and `Set.mem_inter_iff` expose the capstone's preimage memberships.
-/
module

public import Glennie.Compact.FlatSectionsOrbits

@[expose] public section

namespace Glennie.Compact.NearbyOrbits

open Glennie Glennie.Compact.FlatBase Glennie.Compact.Affine20
open Glennie.Compact.FrameTopology Glennie.Compact.FlatOrbit
open Glennie.Compact.Sections

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-! ## 1. The twenty chart coordinates and the fifty-four ledger entries are the same fibre

This section is the whole content of the coordinate shortcut, and it is unconditional. The
sharper tool is `Affine20.decode_encode_frames` (`Affine20/Chart.lean`), which PINS the
value `ledger54 T = decode20 b` rather than merely comparing two triples;
`Affine20.encode20_injOn` (`:344`) is the injectivity form and follows. Both rest on
`Affine20.ledger54_inDomain` (`:80`), which holds for ARBITRARY genuine frame triples with no
nearness, no genericity and nothing about sections.

What this buys and what it does not: it collapses the 54-versus-20 distinction completely,
so "full-54" is a redundant adjective wherever both fibres are in play. It says NOTHING about
how many orbits sit in a fibre, nothing about non-emptiness of a nearby fibre, and nothing
about Phi -- which is not a function of the ledger at all. It is load-bearing at exactly one
step below: it is what puts an arbitrary fibre member, known only by its twenty chart
coordinates, inside a neighbourhood of a 54-entry ledger VALUE. -/

/-- Twenty chart coordinates pin all fifty-four ledger entries. -/
theorem ledger54_eq_decode20 {T : Triple} (hT : ∀ a : Fin 3, Glennie.Frame (T a))
    {b : Fin 20 → ℝ} (hb : encode20 (ledger54 T) = b) :
    ledger54 T = decode20 b := by
  subst hb
  exact (decode_encode_frames T hT).symm

/-- The injectivity form. -/
theorem ledger54_eq_of_encode20_eq {T S : Triple}
    (hT : ∀ a : Fin 3, Glennie.Frame (T a)) (hS : ∀ a : Fin 3, Glennie.Frame (S a))
    (h : encode20 (ledger54 T) = encode20 (ledger54 S)) :
    ledger54 T = ledger54 S :=
  encode20_injOn (ledger54_inDomain T hT) (ledger54_inDomain S hS) h

/-- The FULL 54-entry fibre over a chart point: ordered frame triples whose complete ledger
is the decoded chart point. This is the set the target is about. -/
def fibre54 (b : Fin 20 → ℝ) : Set Triple :=
  {T : Triple | (∀ a : Fin 3, Glennie.Frame (T a)) ∧ ledger54 T = decode20 b}

/-- The 20-coordinate fibre over a chart point. -/
def fibre20 (b : Fin 20 → ℝ) : Set Triple :=
  {T : Triple | (∀ a : Fin 3, Glennie.Frame (T a)) ∧ encode20 (ledger54 T) = b}

/-- Unconditional, for every chart point, with no hypothesis whatever. -/
theorem fibre20_subset_fibre54 (b : Fin 20 → ℝ) : fibre20 b ⊆ fibre54 b := by
  rintro T ⟨hT, hb⟩
  exact ⟨hT, ledger54_eq_decode20 hT hb⟩

/-- The converse, as soon as one member of the 54-entry fibre is known to have chart point
`b`. The proof uses the explicit witness `S` and its chart equality `hSb`, without
invoking `encode20 (decode20 b) = b` or `decode_encode` (Chart.lean). -/
theorem fibre54_subset_fibre20 {b : Fin 20 → ℝ} {S : Triple}
    (hS : S ∈ fibre54 b) (hSb : encode20 (ledger54 S) = b) :
    fibre54 b ⊆ fibre20 b := by
  rintro T ⟨hT, hTb⟩
  refine ⟨hT, ?_⟩
  rw [hTb, ← hS.2]
  exact hSb

/-- Consistency anchor: at the flat chart point the new fibre is the proved one. -/
theorem fibre54_base_eq_flatFibre :
    fibre54 (encode20 (ledger54 Glennie.Compact.Sections.flatBase)) = flatFibre := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro T ⟨hT, hL⟩
    refine ⟨hT, ?_⟩
    rw [hL]
    exact Glennie.Compact.FlatSectionsOrbits.decode_encode_flatBase
  · rintro T ⟨hT, hL⟩
    refine ⟨hT, ?_⟩
    rw [hL]
    exact Glennie.Compact.FlatSectionsOrbits.decode_encode_flatBase.symm

/-! ## 2. Phi in the sections' spelling

`FlatOrbit` writes Phi out as `phi (encoder (T 0)) (encoder (T 1)) (encoder (T 2))`; the
sections use `Sections.phiOf` (`Sections/Reversal.lean`). `phiOf_apply` is `rfl`, so
these are repackagings and not new mathematics. They are needed because the two halves of
the argument speak the two spellings. -/

/-- Phi in `phiOf` spelling is a diagonal-action invariant. -/
theorem phiOf_mapAtoms (g : Glennie.CompactAutomorphism) (T : Triple) :
    phiOf (mapAtoms g T) = phiOf T := by
  rw [phiOf_apply, phiOf_apply]
  exact phi_mapAtoms g T

/-- Hence constant on orbits. -/
theorem phiOf_eq_of_mem_autOrbit {S T : Triple} (h : T ∈ autOrbit S) :
    phiOf T = phiOf S := by
  rw [phiOf_apply, phiOf_apply]
  exact phi_eq_of_mem_autOrbit h

/-- The action law in the direction `FlatOrbit` does not record. Proved directly from
`apply_symm_apply` rather than from `mapAtoms_symm_mapAtoms` at `g := g.symm`, which would
need `g.symm.symm = g`. -/
theorem mapAtoms_mapAtoms_symm (g : Glennie.CompactAutomorphism) (T : Triple) :
    mapAtoms g (mapAtoms g.symm T) = T := by
  funext a i
  show g.equiv (g.equiv.symm (T a i)) = T a i
  exact g.equiv.apply_symm_apply (T a i)

theorem phiOf_flatBaseTriple_neg : phiOf flatBaseTriple < 0 := by
  rw [phiOf_apply, phi_flatBase]
  norm_num

theorem phiOf_flatBaseRev3_pos : 0 < phiOf flatBaseRev3 := by
  rw [phiOf_apply, phi_flatBaseRev3]
  norm_num

/-! ## 3. Phi does not vanish on fibres near the flat one — UNCONDITIONAL

The set
of triples with |Phi| > 1/27 is open by `continuous_phiOf`; it contains the WHOLE flat fibre,
because `FlatOrbit.ledger54_eq_flat_iff_abs_phi` (`:350`) says every frame triple with the
flat ledger has |Phi| = 4/27; so `FrameTopology.flatBase_ledger_saturated` (`:305`) hands
back a neighbourhood of the flat ledger value on which the bound holds for every frame
triple.

Why it matters: a member of a nearby fibre with Phi = 0 would lie in NEITHER section orbit,
since Phi is an orbit invariant and both section values have Phi strictly signed. So without
this lemma the target is false as stated, and this is the piece most likely to be assumed
silently. The only compactness used anywhere in this file is the one already inside that
saturation lemma. -/

theorem isOpen_phi_bounded_away : IsOpen {T : Triple | 1 / 27 < |phiOf T|} :=
  isOpen_lt continuous_const continuous_phiOf.abs

theorem phi_bounded_away_near_flat :
    ∃ V : Set Ledger54, IsOpen V ∧ ledger54 flatBaseTriple ∈ V ∧
      ∀ T : Triple, (∀ a : Fin 3, Glennie.Frame (T a)) → ledger54 T ∈ V →
        1 / 27 < |phiOf T| := by
  have hsub : ∀ T : Triple, (∀ a : Fin 3, Glennie.Frame (T a)) →
      ledger54 T = ledger54 flatBaseTriple → T ∈ {T : Triple | 1 / 27 < |phiOf T|} := by
    intro T hT hL
    have habs : |phiOf T| = 4 / 27 := by
      rw [phiOf_apply]
      exact (ledger54_eq_flat_iff_abs_phi T hT).mp hL
    show 1 / 27 < |phiOf T|
    rw [habs]
    norm_num
  obtain ⟨V, hVopen, hVmem, hVsub⟩ :=
    flatBase_ledger_saturated isOpen_phi_bounded_away hsub
  exact ⟨V, hVopen, hVmem, hVsub⟩

/-- The bound gives a strict sign, which is what the two-sheet split needs. -/
theorem phi_sign_of_bounded_away {T : Triple} (h : 1 / 27 < |phiOf T|) :
    phiOf T < 0 ∨ 0 < phiOf T := by
  rcases lt_trichotomy (phiOf T) 0 with hlt | heq | hgt
  · exact Or.inl hlt
  · exfalso
    rw [heq, abs_zero] at h
    norm_num at h
  · exact Or.inr hgt

/-! ## 4. THE MISSING LOCAL INGREDIENT, as an explicit named hypothesis

Read the module header for why this is NOT `FlatOrbit.LocalFlatRigidity`: the Phi-equality
hypothesis is dropped, because the Phi-equality version cannot give the target, and the
statement is localised at ONE base triple, because with the Phi condition dropped a set
containing both representatives would make it false.

WHY COMPACTNESS CANNOT SUPPLY THIS, spelled out as the scenario it permits. The tube
machinery (`frameTriples_isCompact` :177, `continuous_ledger54` :227, `fibre_tube` :244,
assembled as `flat_fibre_no_remote_components`) delivers exactly one thing: nearby fibres are
squeezed into any tube drawn around the flat fibre. That is proximity, and orbits are not
open sets, so there is no continuity step from proximity to membership. Suppose the fibre
over each nearby chart point carried a THIRD orbit which shrank into the flat fibre as the
chart point returned to the flat one. The compactness and section statements would still be
true -- the third orbit lies in the tube, it is invisible at the flat value where the exact
classification holds, and the sections and their signs are untouched -- and the target would
be false. Orbit count jumping up away from a non-generic value is ordinary behaviour of level
sets, not a pathology. So this hypothesis is a genuine proof obligation and not a worry. -/

/-- LOCAL ORBIT-COMPLETENESS AT ONE TRIPLE. On some open set around `B`, two frame triples
with the same 54-entry ledger are automorphism related. NOT PROVED HERE.

By section 1 the hypothesis `ledger54 T = ledger54 S` may be read interchangeably as
`encode20 (ledger54 T) = encode20 (ledger54 S)` for frame triples, so nothing is lost or
gained by the choice of coordinate system here. -/
def LocalOrbitCompleteness (B : Triple) : Prop :=
  ∃ U : Set Triple, IsOpen U ∧ B ∈ U ∧
    ∀ T S : Triple, (∀ a : Fin 3, Glennie.Frame (T a)) →
      (∀ a : Fin 3, Glennie.Frame (S a)) → T ∈ U → S ∈ U →
      ledger54 T = ledger54 S →
      ∃ k : Glennie.CompactAutomorphism, mapAtoms k S = T

/-- THE HYPOTHESIS IS A PROPERTY OF THE ORBIT, NOT OF THE POINT. Unconditional. The open set
is pulled back along `mapAtoms g.symm`, which is continuous by
`FlatOrbit.continuous_mapAtoms` (`:294`). This is what makes "local at the two
representatives" the right amount of hypothesis rather than an arbitrary choice: it already
covers every triple the transport in section 5 reaches. -/
theorem localOrbitCompleteness_mapAtoms {B : Triple} (g : Glennie.CompactAutomorphism)
    (h : LocalOrbitCompleteness B) : LocalOrbitCompleteness (mapAtoms g B) := by
  obtain ⟨U, hUopen, hBU, hrig⟩ := h
  refine ⟨(fun T : Triple => mapAtoms g.symm T) ⁻¹' U,
    hUopen.preimage (continuous_mapAtoms g.symm), ?_, ?_⟩
  · show mapAtoms g.symm (mapAtoms g B) ∈ U
    rw [mapAtoms_symm_mapAtoms]
    exact hBU
  · intro T S hT hS hTU hSU hL
    obtain ⟨k, hk⟩ :=
      hrig (mapAtoms g.symm T) (mapAtoms g.symm S)
        (fun a => frame_mapAtoms g.symm T hT a) (fun a => frame_mapAtoms g.symm S hS a)
        hTU hSU (by rw [ledger54_map, ledger54_map, hL])
    refine ⟨g.comp (k.comp g.symm), ?_⟩
    calc mapAtoms (g.comp (k.comp g.symm)) S
        = mapAtoms g (mapAtoms (k.comp g.symm) S) :=
          (mapAtoms_comp g (k.comp g.symm) S).symm
      _ = mapAtoms g (mapAtoms k (mapAtoms g.symm S)) :=
          congrArg (fun X : Triple => mapAtoms g X) (mapAtoms_comp k g.symm S).symm
      _ = mapAtoms g (mapAtoms g.symm T) := congrArg (fun X : Triple => mapAtoms g X) hk
      _ = T := mapAtoms_mapAtoms_symm g T

/-! ## 5. Rigidity over a whole neighbourhood of the flat ledger, in SIGN form

CONDITIONAL on the two instances of the hypothesis, and on nothing else. The transport uses `FlatOrbit.exists_invariant_open` (`:716`) saturates the
local set under the action, and `FlatOrbit.flat_fibre_no_remote_components` (`:744`) converts
"contains the two representatives" into "contains every frame triple whose ledger is near the
flat value". The new part is only the sign separation, which costs two intersections with
open half-spaces of Phi.

The argument does not need compactness of either orbit,
compactness of the automorphism group as a topological group, `automorphismMaps_compact`,
`compactAutomorphismOfMap`, and any continuity in the group variable (which is unavailable
anyway -- the corpus has no topology on `CompactAutomorphism`). -/

/-- The conjugation step, lifted verbatim from `FlatOrbit.nearby_fibre_rigidity_of_local`
(`:780`) so that the composition convention cannot drift. -/
theorem related_of_transport {T S : Triple} {g m k : Glennie.CompactAutomorphism}
    (h : mapAtoms k (mapAtoms m S) = mapAtoms g T) :
    ∃ k' : Glennie.CompactAutomorphism, mapAtoms k' S = T := by
  refine ⟨g.symm.comp (k.comp m), ?_⟩
  calc mapAtoms (g.symm.comp (k.comp m)) S
      = mapAtoms g.symm (mapAtoms (k.comp m) S) := (mapAtoms_comp g.symm (k.comp m) S).symm
    _ = mapAtoms g.symm (mapAtoms k (mapAtoms m S)) :=
        congrArg (fun X : Triple => mapAtoms g.symm X) (mapAtoms_comp k m S).symm
    _ = mapAtoms g.symm (mapAtoms g T) := congrArg (fun X : Triple => mapAtoms g.symm X) h
    _ = T := mapAtoms_symm_mapAtoms g T

/-- CONDITIONAL. Over a neighbourhood of the flat ledger value, two frame triples with equal
ledgers and Phi of the SAME SIGN are automorphism related.

This is the sign form, and the sign form is what the target needs; see the module header on
why the Phi-equality form does not suffice. The two local open sets are cut down to the two
Phi half-spaces, so a transported pair with the same sign necessarily lands in the SAME piece
and one of the two hypothesis instances applies. -/
theorem nearby_sign_rigidity
    (h0 : LocalOrbitCompleteness flatBaseTriple)
    (h3 : LocalOrbitCompleteness flatBaseRev3) :
    ∃ V : Set Ledger54, IsOpen V ∧ ledger54 flatBaseTriple ∈ V ∧
      ∀ T S : Triple, (∀ a : Fin 3, Glennie.Frame (T a)) →
        (∀ a : Fin 3, Glennie.Frame (S a)) → ledger54 T ∈ V →
        ledger54 T = ledger54 S →
        ((phiOf T < 0 ∧ phiOf S < 0) ∨ (0 < phiOf T ∧ 0 < phiOf S)) →
        ∃ k : Glennie.CompactAutomorphism, mapAtoms k S = T := by
  obtain ⟨U0, hU0open, hU0mem, hrig0⟩ := h0
  obtain ⟨U3, hU3open, hU3mem, hrig3⟩ := h3
  have hopen :
      IsOpen ((U0 ∩ {T : Triple | phiOf T < 0}) ∪ (U3 ∩ {T : Triple | 0 < phiOf T})) :=
    (hU0open.inter (isOpen_lt continuous_phiOf continuous_const)).union
      (hU3open.inter (isOpen_lt continuous_const continuous_phiOf))
  have hmem0 : flatBaseTriple ∈
      (U0 ∩ {T : Triple | phiOf T < 0}) ∪ (U3 ∩ {T : Triple | 0 < phiOf T}) :=
    Or.inl ⟨hU0mem, phiOf_flatBaseTriple_neg⟩
  have hmem3 : flatBaseRev3 ∈
      (U0 ∩ {T : Triple | phiOf T < 0}) ∪ (U3 ∩ {T : Triple | 0 < phiOf T}) :=
    Or.inr ⟨hU3mem, phiOf_flatBaseRev3_pos⟩
  obtain ⟨W, hWopen, hUW, hWinv, hWmem⟩ := exists_invariant_open _ hopen
  obtain ⟨V, hVopen, hVmem, hVsub⟩ :=
    flat_fibre_no_remote_components hWopen (hUW hmem0) (hUW hmem3) hWinv
  refine ⟨V, hVopen, hVmem, ?_⟩
  intro T S hT hS hTV hLTS hsign
  have hSV : ledger54 S ∈ V := by rw [← hLTS]; exact hTV
  obtain ⟨g, hgU⟩ := hWmem T (hVsub T hT hTV)
  obtain ⟨m, hmU⟩ := hWmem S (hVsub S hS hSV)
  have hgT : ∀ a : Fin 3, Glennie.Frame (mapAtoms g T a) := fun a => frame_mapAtoms g T hT a
  have hmS : ∀ a : Fin 3, Glennie.Frame (mapAtoms m S a) := fun a => frame_mapAtoms m S hS a
  have hLmap : ledger54 (mapAtoms g T) = ledger54 (mapAtoms m S) := by
    rw [ledger54_map, ledger54_map, hLTS]
  have hgphi : phiOf (mapAtoms g T) = phiOf T := phiOf_mapAtoms g T
  have hmphi : phiOf (mapAtoms m S) = phiOf S := phiOf_mapAtoms m S
  rcases hsign with ⟨hTn, hSn⟩ | ⟨hTp, hSp⟩
  · have hgIn : mapAtoms g T ∈ U0 := by
      rcases hgU with hx | hx
      · exact hx.1
      · exfalso
        have hpos : 0 < phiOf (mapAtoms g T) := hx.2
        rw [hgphi] at hpos
        linarith
    have hmIn : mapAtoms m S ∈ U0 := by
      rcases hmU with hx | hx
      · exact hx.1
      · exfalso
        have hpos : 0 < phiOf (mapAtoms m S) := hx.2
        rw [hmphi] at hpos
        linarith
    obtain ⟨k, hk⟩ := hrig0 (mapAtoms g T) (mapAtoms m S) hgT hmS hgIn hmIn hLmap
    exact related_of_transport hk
  · have hgIn : mapAtoms g T ∈ U3 := by
      rcases hgU with hx | hx
      · exfalso
        have hneg : phiOf (mapAtoms g T) < 0 := hx.2
        rw [hgphi] at hneg
        linarith
      · exact hx.1
    have hmIn : mapAtoms m S ∈ U3 := by
      rcases hmU with hx | hx
      · exfalso
        have hneg : phiOf (mapAtoms m S) < 0 := hx.2
        rw [hmphi] at hneg
        linarith
      · exact hx.1
    obtain ⟨k, hk⟩ := hrig3 (mapAtoms g T) (mapAtoms m S) hgT hmS hgIn hmIn hLmap
    exact related_of_transport hk

/-! ## 6. THE TARGET

CONDITIONAL on the two instances of `LocalOrbitCompleteness` and on nothing else. Every
clause of `native_flat_two_sections_full54` is carried through unchanged; the
last three conjuncts are the new content.

The neighbourhood is shrunk HONESTLY and without differentiating anything: it is the
sections' own open set intersected with the preimage, under the continuous-on map
`b ↦ ledger54 (secNeg b)`, of the ledger neighbourhood supplied by section 5 and section 3.
Openness is `ContinuousOn.isOpen_inter_preimage`, exactly the move
`Sections.exists_signed_section_of_equiv` makes at `Sections.lean`. The base chart point
survives because `FlatSectionsOrbits.decode_encode_flatBase` identifies the decoded base
chart point with the flat 54-entry ledger.

Where each ingredient is used, so the proof can be audited by eye. Section 1 converts a
candidate's twenty chart coordinates into its full ledger, which is what puts it inside the
ledger neighbourhood. Section 3 rules out Phi = 0 and so forces one of the two sheets.
Section 5 then matches the candidate with the section value of that sheet. Disjointness is
the sign of Phi and nothing else. -/

/-- THE NEARBY FIBRE CLASSIFICATION. Over an open chart neighbourhood of the flat chart
point, every FULL 54-entry fibre is exactly the disjoint union of the two section orbits
under the diagonal automorphism action, and the 20-coordinate fibre is the same set.

ORDERED TRIPLES. "Exactly two" is a statement about ordered triples and about the diagonal
action. No relabelling is quotiented anywhere; see the module header. -/
theorem nearby_fibres_two_orbits
    (h0 : LocalOrbitCompleteness flatBaseTriple)
    (h3 : LocalOrbitCompleteness flatBaseRev3) :
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
        (∀ b ∈ V, 0 < phiOf (secPos b)) ∧
        (∀ b ∈ V, phiOf (secNeg b) < 0) ∧
        (∀ b ∈ V, fibre54 b = autOrbit (secNeg b) ∪ autOrbit (secPos b)) ∧
        (∀ b ∈ V, Disjoint (autOrbit (secNeg b)) (autOrbit (secPos b))) ∧
        (∀ b ∈ V, fibre20 b = fibre54 b) := by
  obtain ⟨V0, hV0, hbase, secPos, secNeg, hcP, hcN, hfP, hfN, heP, heN, hlP, hlN, hpP, hpN⟩ :=
    Glennie.Compact.NativeFlatSections.native_flat_two_sections_full54
  obtain ⟨V1, hV1open, hV1mem, hrig⟩ := nearby_sign_rigidity h0 h3
  obtain ⟨V2, hV2open, hV2mem, hV2sub⟩ := phi_bounded_away_near_flat
  have hcL : ContinuousOn (fun b : Fin 20 → ℝ => ledger54 (secNeg b)) V0 :=
    continuous_ledger54.comp_continuousOn' hcN
  have hbL : ledger54 (secNeg (encode20 (ledger54 Glennie.Compact.Sections.flatBase)))
      = ledger54 flatBaseTriple := by
    rw [hlN _ hbase]
    exact Glennie.Compact.FlatSectionsOrbits.decode_encode_flatBase
  have hbmem : ledger54 (secNeg (encode20 (ledger54 Glennie.Compact.Sections.flatBase)))
      ∈ V1 ∩ V2 := by
    rw [hbL]
    exact ⟨hV1mem, hV2mem⟩
  refine ⟨V0 ∩ (fun b : Fin 20 → ℝ => ledger54 (secNeg b)) ⁻¹' (V1 ∩ V2),
    hcL.isOpen_inter_preimage hV0 (hV1open.inter hV2open),
    ⟨hbase, hbmem⟩,
    secPos, secNeg,
    hcP.mono Set.inter_subset_left, hcN.mono Set.inter_subset_left,
    (fun b hb => hfP b hb.1), (fun b hb => hfN b hb.1),
    (fun b hb => heP b hb.1), (fun b hb => heN b hb.1),
    (fun b hb => hlP b hb.1), (fun b hb => hlN b hb.1),
    (fun b hb => hpP b hb.1), (fun b hb => hpN b hb.1), ?_, ?_, ?_⟩
  · -- the fibre is exactly the two orbits
    intro b hb
    have hbV0 : b ∈ V0 := hb.1
    have hNL : ledger54 (secNeg b) = decode20 b := hlN b hbV0
    have hPL : ledger54 (secPos b) = decode20 b := hlP b hbV0
    have hNV1 : ledger54 (secNeg b) ∈ V1 := hb.2.1
    have hNV2 : ledger54 (secNeg b) ∈ V2 := hb.2.2
    refine Set.Subset.antisymm ?_ ?_
    · rintro T ⟨hT, hTL⟩
      have hTeqN : ledger54 T = ledger54 (secNeg b) := by rw [hTL, hNL]
      have hTeqP : ledger54 T = ledger54 (secPos b) := by rw [hTL, hPL]
      have hTV1 : ledger54 T ∈ V1 := by rw [hTeqN]; exact hNV1
      have hTV2 : ledger54 T ∈ V2 := by rw [hTeqN]; exact hNV2
      rcases phi_sign_of_bounded_away (hV2sub T hT hTV2) with hneg | hpos
      · exact Or.inl
          (hrig T (secNeg b) hT (hfN b hbV0) hTV1 hTeqN (Or.inl ⟨hneg, hpN b hbV0⟩))
      · exact Or.inr
          (hrig T (secPos b) hT (hfP b hbV0) hTV1 hTeqP (Or.inr ⟨hpos, hpP b hbV0⟩))
    · rintro T (⟨g, rfl⟩ | ⟨g, rfl⟩)
      · exact ⟨fun a => frame_mapAtoms g (secNeg b) (hfN b hbV0) a,
          by rw [ledger54_map, hNL]⟩
      · exact ⟨fun a => frame_mapAtoms g (secPos b) (hfP b hbV0) a,
          by rw [ledger54_map, hPL]⟩
  · -- the two orbits are disjoint, by the sign of Phi and nothing else
    intro b hb
    have hbV0 : b ∈ V0 := hb.1
    rw [Set.disjoint_left]
    intro T hTN hTP
    have h1 : phiOf T = phiOf (secNeg b) := phiOf_eq_of_mem_autOrbit hTN
    have h2 : phiOf T = phiOf (secPos b) := phiOf_eq_of_mem_autOrbit hTP
    have hn : phiOf (secNeg b) < 0 := hpN b hbV0
    have hp : 0 < phiOf (secPos b) := hpP b hbV0
    linarith
  · -- the 20-coordinate fibre is the same set
    intro b hb
    have hbV0 : b ∈ V0 := hb.1
    refine Set.Subset.antisymm (fibre20_subset_fibre54 b) ?_
    exact fibre54_subset_fibre20
      (show secNeg b ∈ fibre54 b from ⟨hfN b hbV0, hlN b hbV0⟩) (heN b hbV0)

/-- PRINTED GUARD AGAINST THE RELABELLING COLLAPSE. The two orbits at the flat base are
distinct as SETS, so the count is genuinely two for ordered triples. Modulo the 1296 outcome
relabellings the flat fibre is ONE class
(`FlatOrbit.flat_fibre_eq_single_relabel_class`, `:676`), which is a different statement
about a different object; the two live here side by side so that neither can be mistaken for
the other. Unconditional. -/
theorem orbits_distinct_at_flat : autOrbit flatBaseTriple ≠ autOrbit flatBaseRev3 := by
  intro h
  have hmem : flatBaseTriple ∈ autOrbit flatBaseRev3 := by
    rw [← h]
    exact mem_autOrbit_self flatBaseTriple
  exact Set.disjoint_left.mp flat_orbits_disjoint (mem_autOrbit_self flatBaseTriple) hmem

/-! ## 7. The dimension count, in open-mapping form

The dimension argument is that genuine rank 20 on the smooth 72-dimensional triple-frame space
makes the local row fibre 52-dimensional, which with the flat classification and embedded
compact-group orbits supplies the orbit conclusion. The arithmetic is right -- the frame space
is 24-dimensional (16 for a primitive idempotent, 8 for the complementary pair, equivalently
52 - 28 with the pointwise frame stabiliser the 28-dimensional Spin(8) acting by triality),
three frames give 72, and 72 - 20 = 52 is exactly the group dimension, which is the
circumstance under which an orbit can be open in its fibre. The transversality half is also
nearly free: the twenty flow directions are tangent to the frame-triple space
(`ChartTransfer.movedTriple_frame`, `:512`) and move twenty ledger coordinates invertibly,
while the diagonal orbit directions move the ledger not at all (`ledger54_map`).

But the route is not stateable in this package. There is no `ChartedSpace`, no `IsManifold`,
no `TangentSpace`, no `mfderiv` and no `Mathlib.Geometry` import anywhere in it, and no
`Group` instance on `CompactAutomorphism` -- `FlatOrbit` re-proves the three action laws by
hand for exactly that reason. The rank-20 result is invertibility of a 20x20
Jacobian of a map from R^20 to R^20 built from FRAME-WISE flows at `s = 0`
(`FlowFamily.rowLedger`, `:341`), not a rank statement on a 72-dimensional space. And even
granted the whole manifold package the conclusion would be "each orbit is open in its fibre",
which kills accumulation but does not give the count two.

So the dimension content is recorded here in OPEN-MAPPING form instead, which needs no
manifold, no tangent space and no topology on the group: near the base triple, every frame
triple is a diagonal automorphism applied to a point of the twenty-parameter flow slice. That
is `LocalSlice`, and it implies the hypothesis of sections 5 and 6, providing an alternative sufficient condition. The second conjunct of `LocalSlice` is the
local-injectivity condition. The inverse function theorem supplies such a condition through
`HasStrictFDerivAt.toOpenPartialHomeomorph` on the same `rowLedger` that
`Sections.exists_section_of_equiv` (`Sections.lean`) uses. Extracting it requires
the invertibility witness in scope. Here the local-injectivity condition remains an
explicit hypothesis. -/

/-- THE DIMENSION COUNT AS AN OPEN-MAPPING STATEMENT, as an explicit named hypothesis. Near
`B`, every frame triple is a diagonal automorphism applied to a point of the flow slice
through `B`, and the ledger is injective on that slice. NOT PROVED HERE. This is where
20 + 52 = 72 would be cashed, with no derivative in the statement. -/
def LocalSlice (B : Triple) : Prop :=
  ∃ U : Set Triple, IsOpen U ∧ B ∈ U ∧
    ∃ S : Set (Fin 20 → ℝ),
      (∀ T : Triple, (∀ a : Fin 3, Glennie.Frame (T a)) → T ∈ U →
        ∃ g : Glennie.CompactAutomorphism, ∃ s ∈ S,
          T = mapAtoms g (Glennie.Compact.ChartTransfer.movedTriple B s)) ∧
      (∀ s ∈ S, ∀ s' ∈ S,
        ledger54 (Glennie.Compact.ChartTransfer.movedTriple B s) =
            ledger54 (Glennie.Compact.ChartTransfer.movedTriple B s') → s = s')

/-- THE SLICE FORM IMPLIES THE RIGIDITY FORM. Unconditional. Four moves, using only the
diagonal invariance of the ledger (`ledger54_map`) and the action laws: write both triples in
slice form, strip the automorphisms off their ledgers, conclude the slice parameters agree,
and compose. So `LocalSlice` is an alternative target for the same gap and not an extra
assumption. -/
theorem localOrbitCompleteness_of_localSlice {B : Triple} (h : LocalSlice B) :
    LocalOrbitCompleteness B := by
  obtain ⟨U, hUopen, hBU, Sl, hcover, hinj⟩ := h
  refine ⟨U, hUopen, hBU, ?_⟩
  intro T S' hT hS' hTU hS'U hL
  obtain ⟨g, s, hsS, hTg⟩ := hcover T hT hTU
  obtain ⟨m, s', hs'S, hSm⟩ := hcover S' hS' hS'U
  have hLs : ledger54 (Glennie.Compact.ChartTransfer.movedTriple B s) =
      ledger54 (Glennie.Compact.ChartTransfer.movedTriple B s') := by
    rw [← ledger54_map g (Glennie.Compact.ChartTransfer.movedTriple B s),
      ← ledger54_map m (Glennie.Compact.ChartTransfer.movedTriple B s'), ← hTg, ← hSm]
    exact hL
  have hss : s = s' := hinj s hsS s' hs'S hLs
  refine ⟨g.comp m.symm, ?_⟩
  rw [hSm, ← mapAtoms_comp, mapAtoms_symm_mapAtoms, ← hss]
  exact hTg.symm

end
end Glennie.Compact.NearbyOrbits
