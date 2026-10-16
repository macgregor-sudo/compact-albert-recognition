/- WHAT THIS MODULE PROVES.

  The set of ORDERED frame triples whose complete 54-entry ledger equals the
  flat-base ledger is EXACTLY the disjoint union of two non-empty compact
  automorphism orbits, and the two are told apart by the sign of Phi:

    flat_fibre_eq_two_orbits      flatFibre = autOrbit flatBaseTriple
                                                 ∪ autOrbit flatBaseRev3
    flat_orbits_disjoint          the two orbits are disjoint
    autOrbit_flatBase_eq          the first orbit is exactly the Phi = -4/27 sheet
    autOrbit_flatBaseRev3_eq      the second orbit is exactly the Phi = +4/27 sheet
    flat_fibre_eq_abs_phi         the fibre itself is the frame triples with |Phi| = 4/27

  The second representative is the flat triple with its THIRD frame reversed.
  That is the triple the classification actually produces. It is NOT
  `Sections.revTriple Sections.flatBase`, which reverses the FIRST frame; the
  first-frame reversal is handled separately as `flatBaseRevP` and lands in the
  same orbit as `flatBaseRev3`, which reconciles this module with the sections.

  Section 7 answers the relabelling question: `flatBaseRev3` is a single outcome
  transposition inside the third frame applied to `flatBaseTriple`, so modulo the
  1296 relabellings the flat fibre is ONE class, not two. The two-orbit count is a
  statement about ORDERED triples and about nothing else.

  Section 8 is the neighbourhood material. `flat_fibre_no_remote_components` is
  UNCONDITIONAL. `nearby_fibre_rigidity_of_local` is CONDITIONAL on an explicit
  named hypothesis `LocalFlatRigidity`, in the style of
  `Rank20Reduction.rank20_of_bridge` (:77) and its `hT` premise. That hypothesis is
  the genuine missing local ingredient and is NOT proved here; it is strictly
  weaker than the theorem's conclusion. Nothing beyond it is assumed anywhere.

Dependencies. `Glennie.NativeFirstPairNormalization.native_flat_full54_ordered_base_fibre`
(FirstPairNormalization.lean) supplies the forward inclusion.
`Glennie.Compact.FrameTopology` supplies `flatBaseTriple`, the flat ledger constants,
`continuous_entry`, and `flatBase_ledger_saturated`.

  NO JACOBIAN MATERIAL IS IN THE IMPORT CLOSURE. `ChartTransfer`, `FlowFamily`,
  `Affine20.Chart`, `Rank20Certificate`, `Rank20Reduction`, `Sections` and
  `Sections.Reversal` are all absent. That is why Phi is written out as
  `phi (encoder (T 0)) (encoder (T 1)) (encoder (T 2))` rather than as
  `Sections.Reversal.phiOf` (Reversal.lean) — the two are the same term by
  `rfl`, but importing `Sections.Reversal` would pull `ChartTransfer` and
  `FlowFamily`, the two modules in that closure that mention Jacobian objects.
  For the same reason `FrameTopology.flatBaseTriple` is used rather than
  `Sections.flatBase` (Sections.lean); both are literally
  `![flatFrameP, flatFrameQ, flatFrameR]`, so in any module importing both,
  `flatBaseTriple = Sections.flatBase` holds by `rfl`.

CONVENTIONS.

  flatXN = diag(1,0,-1) (FlatBase.lean); flatY1 upper slots (1,-i,1) (:64);
  flatScale = 1/sqrt 3 (:53); encoder p = p 2 - p 0 (Native.lean);
  reverseFrame r = ![r 2, r 1, r 0] (FlatBase.lean);
  Phi = -4/27 at the ORIGINAL ordered flat triple (flat_phi, :255).
  `flatFramePRev := projectorFrame witnessX` (:211) is a DIFFERENT, non-default
  convention from `flatFrameP := projectorFrame flatXN` (:207) and flips Phi to
  +4/27 (flatRev_phi, :263); it is used here only where the first-frame reversal
  is meant. `octConj` is an anti-automorphism and is not used.

The lemmas `frame_reverseFrame` and `reverseFrame_apply_swap` have counterparts
`Sections.Reversal.frame_swap` (Reversal.lean) and
`Sections.reverseFrame_eq_swap` (Sections.lean). Their local formulations
keep this module's import closure free of Jacobian material.
`triple_eta` and unfolding `flatBaseTriple` bridge `ledger54 ![T 0, T 1, T 2]`
to `ledger54 flatBaseTriple`; `uniform_of_full54` (FirstPairNormalization.lean)
uses the same reduction. `flatRelabelThird_order` uses `Equiv.refl (Fin 3) = 1` by `rfl`.
-/
module

public import Glennie.Native.FirstPairNormalization
public import Glennie.Compact.FrameTopology
public import Mathlib.Logic.Equiv.Basic

@[expose] public section

namespace Glennie.Compact.FlatOrbit

open Glennie Glennie.Compact.FlatBase Glennie.Compact.Affine20
open Glennie.Compact.FrameTopology

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-! ## 1. The compact automorphism action on ordered triples

`mapAtoms g T a i = g.equiv (T a i)` (`Relabel.lean`) is a pointwise action on
all nine atoms at once. The package carries no `Group CompactAutomorphism`
instance, only `refl` (`Automorphism.lean`), `comp` and `symm`,
so the three action laws are recorded here as lemmas. They are what makes
`autOrbit` an equivalence class rather than merely an image. -/

/-- The identity acts trivially. -/
theorem mapAtoms_refl (T : Triple) :
    mapAtoms Glennie.CompactAutomorphism.refl T = T := by
  funext a i
  show Glennie.CompactAutomorphism.refl.equiv (T a i) = T a i
  rfl

/-- The action is associative. -/
theorem mapAtoms_comp (g h : Glennie.CompactAutomorphism) (T : Triple) :
    mapAtoms g (mapAtoms h T) = mapAtoms (g.comp h) T := rfl

/-- The action is invertible. -/
theorem mapAtoms_symm_mapAtoms (g : Glennie.CompactAutomorphism) (T : Triple) :
    mapAtoms g.symm (mapAtoms g T) = T := by
  funext a i
  show g.equiv.symm (g.equiv (T a i)) = T a i
  exact g.equiv.symm_apply_apply (T a i)

/-- The compact automorphism orbit of an ordered triple. The group is
`Glennie.CompactAutomorphism` (`Obligations.lean`): a real-linear equivalence of
`Albert` preserving the native Jordan product and the trace. No compactness of the
group as a topological group, and no identification with F4, is used or claimed. -/
def autOrbit (S : Triple) : Set Triple :=
  {T : Triple | ∃ g : Glennie.CompactAutomorphism, mapAtoms g S = T}

theorem mem_autOrbit_self (S : Triple) : S ∈ autOrbit S :=
  ⟨Glennie.CompactAutomorphism.refl, mapAtoms_refl S⟩

theorem mapAtoms_mem_autOrbit (g : Glennie.CompactAutomorphism) (S : Triple) :
    mapAtoms g S ∈ autOrbit S := ⟨g, rfl⟩

/-- Orbits of orbit members coincide, so `autOrbit` really is an equivalence class. -/
theorem autOrbit_eq_of_mem {S T : Triple} (h : T ∈ autOrbit S) :
    autOrbit T = autOrbit S := by
  obtain ⟨g, hg⟩ := h
  have hS : mapAtoms g.symm T = S := by
    rw [← hg, mapAtoms_symm_mapAtoms]
  refine Set.Subset.antisymm ?_ ?_
  · rintro X ⟨k, hk⟩
    refine ⟨k.comp g, ?_⟩
    rw [← mapAtoms_comp, hg, hk]
  · rintro X ⟨k, hk⟩
    refine ⟨k.comp g.symm, ?_⟩
    rw [← mapAtoms_comp, hS, hk]

/-- Frames are preserved slotwise, by `map_frame` (`Automorphism.lean`). -/
theorem frame_mapAtoms (g : Glennie.CompactAutomorphism) (T : Triple)
    (hT : ∀ a : Fin 3, Glennie.Frame (T a)) (a : Fin 3) :
    Glennie.Frame (mapAtoms g T a) :=
  g.map_frame (T a) (hT a)

/-- Phi is an orbit invariant. This is the whole separation mechanism: `encoder_map`
(`Automorphism.lean`) moves the automorphism out of each encoder and `phi_map`
(`:49`) then cancels it. No genericity guard and no side condition. -/
theorem phi_mapAtoms (g : Glennie.CompactAutomorphism) (T : Triple) :
    Glennie.phi (Glennie.encoder (mapAtoms g T 0)) (Glennie.encoder (mapAtoms g T 1))
        (Glennie.encoder (mapAtoms g T 2)) =
      Glennie.phi (Glennie.encoder (T 0)) (Glennie.encoder (T 1))
        (Glennie.encoder (T 2)) := by
  have h : ∀ a : Fin 3,
      Glennie.encoder (mapAtoms g T a) = g.equiv (Glennie.encoder (T a)) := by
    intro a
    rw [mapAtoms_slot]
    exact g.encoder_map (T a)
  rw [h 0, h 1, h 2, g.phi_map]

theorem phi_eq_of_mem_autOrbit {S T : Triple} (h : T ∈ autOrbit S) :
    Glennie.phi (Glennie.encoder (T 0)) (Glennie.encoder (T 1)) (Glennie.encoder (T 2)) =
      Glennie.phi (Glennie.encoder (S 0)) (Glennie.encoder (S 1))
        (Glennie.encoder (S 2)) := by
  obtain ⟨g, rfl⟩ := h
  exact phi_mapAtoms g S

/-! ## 2. Elementary lemmas

`encoder_reverseFrame` negates the encoder of the reversed frame. The sign lemmas
`flat_phi` / `flatRev_phi` concern the first frame, whereas the classification produces
reversal of the third frame. -/

/-- A triple is its own three slots. Needed only because the classification is
stated on `![p, q, r]` and the fibre on `T`; the two sides are already equal after
`ledger54` unfolds. -/
theorem triple_eta (T : Triple) : ![T 0, T 1, T 2] = T := by
  funext a i
  rcases fin3_cases a with rfl | rfl | rfl
  · rfl
  · rfl
  · rfl

/-- Reversing a frame negates its encoder. `encoder p = p 2 - p 0`
(`Native.lean`) and `reverseFrame p = ![p 2, p 1, p 0]` (`FlatBase.lean`),
so this is `p 0 - p 2 = -(p 2 - p 0)`. -/
theorem encoder_reverseFrame (p : Fin 3 → Albert) :
    Glennie.encoder (reverseFrame p) = -Glennie.encoder p := by
  show p 0 - p 2 = -(p 2 - p 0)
  abel

/-- The reversal of a frame is a frame. Duplicates `Reversal.frame_swap`
(`Reversal.lean`) in the `reverseFrame` formulation; see the header. -/
theorem frame_reverseFrame {p : Fin 3 → Albert} (hp : Glennie.Frame p) :
    Glennie.Frame (reverseFrame p) where
  trace_one i := by
    rcases fin3_cases i with rfl | rfl | rfl
    · exact hp.trace_one 2
    · exact hp.trace_one 1
    · exact hp.trace_one 0
  idempotent i := by
    rcases fin3_cases i with rfl | rfl | rfl
    · exact hp.idempotent 2
    · exact hp.idempotent 1
    · exact hp.idempotent 0
  orthogonal i j hij := by
    rcases pair3_cases i j hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hp.orthogonal 2 1 (by decide)
    · exact hp.orthogonal 1 2 (by decide)
    · exact hp.orthogonal 1 0 (by decide)
    · exact hp.orthogonal 0 1 (by decide)
    · exact hp.orthogonal 0 2 (by decide)
    · exact hp.orthogonal 2 0 (by decide)
  sum_unit := by
    show p 2 + p 1 + p 0 = 1
    rw [← hp.sum_unit]
    abel

/-- `reverseFrame` is the transposition (0 2) of the outcome index, pointwise.
Duplicates `Sections.reverseFrame_eq_swap` (`Sections.lean`); see the header. -/
theorem reverseFrame_apply_swap (p : Fin 3 → Albert) (i : Fin 3) :
    reverseFrame p i = p (Equiv.swap (0 : Fin 3) 2 i) := by
  rcases fin3_cases i with rfl | rfl | rfl
  · show p 2 = p (Equiv.swap (0 : Fin 3) 2 0)
    rw [Equiv.swap_apply_left]
  · show p 1 = p (Equiv.swap (0 : Fin 3) 2 1)
    rw [Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)]
  · show p 0 = p (Equiv.swap (0 : Fin 3) 2 2)
    rw [Equiv.swap_apply_right]

/-- Relabelling the outcomes of a frame by any permutation gives a frame. -/
theorem frame_perm {p : Fin 3 → Albert} (hp : Glennie.Frame p)
    (σ : Equiv.Perm (Fin 3)) : Glennie.Frame (fun i => p (σ i)) where
  trace_one i := hp.trace_one (σ i)
  idempotent i := hp.idempotent (σ i)
  orthogonal i j hij := hp.orthogonal (σ i) (σ j) (σ.injective.ne hij)
  sum_unit := by
    have h01 : σ 0 ≠ σ 1 := σ.injective.ne (by decide)
    have h12 : σ 1 ≠ σ 2 := σ.injective.ne (by decide)
    have h02 : σ 0 ≠ σ 2 := σ.injective.ne (by decide)
    show p (σ 0) + p (σ 1) + p (σ 2) = 1
    rcases perm3_cases (σ 0) (σ 1) (σ 2) h01 h12 h02 with
      ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ |
      ⟨e0, e1, e2⟩
    all_goals (rw [e0, e1, e2, ← hp.sum_unit]; try abel)

/-- Each `mapAtoms g` is continuous: `g.equiv` is linear on a finite-dimensional
space (`Hilbert.lean` gives `FiniteDimensional ℝ Albert`, and
`Mathlib.Analysis.Normed.Module.FiniteDimension` is already in `Compactness`'s
imports at `Compactness.lean`). Used only in section 8. -/
theorem continuous_mapAtoms (g : Glennie.CompactAutomorphism) :
    Continuous (fun T : Triple => mapAtoms g T) := by
  have hg : Continuous (fun x : Albert => g.equiv x) :=
    g.equiv.toLinearMap.continuous_of_finiteDimensional
  refine continuous_pi fun a => continuous_pi fun i => ?_
  simpa only [Function.comp_def, mapAtoms_apply] using hg.comp (continuous_entry a i)

/-! ## 3. The ledger criterion

For a frame triple, equality of the complete 54-entry ledger with the flat base is
equivalent to the 27 triple traces all being `1/9`, hence — by
`frame_equality` (`Theorems/FrameEquality.lean`) — to the single scalar
condition `|Phi| = 4/27`. One lemma serves both reversals and every member of the
fibre. -/

/-- The fibre over the flat 54-entry ledger: ORDERED frame triples with that ledger. -/
def flatFibre : Set Triple :=
  {T : Triple | (∀ a : Fin 3, Glennie.Frame (T a)) ∧
    ledger54 T = ledger54 flatBaseTriple}

/-- Uniform triple traces plus frames force the whole 54-entry ledger to be the flat
one. The C block is `1/9` on both sides; the three pair blocks are `1/3` on both
sides, by `uniform_pair_blocks` (`FlatBase.lean`) and
`flatBaseTriple_ledger54_P/Q/R` (`FrameTopology.lean`). -/
theorem ledger54_eq_flat_of_uniform (T : Triple)
    (hT : ∀ a : Fin 3, Glennie.Frame (T a))
    (hu : Glennie.UniformLedger (T 0) (T 1) (T 2)) :
    ledger54 T = ledger54 flatBaseTriple := by
  have hb := uniform_pair_blocks (T 0) (T 1) (T 2) (hT 0) (hT 1) (hT 2) hu
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
  · funext i j k
    rw [ledger54_C, flatBaseTriple_ledger54_C]
    exact hu i j k
  · funext i j
    rw [ledger54_P, flatBaseTriple_ledger54_P]
    exact (hb i j).1
  · funext j k
    rw [ledger54_Q, flatBaseTriple_ledger54_Q]
    exact (hb j k).2.1
  · funext k i
    rw [ledger54_R, flatBaseTriple_ledger54_R]
    exact (hb k i).2.2

/-- The converse: projecting the C block. This is `uniform_of_full54`
(`FirstPairNormalization.lean`) restated on `T`; that one is `private`. -/
theorem uniform_of_ledger54_eq_flat (T : Triple)
    (hL : ledger54 T = ledger54 flatBaseTriple) :
    Glennie.UniformLedger (T 0) (T 1) (T 2) := by
  intro i j k
  have h : (ledger54 T).1 i j k = (ledger54 flatBaseTriple).1 i j k :=
    congrArg (fun L : Ledger54 => L.1 i j k) hL
  rw [ledger54_C, flatBaseTriple_ledger54_C] at h
  exact h

/-- THE FIBRE IS CUT OUT BY ONE SCALAR EQUATION. For a frame triple, 54-entry ledger
equality with the flat base is equivalent to `|Phi| = 4/27`. -/
theorem ledger54_eq_flat_iff_abs_phi (T : Triple)
    (hT : ∀ a : Fin 3, Glennie.Frame (T a)) :
    ledger54 T = ledger54 flatBaseTriple ↔
      |Glennie.phi (Glennie.encoder (T 0)) (Glennie.encoder (T 1))
        (Glennie.encoder (T 2))| = 4 / 27 := by
  constructor
  · intro hL
    exact (Glennie.frame_equality (T 0) (T 1) (T 2) (hT 0) (hT 1) (hT 2)).mpr
      (uniform_of_ledger54_eq_flat T hL)
  · intro hp
    exact ledger54_eq_flat_of_uniform T hT
      ((Glennie.frame_equality (T 0) (T 1) (T 2) (hT 0) (hT 1) (hT 2)).mp hp)

/-! ## 4. The two representatives

`flatBaseRev3` reverses the THIRD frame and is what the classification produces.
`flatBaseRevP` reverses the FIRST frame and is the triple the sections are
built on. Both lie in the fibre, both carry Phi = +4/27, and section 6 shows they
lie in one and the same orbit. -/

/-- The flat triple with its THIRD frame reversed. -/
def flatBaseRev3 : Triple := ![flatFrameP, flatFrameQ, reverseFrame flatFrameR]

/-- The flat triple with its FIRST frame reversed. Equal to
`Sections.revTriple Sections.flatBase`, via `flatFramePRev_eq_reverse`
(`FlatBase.lean`) and `Sections.reverseFrame_eq_swap` (`Sections.lean`), in
any module that imports `Sections`. -/
def flatBaseRevP : Triple := ![flatFramePRev, flatFrameQ, flatFrameR]

theorem flatBaseRev3_frames : ∀ a : Fin 3, Glennie.Frame (flatBaseRev3 a) := by
  intro a
  rcases fin3_cases a with rfl | rfl | rfl
  · exact flatFrameP_frame
  · exact flatFrameQ_frame
  · exact frame_reverseFrame flatFrameR_frame

theorem flatBaseRevP_frames : ∀ a : Fin 3, Glennie.Frame (flatBaseRevP a) := by
  intro a
  rcases fin3_cases a with rfl | rfl | rfl
  · exact flatFramePRev_frame
  · exact flatFrameQ_frame
  · exact flatFrameR_frame

/-- Phi at the flat base is `-4/27`. A defeq restatement of `flat_phi`
(`FlatBase.lean`); the `phiOf` spelling is `Sections.phiOf_flatBase`
(`Sections.lean`). -/
theorem phi_flatBase :
    Glennie.phi (Glennie.encoder (flatBaseTriple 0)) (Glennie.encoder (flatBaseTriple 1))
      (Glennie.encoder (flatBaseTriple 2)) = -4 / 27 := flat_phi

/-- Phi at the THIRD-frame reversal is `+4/27`. The encoder of the reversed frame is
`(-1) • encoder` by `encoder_reverseFrame`, and `phi_smul_third`
(`BasicLaws.lean`) contributes `(-1)^3`. -/
theorem phi_flatBaseRev3 :
    Glennie.phi (Glennie.encoder (flatBaseRev3 0)) (Glennie.encoder (flatBaseRev3 1))
      (Glennie.encoder (flatBaseRev3 2)) = 4 / 27 := by
  have hz : Glennie.encoder (reverseFrame flatFrameR)
      = (-1 : ℝ) • Glennie.encoder flatFrameR := by
    rw [encoder_reverseFrame, neg_one_smul]
  show Glennie.phi (Glennie.encoder flatFrameP) (Glennie.encoder flatFrameQ)
    (Glennie.encoder (reverseFrame flatFrameR)) = 4 / 27
  rw [hz, phi_smul_third, flat_phi]
  norm_num

/-- Phi at the FIRST-frame reversal is `+4/27`. A defeq restatement of `flatRev_phi`
(`FlatBase.lean`). -/
theorem phi_flatBaseRevP :
    Glennie.phi (Glennie.encoder (flatBaseRevP 0)) (Glennie.encoder (flatBaseRevP 1))
      (Glennie.encoder (flatBaseRevP 2)) = 4 / 27 := flatRev_phi

theorem uniform_flatBaseRev3 :
    Glennie.UniformLedger (flatBaseRev3 0) (flatBaseRev3 1) (flatBaseRev3 2) := by
  refine (Glennie.frame_equality (flatBaseRev3 0) (flatBaseRev3 1) (flatBaseRev3 2)
    (flatBaseRev3_frames 0) (flatBaseRev3_frames 1) (flatBaseRev3_frames 2)).mp ?_
  rw [phi_flatBaseRev3, abs_of_pos (show (0 : ℝ) < 4 / 27 by norm_num)]

/-- The second representative lies in the flat fibre. Together with the orbit separation,
this gives two distinct orbits within the fibre. -/
theorem ledger54_flatBaseRev3 : ledger54 flatBaseRev3 = ledger54 flatBaseTriple :=
  ledger54_eq_flat_of_uniform flatBaseRev3 flatBaseRev3_frames uniform_flatBaseRev3

/-- The first-frame reversal is in the fibre too, from `flatRev_uniform`
(`FlatBase.lean`). -/
theorem ledger54_flatBaseRevP : ledger54 flatBaseRevP = ledger54 flatBaseTriple :=
  ledger54_eq_flat_of_uniform flatBaseRevP flatBaseRevP_frames flatRev_uniform

theorem flatBaseTriple_mem_flatFibre : flatBaseTriple ∈ flatFibre :=
  ⟨flatBaseTriple_frames, rfl⟩

theorem flatBaseRev3_mem_flatFibre : flatBaseRev3 ∈ flatFibre :=
  ⟨flatBaseRev3_frames, ledger54_flatBaseRev3⟩

theorem flatBaseRevP_mem_flatFibre : flatBaseRevP ∈ flatFibre :=
  ⟨flatBaseRevP_frames, ledger54_flatBaseRevP⟩

/-! ## 5. The set equality

`⊆` is the classification; `⊇` is frame and ledger invariance of
the action. -/

/-- `⊇`, uniformly: any orbit of a fibre member stays in the fibre. -/
theorem autOrbit_subset_flatFibre {S : Triple}
    (hS : ∀ a : Fin 3, Glennie.Frame (S a))
    (hLS : ledger54 S = ledger54 flatBaseTriple) : autOrbit S ⊆ flatFibre := by
  rintro T ⟨g, rfl⟩
  exact ⟨fun a => frame_mapAtoms g S hS a, (ledger54_map g S).trans hLS⟩

/-- `⊆`. The only input is
`Glennie.NativeFirstPairNormalization.native_flat_full54_ordered_base_fibre`
(`FirstPairNormalization.lean`), whose hypotheses are exactly three `Frame`s and
one ledger equality: no genericity, rank, derivative or transitivity premise. -/
theorem flatFibre_subset_union :
    flatFibre ⊆ autOrbit flatBaseTriple ∪ autOrbit flatBaseRev3 := by
  rintro T ⟨hT, hL⟩
  have hL' : ledger54 ![T 0, T 1, T 2]
      = ledger54 ![flatFrameP, flatFrameQ, flatFrameR] := by
    rw [triple_eta]
    exact hL
  obtain ⟨g, h0, h1, hcase⟩ :=
    Glennie.NativeFirstPairNormalization.native_flat_full54_ordered_base_fibre
      (T 0) (T 1) (T 2) (hT 0) (hT 1) (hT 2) hL'
  rcases hcase with h2 | h2
  · refine Or.inl ⟨g.symm, ?_⟩
    have hmap : mapAtoms g T = flatBaseTriple := by
      funext a i
      rcases fin3_cases a with rfl | rfl | rfl
      · exact h0 i
      · exact h1 i
      · exact h2 i
    rw [← hmap, mapAtoms_symm_mapAtoms]
  · refine Or.inr ⟨g.symm, ?_⟩
    have hmap : mapAtoms g T = flatBaseRev3 := by
      funext a i
      rcases fin3_cases a with rfl | rfl | rfl
      · exact h0 i
      · exact h1 i
      · exact h2 i
    rw [← hmap, mapAtoms_symm_mapAtoms]

/-- THE SET EQUALITY. The fibre over the flat 54-entry ledger is EXACTLY the union of
two compact automorphism orbits. ORDERED triples throughout. -/
theorem flat_fibre_eq_two_orbits :
    flatFibre = autOrbit flatBaseTriple ∪ autOrbit flatBaseRev3 := by
  refine Set.Subset.antisymm flatFibre_subset_union ?_
  rintro T (h | h)
  · exact autOrbit_subset_flatFibre flatBaseTriple_frames rfl h
  · exact autOrbit_subset_flatFibre flatBaseRev3_frames ledger54_flatBaseRev3 h

/-- DISTINCTNESS. Phi is constant on each orbit (`phi_mapAtoms`) and takes the two
opposite values `-4/27` and `+4/27` at the two representatives, so no automorphism
carries either to the other. No genericity guard; no compactness; not the
dense-generic separation theorem, which does not apply at this point. -/
theorem flat_orbits_disjoint :
    Disjoint (autOrbit flatBaseTriple) (autOrbit flatBaseRev3) := by
  rw [Set.disjoint_left]
  intro T hT hT'
  have h1 := phi_eq_of_mem_autOrbit hT
  have h2 := phi_eq_of_mem_autOrbit hT'
  rw [phi_flatBase] at h1
  rw [phi_flatBaseRev3] at h2
  have hcontra : (-4 / 27 : ℝ) = 4 / 27 := h1.symm.trans h2
  norm_num at hcontra

/-- Both classes are non-empty and both lie inside the fibre, so "exactly two" is
justified with nothing left implicit. -/
theorem flat_fibre_two_nonempty_orbits :
    flatBaseTriple ∈ autOrbit flatBaseTriple ∧ flatBaseRev3 ∈ autOrbit flatBaseRev3 ∧
      autOrbit flatBaseTriple ⊆ flatFibre ∧ autOrbit flatBaseRev3 ⊆ flatFibre :=
  ⟨mem_autOrbit_self flatBaseTriple, mem_autOrbit_self flatBaseRev3,
    autOrbit_subset_flatFibre flatBaseTriple_frames rfl,
    autOrbit_subset_flatFibre flatBaseRev3_frames ledger54_flatBaseRev3⟩

/-! ## 6. The sharper form: each orbit is exactly one Phi sheet -/

/-- The first orbit is EXACTLY the `Phi = -4/27` part of the fibre. -/
theorem autOrbit_flatBase_eq :
    autOrbit flatBaseTriple =
      {T : Triple | T ∈ flatFibre ∧
        Glennie.phi (Glennie.encoder (T 0)) (Glennie.encoder (T 1))
          (Glennie.encoder (T 2)) = -4 / 27} := by
  refine Set.Subset.antisymm ?_ ?_
  · intro T hT
    refine ⟨autOrbit_subset_flatFibre flatBaseTriple_frames rfl hT, ?_⟩
    rw [phi_eq_of_mem_autOrbit hT, phi_flatBase]
  · rintro T ⟨hmem, hphi⟩
    rcases flatFibre_subset_union hmem with h | h
    · exact h
    · have h2 := phi_eq_of_mem_autOrbit h
      rw [phi_flatBaseRev3, hphi] at h2
      norm_num at h2

/-- The second orbit is EXACTLY the `Phi = +4/27` part of the fibre. -/
theorem autOrbit_flatBaseRev3_eq :
    autOrbit flatBaseRev3 =
      {T : Triple | T ∈ flatFibre ∧
        Glennie.phi (Glennie.encoder (T 0)) (Glennie.encoder (T 1))
          (Glennie.encoder (T 2)) = 4 / 27} := by
  refine Set.Subset.antisymm ?_ ?_
  · intro T hT
    refine ⟨autOrbit_subset_flatFibre flatBaseRev3_frames ledger54_flatBaseRev3 hT, ?_⟩
    rw [phi_eq_of_mem_autOrbit hT, phi_flatBaseRev3]
  · rintro T ⟨hmem, hphi⟩
    rcases flatFibre_subset_union hmem with h | h
    · have h1 := phi_eq_of_mem_autOrbit h
      rw [phi_flatBase, hphi] at h1
      norm_num at h1
    · exact h

/-- THE FIBRE AS A LEVEL SET. The whole 54-entry fibre is the frame triples with
`|Phi| = 4/27`, and its two sheets are the two signs. -/
theorem flat_fibre_eq_abs_phi :
    flatFibre = {T : Triple | (∀ a : Fin 3, Glennie.Frame (T a)) ∧
      |Glennie.phi (Glennie.encoder (T 0)) (Glennie.encoder (T 1))
        (Glennie.encoder (T 2))| = 4 / 27} := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro T ⟨hT, hL⟩
    exact ⟨hT, (ledger54_eq_flat_iff_abs_phi T hT).mp hL⟩
  · rintro T ⟨hT, hp⟩
    exact ⟨hT, (ledger54_eq_flat_iff_abs_phi T hT).mpr hp⟩

/-- RECONCILIATION WITH THE SECTIONS. The FIRST-frame reversal, which the
sections are built on, lies in the SAME orbit as the THIRD-frame reversal, which the
classification produces. They are different triples; they are one orbit. -/
theorem flatBaseRevP_mem_autOrbit_flatBaseRev3 :
    flatBaseRevP ∈ autOrbit flatBaseRev3 := by
  rw [autOrbit_flatBaseRev3_eq]
  exact ⟨flatBaseRevP_mem_flatFibre, phi_flatBaseRevP⟩

theorem autOrbit_flatBaseRevP_eq_autOrbit_flatBaseRev3 :
    autOrbit flatBaseRevP = autOrbit flatBaseRev3 :=
  autOrbit_eq_of_mem flatBaseRevP_mem_autOrbit_flatBaseRev3

/-! ## 7. The relabelling question

The 1296 relabellings are `Relabel` (`Relabel.lean`, `card_relabel`): a frame
order in S3 together with one outcome permutation per slot, acting by
`relabelTriple γ T a i = T (γ.order a) (γ.labels a i)` (:136), commuting with the
automorphism action (`mapAtoms_relabel` :158).

The point is that `flatBaseRev3` is `flatBaseTriple` relabelled by a SINGLE outcome
transposition inside the third frame. So modulo relabellings the flat fibre is ONE
class, not two, so the two-orbit count does not persist after quotienting by relabellings.

Phi cannot rescue the relabelled statement: `encoder p = p 2 - p 0` sees only
outcomes 0 and 2, so a relabelling by `ℓ` sends `encoder p` to `p (ℓ 2) - p (ℓ 0)`,
which is `± encoder p` only when `ℓ` fixes outcome 1. Phi is not a relabelling
invariant even up to sign, so the separation of section 6 is about ORDERED triples
and about nothing else. -/

/-- Trivial frame order; identity labels on slots 0 and 1; the transposition (0 2) of
the outcome labels on slot 2. -/
def flatRelabelThird : Relabel :=
  ⟨Equiv.refl (Fin 3),
    ![Equiv.refl (Fin 3), Equiv.refl (Fin 3), Equiv.swap (0 : Fin 3) 2]⟩

theorem flatRelabelThird_order : flatRelabelThird.order = 1 := rfl

/-- THE KEY COMPUTATION. The second representative is one outcome transposition away
from the first. -/
theorem relabelTriple_flatBaseTriple_third :
    relabelTriple flatRelabelThird flatBaseTriple = flatBaseRev3 := by
  funext a i
  rcases fin3_cases a with rfl | rfl | rfl
  · rfl
  · rfl
  · show flatFrameR (Equiv.swap (0 : Fin 3) 2 i) = reverseFrame flatFrameR i
    exact (reverseFrame_apply_swap flatFrameR i).symm

/-- Every relabelling of a frame triple is a frame triple. -/
theorem frame_relabelTriple (γ : Relabel) (T : Triple)
    (hT : ∀ a : Fin 3, Glennie.Frame (T a)) (a : Fin 3) :
    Glennie.Frame (relabelTriple γ T a) := by
  show Glennie.Frame (fun i => T (γ.order a) (γ.labels a i))
  exact frame_perm (hT (γ.order a)) (γ.labels a)

/-- The flat ledger is constant on each of the three pair blocks, so any off-diagonal
`pairExt` read of it is `1/3`. The six cases of `pair3_cases` (`Relabel.lean`)
fall in exactly the order the `pairExt` matrix literal (:236) reads
`P`, `Pᵀ`, `Q`, `Qᵀ`, `R`, `Rᵀ`. -/
theorem pairExt_flat (f g u w : Fin 3) (hfg : f ≠ g) :
    pairExt (ledger54 flatBaseTriple) f g u w = 1 / 3 := by
  rcases pair3_cases f g hfg with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact flatBaseTriple_ledger54_P u w
  · exact flatBaseTriple_ledger54_P w u
  · exact flatBaseTriple_ledger54_Q u w
  · exact flatBaseTriple_ledger54_Q w u
  · exact flatBaseTriple_ledger54_R u w
  · exact flatBaseTriple_ledger54_R w u

/-- The induced coordinate action fixes the flat ledger. `ledgerAct` (:247) is a pure
coordinate permutation of the C block and a `pairExt` read of the pair blocks, and
the flat ledger is constant on every block. -/
theorem ledgerAct_flat (γ : Relabel) :
    ledgerAct γ (ledger54 flatBaseTriple) = ledger54 flatBaseTriple := by
  have h01 : γ.order 0 ≠ γ.order 1 := γ.order.injective.ne (by decide)
  have h12 : γ.order 1 ≠ γ.order 2 := γ.order.injective.ne (by decide)
  have h20 : γ.order 2 ≠ γ.order 0 := γ.order.injective.ne (by decide)
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
  · funext i j k
    rw [ledgerAct_C, flatBaseTriple_ledger54_C, flatBaseTriple_ledger54_C]
  · funext i j
    rw [ledgerAct_P,
      pairExt_flat (γ.order 0) (γ.order 1) (γ.labels 0 i) (γ.labels 1 j) h01,
      flatBaseTriple_ledger54_P]
  · funext j k
    rw [ledgerAct_Q,
      pairExt_flat (γ.order 1) (γ.order 2) (γ.labels 1 j) (γ.labels 2 k) h12,
      flatBaseTriple_ledger54_Q]
  · funext k i
    rw [ledgerAct_R,
      pairExt_flat (γ.order 2) (γ.order 0) (γ.labels 2 k) (γ.labels 0 i) h20,
      flatBaseTriple_ledger54_R]

/-- Every relabelling of the flat triple is still in the fibre, by `ledger54_relabel`
(`Relabel.lean`). -/
theorem relabelTriple_flatBaseTriple_mem_flatFibre (γ : Relabel) :
    relabelTriple γ flatBaseTriple ∈ flatFibre := by
  refine ⟨frame_relabelTriple γ flatBaseTriple flatBaseTriple_frames, ?_⟩
  rw [ledger54_relabel, ledgerAct_flat]

/-- MODULO RELABELLINGS THE FLAT FIBRE IS ONE CLASS, NOT TWO. -/
theorem flat_fibre_eq_single_relabel_class :
    flatFibre = {T : Triple | ∃ (g : Glennie.CompactAutomorphism) (γ : Relabel),
      mapAtoms g (relabelTriple γ flatBaseTriple) = T} := by
  refine Set.Subset.antisymm ?_ ?_
  · intro T hT
    rcases flatFibre_subset_union hT with ⟨g, hg⟩ | ⟨g, hg⟩
    · exact ⟨g, 1, by rw [relabelTriple_one]; exact hg⟩
    · exact ⟨g, flatRelabelThird, by rw [relabelTriple_flatBaseTriple_third]; exact hg⟩
  · rintro T ⟨g, γ, rfl⟩
    exact autOrbit_subset_flatFibre
      (frame_relabelTriple γ flatBaseTriple flatBaseTriple_frames)
      (relabelTriple_flatBaseTriple_mem_flatFibre γ).2
      (mapAtoms_mem_autOrbit g (relabelTriple γ flatBaseTriple))

/-! ## 8. The neighbourhood of the flat ledger

`flat_fibre_no_remote_components` is UNCONDITIONAL: the set equality discharges the
premise of `flatBase_ledger_saturated` (`FrameTopology.lean`). It needs no compactness of either orbit, no
`automorphismMaps_compact`, no `compactAutomorphismOfMap`. Those would be needed only
to produce one specific small open set, not to quantify over all of them.

`nearby_fibre_rigidity_of_local` is CONDITIONAL on `LocalFlatRigidity`, stated as an
explicit named hypothesis exactly as `Rank20Reduction.rank20_of_bridge` (:77) takes
its `hT`. That hypothesis is NOT proved here and is not provable from compactness or
from the tube lemma: the tube lemma converts "contains the fibre" into "contains a
ledger-neighbourhood of it" and has no mechanism for converting proximity into
membership. It needs derivative information at the flat base, hence the rank-20
statement, hence the bridge.

What the conditional conclusion is NOT: it is rigidity over a neighbourhood (same
ledger plus same Phi implies same orbit), not "exactly two orbits over each nearby
ledger". The latter additionally needs non-emptiness of nearby fibres and a Phi
dichotomy over nearby ledger values, both of which are the two-sections statement and
are bridge-dependent. -/

/-- The automorphism saturation of an open set is open, contains it, is invariant, and
every member of it is carried into the original set by some automorphism. This is the
"free transport" step: the only non-formal ingredient is continuity of each
`mapAtoms g`, which needs `FiniteDimensional ℝ Albert` (`Hilbert.lean`). -/
theorem exists_invariant_open (U : Set Triple) (hUopen : IsOpen U) :
    ∃ W : Set Triple, IsOpen W ∧ U ⊆ W ∧
      (∀ (g : Glennie.CompactAutomorphism) (T : Triple), T ∈ W → mapAtoms g T ∈ W) ∧
      ∀ T : Triple, T ∈ W → ∃ g : Glennie.CompactAutomorphism, mapAtoms g T ∈ U := by
  refine ⟨⋃ g : Glennie.CompactAutomorphism, (fun T : Triple => mapAtoms g T) ⁻¹' U,
    isOpen_iUnion fun g => hUopen.preimage (continuous_mapAtoms g), ?_, ?_, ?_⟩
  · intro T hT
    refine Set.mem_iUnion.mpr ⟨Glennie.CompactAutomorphism.refl, ?_⟩
    show mapAtoms Glennie.CompactAutomorphism.refl T ∈ U
    rw [mapAtoms_refl]
    exact hT
  · intro g T hT
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hT
    refine Set.mem_iUnion.mpr ⟨k.comp g.symm, ?_⟩
    show mapAtoms (k.comp g.symm) (mapAtoms g T) ∈ U
    rw [← mapAtoms_comp, mapAtoms_symm_mapAtoms]
    exact hk
  · intro T hT
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hT
    exact ⟨k, hk⟩

/-- NO REMOTE COMPONENTS NEAR THE FLAT LEDGER. For every automorphism-invariant open
set containing the two representatives, some neighbourhood of the flat ledger value
has every frame triple with ledger in it already inside that set.

Honest limit: this is a containment near one ledger VALUE, not a census. It does not
say any nearby fibre is non-empty, and proximity to the two orbits is not membership
in them. -/
theorem flat_fibre_no_remote_components {W : Set Triple} (hW : IsOpen W)
    (h0 : flatBaseTriple ∈ W) (h3 : flatBaseRev3 ∈ W)
    (hinv : ∀ (g : Glennie.CompactAutomorphism) (T : Triple), T ∈ W → mapAtoms g T ∈ W) :
    ∃ V : Set Ledger54, IsOpen V ∧ ledger54 flatBaseTriple ∈ V ∧
      ∀ T : Triple, (∀ a : Fin 3, Glennie.Frame (T a)) → ledger54 T ∈ V → T ∈ W := by
  refine flatBase_ledger_saturated hW ?_
  intro T hT hL
  rcases flatFibre_subset_union ⟨hT, hL⟩ with ⟨g, hg⟩ | ⟨g, hg⟩
  · rw [← hg]
    exact hinv g flatBaseTriple h0
  · rw [← hg]
    exact hinv g flatBaseRev3 h3

/-- THE MISSING LOCAL INGREDIENT, as an explicit hypothesis. Near the flat base, two
frame triples with the same 54-entry ledger and the same Phi are automorphism
related. This is local; the conclusion of `nearby_fibre_rigidity_of_local` is over a
whole neighbourhood of the flat ledger value, so the hypothesis is strictly weaker
than that conclusion. NOT proved here. -/
def LocalFlatRigidity : Prop :=
  ∃ U : Set Triple, IsOpen U ∧ flatBaseTriple ∈ U ∧ flatBaseRev3 ∈ U ∧
    ∀ T S : Triple, (∀ a : Fin 3, Glennie.Frame (T a)) →
      (∀ a : Fin 3, Glennie.Frame (S a)) → T ∈ U → S ∈ U →
      ledger54 T = ledger54 S →
      Glennie.phi (Glennie.encoder (T 0)) (Glennie.encoder (T 1))
          (Glennie.encoder (T 2)) =
        Glennie.phi (Glennie.encoder (S 0)) (Glennie.encoder (S 1))
          (Glennie.encoder (S 2)) →
      ∃ k : Glennie.CompactAutomorphism, mapAtoms k S = T

/-- CONDITIONAL. Given local rigidity at the flat base, rigidity holds over a whole
neighbourhood of the flat ledger value: two frame triples with the same ledger in
that neighbourhood and the same Phi lie in one orbit.

The transport from the flat base point to nearby points is the free part — the
invariant open set `⋃ g, (mapAtoms g)⁻¹' U` plus the tube lemma. The hypothesis is
the hard part. -/
theorem nearby_fibre_rigidity_of_local (h : LocalFlatRigidity) :
    ∃ V : Set Ledger54, IsOpen V ∧ ledger54 flatBaseTriple ∈ V ∧
      ∀ T S : Triple, (∀ a : Fin 3, Glennie.Frame (T a)) →
        (∀ a : Fin 3, Glennie.Frame (S a)) → ledger54 T ∈ V →
        ledger54 T = ledger54 S →
        Glennie.phi (Glennie.encoder (T 0)) (Glennie.encoder (T 1))
            (Glennie.encoder (T 2)) =
          Glennie.phi (Glennie.encoder (S 0)) (Glennie.encoder (S 1))
            (Glennie.encoder (S 2)) →
        ∃ k : Glennie.CompactAutomorphism, mapAtoms k S = T := by
  obtain ⟨U, hUopen, hU0, hU3, hrig⟩ := h
  obtain ⟨W, hWopen, hUW, hWinv, hWmem⟩ := exists_invariant_open U hUopen
  obtain ⟨V, hVopen, hVmem, hVsub⟩ :=
    flat_fibre_no_remote_components hWopen (hUW hU0) (hUW hU3) hWinv
  refine ⟨V, hVopen, hVmem, ?_⟩
  intro T S hT hS hTV hLTS hPTS
  have hSV : ledger54 S ∈ V := by rw [← hLTS]; exact hTV
  obtain ⟨g, hgU⟩ := hWmem T (hVsub T hT hTV)
  obtain ⟨m, hmU⟩ := hWmem S (hVsub S hS hSV)
  obtain ⟨k, hk⟩ :=
    hrig (mapAtoms g T) (mapAtoms m S)
      (fun a => frame_mapAtoms g T hT a) (fun a => frame_mapAtoms m S hS a)
      hgU hmU
      (by rw [ledger54_map, ledger54_map, hLTS])
      (by rw [phi_mapAtoms, phi_mapAtoms, hPTS])
  refine ⟨g.symm.comp (k.comp m), ?_⟩
  calc
    mapAtoms (g.symm.comp (k.comp m)) S
        = mapAtoms g.symm (mapAtoms (k.comp m) S) := (mapAtoms_comp g.symm (k.comp m) S).symm
    _ = mapAtoms g.symm (mapAtoms k (mapAtoms m S)) :=
        congrArg (fun X : Triple => mapAtoms g.symm X) (mapAtoms_comp k m S).symm
    _ = mapAtoms g.symm (mapAtoms g T) :=
        congrArg (fun X : Triple => mapAtoms g.symm X) hk
    _ = T := mapAtoms_symm_mapAtoms g T

end
end Glennie.Compact.FlatOrbit
