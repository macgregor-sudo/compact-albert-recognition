/- Four elementary topological inputs for the saturation obligation.

  * `frames_isCompact` and `frameTriples_isCompact`: the set of ordered native
    frames, and the set of frame triples, are compact. Closedness is the four
    `Frame` fields read as equalities between continuous functions of the
    atoms (`isClosed_eq` plus `isClosed_iInter`, exactly as
    `automorphismMaps_closed`). Boundedness is
    `inner (p i) (p i) = trace (jordan (p i) (p i)) = trace (p i) = 1`,
    which `native_norm_sq` turns into `‖p i‖ = 1`, so the set lies inside a
    finite product of unit closed balls; `isCompact_pi_infinite` and
    `IsCompact.of_isClosed_subset` finish, the same two steps as
    `automorphismMaps_compact`.

  * `continuous_ledger54`: the raw 54-entry ledger is continuous in the
    triple. Componentwise by `continuous_pi` and `Continuous.prodMk`, with the
    `continuous_jordan` / `continuous_native_inner` composed with the
    coordinate projections `fun T => T a i`.

  * `fibre_tube`: for compact `K`, a map continuous on `K` into a Hausdorff
    space, and an open `U` containing the WHOLE fibre `K ∩ f⁻¹' {y}`, some
    open neighbourhood `V` of `y` already satisfies `K ∩ f⁻¹' V ⊆ U`. Proved
    from Mathlib primitives only (`IsCompact.diff`,
    `IsCompact.image_of_continuousOn`, `IsCompact.isClosed`).

  * `flatBase_ledger_saturated`: the instance at the flat base. For
    every open set containing every frame triple whose 54-entry ledger equals
    the flat-base ledger, there is a neighbourhood of that ledger value in
    which every frame triple already lies in the open set. -/
module

public import Glennie.Compactness
public import Glennie.Compact.Affine20.Relabel
public import Glennie.Compact.FlatBase

@[expose] public section

namespace Glennie.Compact.FrameTopology

open Glennie Glennie.Compact.FlatBase Glennie.Compact.Affine20

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-! ## Continuity building blocks

Each of these is the `Glennie.Compactness` continuity statement
composed with a continuous map, using the `simpa only [Function.comp_def]`
idiom of `automorphismMaps_closed`. -/

/-- The native Jordan product of two continuous Albert-valued maps is
continuous. -/
theorem continuous_jordan_comp {α : Type*} [TopologicalSpace α] {f g : α → Albert}
    (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun a => Glennie.jordan (f a) (g a)) := by
  have hprod : Continuous (fun a => (f a, g a)) := hf.prodMk hg
  simpa only [Function.comp_def] using continuous_jordan.comp hprod

/-- The native trace form of two continuous Albert-valued maps is
continuous. -/
theorem continuous_inner_comp {α : Type*} [TopologicalSpace α] {f g : α → Albert}
    (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun a => Glennie.inner (f a) (g a)) := by
  have hprod : Continuous (fun a => (f a, g a)) := hf.prodMk hg
  simpa only [Function.comp_def] using continuous_native_inner.comp hprod

/-- The native trace is continuous; it is the trace form against the unit. -/
theorem continuous_trace : Continuous (fun x : Albert => Glennie.trace x) := by
  have h : Continuous (fun x : Albert => Glennie.inner x 1) :=
    continuous_inner_comp (f := fun x : Albert => x) (g := fun _ : Albert => (1 : Albert))
      continuous_id' continuous_const
  simpa only [inner_unit_right] using h

/-- The native trace of a continuous Albert-valued map is continuous. -/
theorem continuous_trace_comp {α : Type*} [TopologicalSpace α] {f : α → Albert}
    (hf : Continuous f) : Continuous (fun a => Glennie.trace (f a)) := by
  simpa only [Function.comp_def] using continuous_trace.comp hf

/-- The atoms of an ordered triple of Albert elements are continuous. -/
theorem continuous_atom (i : Fin 3) : Continuous (fun p : Fin 3 → Albert => p i) :=
  continuous_apply i

/-- The entries of a frame triple are continuous. -/
theorem continuous_entry (a i : Fin 3) : Continuous (fun T : Triple => T a i) := by
  have h1 : Continuous (fun T : Triple => T a) := continuous_apply a
  have h2 : Continuous (fun p : Fin 3 → Albert => p i) := continuous_apply i
  simpa only [Function.comp_def] using h2.comp h1

/-! ## Frames form a compact set

`Frame` is four conditions on the atoms, each an equality between continuous
functions of the atoms, so the set of frames is closed. -/

/-- The four `Frame` fields, read as an intersection of four sets. This is
bookkeeping only: it moves the structure `Frame` into the shape that
`isClosed_eq` and `isClosed_iInter` consume. -/
theorem frames_eq_inter :
    {p : Fin 3 → Albert | Frame p} =
      (⋂ i : Fin 3, {p : Fin 3 → Albert | Glennie.trace (p i) = 1}) ∩
        ((⋂ i : Fin 3, {p : Fin 3 → Albert | Glennie.jordan (p i) (p i) = p i}) ∩
          ((⋂ i : Fin 3, ⋂ j : Fin 3, ⋂ _ : i ≠ j,
              {p : Fin 3 → Albert | Glennie.jordan (p i) (p j) = 0}) ∩
            {p : Fin 3 → Albert | p 0 + p 1 + p 2 = 1})) := by
  ext p
  constructor
  · intro hp
    exact ⟨Set.mem_iInter.mpr fun i => hp.trace_one i,
      Set.mem_iInter.mpr fun i => hp.idempotent i,
      Set.mem_iInter.mpr fun i => Set.mem_iInter.mpr fun j =>
        Set.mem_iInter.mpr fun hij => hp.orthogonal i j hij,
      hp.sum_unit⟩
  · intro hp
    exact ⟨fun i => Set.mem_iInter.mp hp.1 i,
      fun i => Set.mem_iInter.mp hp.2.1 i,
      fun i j hij =>
        Set.mem_iInter.mp (Set.mem_iInter.mp (Set.mem_iInter.mp hp.2.2.1 i) j) hij,
      hp.2.2.2⟩

/-- The set of ordered native frames is closed. -/
theorem frames_isClosed : IsClosed {p : Fin 3 → Albert | Frame p} := by
  have hA : IsClosed (⋂ i : Fin 3, {p : Fin 3 → Albert | Glennie.trace (p i) = 1}) :=
    isClosed_iInter fun i =>
      isClosed_eq (continuous_trace_comp (continuous_atom i))
        (continuous_const : Continuous (fun _ : Fin 3 → Albert => (1 : ℝ)))
  have hB : IsClosed
      (⋂ i : Fin 3, {p : Fin 3 → Albert | Glennie.jordan (p i) (p i) = p i}) :=
    isClosed_iInter fun i =>
      isClosed_eq (continuous_jordan_comp (continuous_atom i) (continuous_atom i))
        (continuous_atom i)
  have hC : IsClosed (⋂ i : Fin 3, ⋂ j : Fin 3, ⋂ _ : i ≠ j,
      {p : Fin 3 → Albert | Glennie.jordan (p i) (p j) = 0}) :=
    isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
      isClosed_eq (continuous_jordan_comp (continuous_atom i) (continuous_atom j))
        (continuous_const : Continuous (fun _ : Fin 3 → Albert => (0 : Albert)))
  have hD : IsClosed {p : Fin 3 → Albert | p 0 + p 1 + p 2 = 1} :=
    isClosed_eq
      (((continuous_atom 0).fun_add (continuous_atom 1)).fun_add (continuous_atom 2))
      (continuous_const : Continuous (fun _ : Fin 3 → Albert => (1 : Albert)))
  rw [frames_eq_inter]
  exact hA.inter (hB.inter (hC.inter hD))

/-- Every atom of a frame is a native unit vector: it is an idempotent of
trace one, so `inner (p i) (p i) = trace (jordan (p i) (p i)) = trace (p i) = 1`,
and `native_norm_sq` converts that to the norm. -/
theorem frame_norm {p : Fin 3 → Albert} (hp : Frame p) (i : Fin 3) : ‖p i‖ = 1 := by
  have hsq : ‖p i‖ ^ 2 = 1 := by
    rw [native_norm_sq]
    show Glennie.trace (Glennie.jordan (p i) (p i)) = 1
    rw [hp.idempotent i]
    exact hp.trace_one i
  have h0 : (0 : ℝ) ≤ ‖p i‖ := norm_nonneg (p i)
  have hle : ‖p i‖ ≤ 1 := by nlinarith [hsq, h0]
  have hge : (1 : ℝ) ≤ ‖p i‖ := by nlinarith [hsq, h0]
  linarith

/-- The set of ordered native frames is compact. The frames sit inside a
finite product of unit closed balls, and the set is closed. -/
theorem frames_isCompact : IsCompact {p : Fin 3 → Albert | Frame p} := by
  have hball : ∀ _ : Fin 3, IsCompact (Metric.closedBall (0 : Albert) 1) :=
    fun _ => isCompact_closedBall (0 : Albert) 1
  have hb := isCompact_pi_infinite hball
  apply hb.of_isClosed_subset frames_isClosed
  intro p hp i
  simpa only [Metric.mem_closedBall, dist_zero_right] using (frame_norm hp i).le

/-- The set of frame triples is compact: it is the product of three copies of
the compact set of frames. -/
theorem frameTriples_isCompact : IsCompact {T : Triple | ∀ a, Frame (T a)} := by
  have hfib : ∀ _ : Fin 3, IsCompact {p : Fin 3 → Albert | Frame p} :=
    fun _ => frames_isCompact
  have h := isCompact_pi_infinite hfib
  exact h

/-- The set of frame triples is closed. -/
theorem frameTriples_isClosed : IsClosed {T : Triple | ∀ a, Frame (T a)} := by
  have h : {T : Triple | ∀ a, Frame (T a)} =
      ⋂ a : Fin 3, (fun T : Triple => T a) ⁻¹' {p : Fin 3 → Albert | Frame p} := by
    ext T
    exact ⟨fun hT => Set.mem_iInter.mpr fun a => hT a,
      fun hT a => Set.mem_iInter.mp hT a⟩
  rw [h]
  exact isClosed_iInter fun a => frames_isClosed.preimage (continuous_apply a)

/-! ## Continuity of the raw 54-entry ledger

`ledger54` is built only from `ledger` (a trace of a double Jordan product)
and the trace form, so continuity is componentwise. -/

/-- The 27 triple traces are continuous in the triple. -/
theorem continuous_ledger54_C :
    Continuous (fun T : Triple => Glennie.ledger (T 0) (T 1) (T 2)) := by
  refine continuous_pi fun i => continuous_pi fun j => continuous_pi fun k => ?_
  show Continuous fun T : Triple =>
    Glennie.trace (Glennie.jordan (Glennie.jordan (T 0 i) (T 1 j)) (T 2 k))
  exact continuous_trace_comp (continuous_jordan_comp
    (continuous_jordan_comp (continuous_entry 0 i) (continuous_entry 1 j))
    (continuous_entry 2 k))

/-- The P block of pair overlaps is continuous in the triple. -/
theorem continuous_ledger54_P :
    Continuous (fun T : Triple => fun i j : Fin 3 => Glennie.inner (T 0 i) (T 1 j)) :=
  continuous_pi fun i => continuous_pi fun j =>
    continuous_inner_comp (continuous_entry 0 i) (continuous_entry 1 j)

/-- The Q block of pair overlaps is continuous in the triple. -/
theorem continuous_ledger54_Q :
    Continuous (fun T : Triple => fun j k : Fin 3 => Glennie.inner (T 1 j) (T 2 k)) :=
  continuous_pi fun j => continuous_pi fun k =>
    continuous_inner_comp (continuous_entry 1 j) (continuous_entry 2 k)

/-- The R block of pair overlaps is continuous in the triple. -/
theorem continuous_ledger54_R :
    Continuous (fun T : Triple => fun k i : Fin 3 => Glennie.inner (T 2 k) (T 0 i)) :=
  continuous_pi fun k => continuous_pi fun i =>
    continuous_inner_comp (continuous_entry 2 k) (continuous_entry 0 i)

/-- The complete raw 54-entry ledger is continuous in the triple. -/
theorem continuous_ledger54 : Continuous (fun T : Triple => ledger54 T) := by
  have h := Continuous.prodMk continuous_ledger54_C
    (Continuous.prodMk continuous_ledger54_P
      (Continuous.prodMk continuous_ledger54_Q continuous_ledger54_R))
  exact h

/-! ## A self-contained fibre tube lemma

Stated and proved from Mathlib primitives only. -/

/-- Fibre tube. If `K` is compact, `f` is continuous on `K` into a Hausdorff
space, and the open set `U` contains the entire fibre `K ∩ f⁻¹' {y}`, then some
open neighbourhood `V` of `y` already satisfies `K ∩ f⁻¹' V ⊆ U`.

The proof is four moves: `K \ U` is compact; its image is compact, hence
closed because the target is Hausdorff; `y` misses that image, precisely
because the whole fibre lies in `U`; take `V` to be the complement. -/
theorem fibre_tube {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]
    {K : Set X} (hK : IsCompact K) {f : X → Y} (hf : ContinuousOn f K) {y : Y}
    {U : Set X} (hU : IsOpen U) (hsub : K ∩ f ⁻¹' {y} ⊆ U) :
    ∃ V : Set Y, IsOpen V ∧ y ∈ V ∧ K ∩ f ⁻¹' V ⊆ U := by
  have hKU : IsCompact (K \ U) := hK.diff hU
  have himg : IsCompact (f '' (K \ U)) :=
    hKU.image_of_continuousOn (hf.mono fun x hx => hx.1)
  have hy : ¬ y ∈ f '' (K \ U) := by
    intro hmem
    obtain ⟨x, hx, hfx⟩ := hmem
    exact hx.2 (hsub ⟨hx.1, hfx⟩)
  refine ⟨(f '' (K \ U))ᶜ, himg.isClosed.isOpen_compl, hy, ?_⟩
  intro x hx
  have hxK : x ∈ K := hx.1
  have hxV : ¬ f x ∈ f '' (K \ U) := hx.2
  by_contra hxU
  exact hxV (Set.mem_image_of_mem f ⟨hxK, hxU⟩)

/-! ## The instance at the flat base -/

/-- The flat base, as a frame triple. -/
def flatBaseTriple : Triple := ![flatFrameP, flatFrameQ, flatFrameR]

/-- The flat base triple is a triple of genuine native frames. -/
theorem flatBaseTriple_frames : ∀ a, Frame (flatBaseTriple a) := by
  intro a
  fin_cases a
  · exact flatFrameP_frame
  · exact flatFrameQ_frame
  · exact flatFrameR_frame

/-- All 27 triple traces of the flat base ledger are `1/9`. -/
theorem flatBaseTriple_ledger54_C (i j k : Fin 3) :
    (ledger54 flatBaseTriple).1 i j k = 1 / 9 :=
  flat_uniform i j k

/-- The P block of the flat base ledger is uniformly `1/3`. -/
theorem flatBaseTriple_ledger54_P (i j : Fin 3) :
    (ledger54 flatBaseTriple).2.1 i j = 1 / 3 :=
  (uniform_pair_blocks flatFrameP flatFrameQ flatFrameR flatFrameP_frame
    flatFrameQ_frame flatFrameR_frame flat_uniform i j).1

/-- The Q block of the flat base ledger is uniformly `1/3`. -/
theorem flatBaseTriple_ledger54_Q (j k : Fin 3) :
    (ledger54 flatBaseTriple).2.2.1 j k = 1 / 3 :=
  (uniform_pair_blocks flatFrameP flatFrameQ flatFrameR flatFrameP_frame
    flatFrameQ_frame flatFrameR_frame flat_uniform j k).2.1

/-- The R block of the flat base ledger is uniformly `1/3`. -/
theorem flatBaseTriple_ledger54_R (k i : Fin 3) :
    (ledger54 flatBaseTriple).2.2.2 k i = 1 / 3 :=
  (uniform_pair_blocks flatFrameP flatFrameQ flatFrameR flatFrameP_frame
    flatFrameQ_frame flatFrameR_frame flat_uniform k i).2.2

/-- Saturation at the flat base. If an open set of triples contains every
frame triple whose complete 54-entry ledger equals the flat base ledger, then
some open neighbourhood `V` of that ledger value has the property that every
frame triple with ledger in `V` already lies in the open set.

The hypothesis is about the one ledger value only; the conclusion is a genuine
neighbourhood of it. Nothing beyond that is asserted. -/
theorem flatBase_ledger_saturated {W : Set Triple} (hW : IsOpen W)
    (hWsub : ∀ T : Triple, (∀ a, Frame (T a)) →
      ledger54 T = ledger54 flatBaseTriple → T ∈ W) :
    ∃ V : Set Ledger54, IsOpen V ∧ ledger54 flatBaseTriple ∈ V ∧
      ∀ T : Triple, (∀ a, Frame (T a)) → ledger54 T ∈ V → T ∈ W := by
  obtain ⟨V, hVopen, hVmem, hVsub⟩ :=
    fibre_tube (K := {T : Triple | ∀ a, Frame (T a)})
      (f := fun T : Triple => ledger54 T) (y := ledger54 flatBaseTriple)
      frameTriples_isCompact continuous_ledger54.continuousOn hW
      (fun T hT => hWsub T hT.1 hT.2)
  exact ⟨V, hVopen, hVmem, fun T hT hTV => hVsub ⟨hT, hTV⟩⟩

end
end Glennie.Compact.FrameTopology
