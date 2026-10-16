/- Q20 and compact feasible recovery. -/
module
public import Glennie.Compact.NativeQFamilyLedger
public import Glennie.Compact.LocalOrbitQuotientR01
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.UniformSpace.HeineCantor
public import Mathlib.Topology.Order.Compact

@[expose] public section
namespace Glennie.Compact.NativeQ20AdapterR01
noncomputable section
open Glennie Glennie.Compact.Affine20
open Glennie.Compact.NativeQFamilyLedger
open Glennie.Compact.NearbyOrbits
open Glennie.Compact.Sections
open Glennie.Compact.LocalOrbitQuotientR01
set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- Drop exactly the six single observations. No injectivity on arbitrary arrays. -/
def dropSingles (a : Fin 26 → ℝ) : Fin 20 → ℝ :=
  fun i => a ⟨i.val + 6, by omega⟩

/-- Reinsert (2,0,2,0,2,0) in exactly the existing Q26 positions. -/
def insertSingles (q : Fin 20 → ℝ) : Fin 26 → ℝ :=
  fun n => if h : n.val < 6 then (if n.val % 2 = 0 then 2 else 0)
    else q ⟨n.val - 6, by omega⟩

/-- All twenty positions round-trip for arbitrary serialized Q20 data. -/
theorem drop_insert (q : Fin 20 → ℝ) : dropSingles (insertSingles q) = q := by
  funext i
  fin_cases i <;> simp [dropSingles, insertSingles]

/-- Actual frames are required for the other round trip. -/
theorem insert_drop_q26 (T : Triple) (hT : ∀ a, Frame (T a)) :
    insertSingles (dropSingles (q26 T)) = q26 T := by
  funext n
  fin_cases n <;> simp [insertSingles, dropSingles, q26, qSingle_frame T hT]

/-- The twelve pair values and eight triple values, in inherited script order. -/
def q20 (T : Triple) : Fin 20 → ℝ := dropSingles (q26 T)

theorem q20_eq_of_q26_eq (T S : Triple) (h : q26 T = q26 S) :
    q20 T = q20 S := congrArg dropSingles h

/-- The six removed observations are fixed only under actual-frame hypotheses. -/
theorem q26_eq_of_q20_eq (T S : Triple)
    (hT : ∀ a, Frame (T a)) (hS : ∀ a, Frame (S a))
    (h : q20 T = q20 S) : q26 T = q26 S := by
  have hs (v : Fin 3) (s : Fin 2) : qSingle T v s = qSingle S v s := by
    rw [qSingle_frame T hT, qSingle_frame S hS]
  funext n
  fin_cases n
  · simp [q26, hs]
  · simp [q26, hs]
  · simp [q26, hs]
  · simp [q26, hs]
  · simp [q26, hs]
  · simp [q26, hs]
  · simpa [q20, dropSingles, q26] using congrFun h (0 : Fin 20)
  · simpa [q20, dropSingles, q26] using congrFun h (1 : Fin 20)
  · simpa [q20, dropSingles, q26] using congrFun h (2 : Fin 20)
  · simpa [q20, dropSingles, q26] using congrFun h (3 : Fin 20)
  · simpa [q20, dropSingles, q26] using congrFun h (4 : Fin 20)
  · simpa [q20, dropSingles, q26] using congrFun h (5 : Fin 20)
  · simpa [q20, dropSingles, q26] using congrFun h (6 : Fin 20)
  · simpa [q20, dropSingles, q26] using congrFun h (7 : Fin 20)
  · simpa [q20, dropSingles, q26] using congrFun h (8 : Fin 20)
  · simpa [q20, dropSingles, q26] using congrFun h (9 : Fin 20)
  · simpa [q20, dropSingles, q26] using congrFun h (10 : Fin 20)
  · simpa [q20, dropSingles, q26] using congrFun h (11 : Fin 20)
  · simpa [q20, dropSingles, q26] using congrFun h (12 : Fin 20)
  · simpa [q20, dropSingles, q26] using congrFun h (13 : Fin 20)
  · simpa [q20, dropSingles, q26] using congrFun h (14 : Fin 20)
  · simpa [q20, dropSingles, q26] using congrFun h (15 : Fin 20)
  · simpa [q20, dropSingles, q26] using congrFun h (16 : Fin 20)
  · simpa [q20, dropSingles, q26] using congrFun h (17 : Fin 20)
  · simpa [q20, dropSingles, q26] using congrFun h (18 : Fin 20)
  · simpa [q20, dropSingles, q26] using congrFun h (19 : Fin 20)

theorem q20_eq_iff_q26_eq (T S : Triple)
    (hT : ∀ a, Frame (T a)) (hS : ∀ a, Frame (S a)) :
    q20 T = q20 S ↔ q26 T = q26 S :=
  ⟨q26_eq_of_q20_eq T S hT hS, q20_eq_of_q26_eq T S⟩

/-- Actual ordered frame feasibility is indispensable to this equivalence. -/
theorem q20_eq_iff_ledger54_eq (T S : Triple)
    (hT : ∀ a, Frame (T a)) (hS : ∀ a, Frame (S a)) :
    q20 T = q20 S ↔ ledger54 T = ledger54 S :=
  (q20_eq_iff_q26_eq T S hT hS).trans (q26_eq_iff_ledger54_eq T S hT hS)

/-- Q20 equality and affine-chart equality agree on actual ordered frame triples.
This does not identify the twenty polynomial observations with encode20 pointwise. -/
theorem q20_eq_iff_encode20_eq (T S : Triple)
    (hT : ∀ a, Frame (T a)) (hS : ∀ a, Frame (S a)) :
    q20 T = q20 S ↔ encode20 (ledger54 T) = encode20 (ledger54 S) := by
  rw [q20_eq_iff_ledger54_eq T S hT hS]
  constructor
  · exact congrArg encode20
  · exact ledger54_eq_of_encode20_eq hT hS

/-- Here both points lie in the exact admitted local domain, with ordered atoms. -/
theorem chart_eq_iff_q20_eq (d : LocalData) (T S : Admitted d) :
    chart d T = chart d S ↔ q20 T.1 = q20 S.1 := by
  constructor
  · intro h
    exact (q20_eq_iff_encode20_eq T.1 S.1 T.2.1 S.2.1).2
      (congrArg Subtype.val h)
  · intro h
    apply Subtype.ext
    exact (q20_eq_iff_encode20_eq T.1 S.1 T.2.1 S.2.1).1 h

/-- Exact local orbit recovery needs the sign sheet in addition to Q20. -/
theorem rel_iff_q20_sheet_eq (d : LocalData) (T S : Admitted d) :
    (orbitSetoid d).r T S ↔ q20 T.1 = q20 S.1 ∧ sheet d T = sheet d S := by
  rw [rel_iff_chart_sheet_eq d T S, chart_eq_iff_q20_eq d T S]

/-- Recover the actual admitted orbit from a feasible chart and a sign. -/
def recover (d : LocalData) : d.V × Bool → OrbitQuotient d := inverse d

theorem continuous_recover (d : LocalData) : Continuous (recover d) :=
  continuous_inverse d

theorem recover_actual (d : LocalData) (T : Admitted d) :
    recover d (chart d T, sheet d T) =
      (Quotient.mk' T : OrbitQuotient d) := by
  exact inverse_forward d (Quotient.mk' T)

/-- A compact feasible ledger region has a compact recovered orbit region.
The existing quotient topology suffices; no orbit metric is postulated. -/
theorem isCompact_recovered (d : LocalData) (K : Set d.V) (hK : IsCompact K) :
    IsCompact (recover d '' (K ×ˢ (Set.univ : Set Bool))) :=
  (hK.prod isCompact_univ).image (continuous_recover d)

/-- Reconstruction restricted to a compact feasible region remains continuous.
Compactness is used by isCompact_recovered; restriction continuity itself is general. -/
def recoverOn (d : LocalData) (K : Set d.V) : K × Bool → OrbitQuotient d :=
  fun z => recover d (z.1.1, z.2)

theorem continuous_recoverOn (d : LocalData) (K : Set d.V) :
    Continuous (recoverOn d K) := by
  exact (continuous_recover d).comp
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)

/-- Branch representative with both feasible input coordinates certified by d.V. -/
def branchSection (d : LocalData) (b : d.V) (s : Bool) : Triple :=
  if s then d.pos b.1 else d.neg b.1

theorem continuous_section (d : LocalData) (s : Bool) :
    Continuous (fun b : d.V => branchSection d b s) := by
  cases s
  · change Continuous (d.V.domRestrict d.neg)
    exact d.contNeg.domRestrict
  · change Continuous (d.V.domRestrict d.pos)
    exact d.contPos.domRestrict

/-- Whole admitted fibres select the branchSection orbit by their actual sign. -/
theorem mem_section_orbit (d : LocalData) (T : Admitted d) :
    T.1 ∈ Glennie.Compact.FlatOrbit.autOrbit (branchSection d (chart d T) (sheet d T)) := by
  cases hs : sheet d T
  · simpa [branchSection, hs] using
      mem_neg_of_phi_neg d T ((sheet_false_iff d T).1 hs)
  · simpa [branchSection, hs] using
      mem_pos_of_phi_pos d T ((sheet_true_iff d T).1 hs)

/-- The existing full product-and-trace automorphism preserves the raw native norm. -/
theorem norm_automorphism (g : CompactAutomorphism) (x : Albert) :
    ‖g.equiv x‖ = ‖x‖ := by
  have hsq : ‖g.equiv x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [native_norm_sq, native_norm_sq, g.inner_map]
  nlinarith [norm_nonneg (g.equiv x), norm_nonneg x]

/-- Pi's norm on Triple is the maximum atom norm, using the native raw trace norm. -/
theorem norm_mapAtoms_sub (g : CompactAutomorphism) (T S : Triple) :
    ‖mapAtoms g T - mapAtoms g S‖ = ‖T - S‖ := by
  have hnn (x : Albert) : ‖g.equiv x‖₊ = ‖x‖₊ := by
    apply NNReal.eq
    exact norm_automorphism g x
  simp only [Pi.norm_def, Pi.nnnorm_def, mapAtoms, Pi.sub_apply, ← map_sub, hnn]

/-- Uniform branchSection recovery on compact feasible chart points, for either sign. -/
theorem compact_section_tolerance (d : LocalData) (K : Set d.V) (hK : IsCompact K)
    (ζ : ℝ) (hζ : 0 < ζ) :
    ∃ η > 0, ∀ b ∈ K, ∀ c ∈ K, ∀ s : Bool,
      dist b c < η → ‖branchSection d b s - branchSection d c s‖ < ζ := by
  have hp := hK.uniformContinuousOn_of_continuous (continuous_section d true).continuousOn
  have hn := hK.uniformContinuousOn_of_continuous (continuous_section d false).continuousOn
  obtain ⟨ηp, hηp, hp⟩ := Metric.uniformContinuousOn_iff.mp hp ζ hζ
  obtain ⟨ηn, hηn, hn⟩ := Metric.uniformContinuousOn_iff.mp hn ζ hζ
  refine ⟨min ηp ηn, lt_min hηp hηn, ?_⟩
  intro b hb c hc s hbc
  cases s
  · simpa only [dist_eq_norm] using hn b hb c hc (lt_of_lt_of_le hbc (min_le_right _ _))
  · simpa only [dist_eq_norm] using hp b hb c hc (lt_of_lt_of_le hbc (min_le_left _ _))

/-- Feasible uncertain chart recovery, modulo an actual simultaneous automorphism.
Both chart points must lie in the compact region; no array projection is supplied. -/
theorem compact_feasible_recovery (d : LocalData) (K : Set d.V) (hK : IsCompact K)
    (ζ : ℝ) (hζ : 0 < ζ) :
    ∃ η > 0, ∀ T : Admitted d, chart d T ∈ K → ∀ b : d.V, b ∈ K →
      dist (chart d T) b < η → ∃ g : CompactAutomorphism,
        ‖T.1 - mapAtoms g (branchSection d b (sheet d T))‖ < ζ := by
  obtain ⟨η, hη, ht⟩ := compact_section_tolerance d K hK ζ hζ
  refine ⟨η, hη, ?_⟩
  intro T hT b hb hdist
  obtain ⟨g, hg⟩ := mem_section_orbit d T
  refine ⟨g, ?_⟩
  rw [← hg, norm_mapAtoms_sub]
  exact ht (chart d T) hT b hb (sheet d T) hdist

/-- The compact response margin covers every actual fibre member.
No equality of the two branch magnitudes is assumed. -/
theorem compact_response_margin (d : LocalData) (K : Set d.V) (hK : IsCompact K) :
    ∃ m > 0, ∀ T : Admitted d, chart d T ∈ K → m ≤ |phiOf T.1| := by
  let fPos : d.V → ℝ := fun b => |(phiOf ∘ d.V.domRestrict d.pos) b|
  let fNeg : d.V → ℝ := fun b => |(phiOf ∘ d.V.domRestrict d.neg) b|
  have hcPos : Continuous fPos := (continuous_phiOf.comp d.contPos.domRestrict).abs
  have hcNeg : Continuous fNeg := (continuous_phiOf.comp d.contNeg.domRestrict).abs
  have hp0 : ∀ b ∈ K, 0 < fPos b := by
    intro b _
    simpa only [fPos, Function.comp_apply, Set.domRestrict_apply] using
      (abs_pos.mpr (ne_of_gt (d.phiPos b.1 b.2)))
  have hn0 : ∀ b ∈ K, 0 < fNeg b := by
    intro b _
    simpa only [fNeg, Function.comp_apply, Set.domRestrict_apply] using
      (abs_pos.mpr (ne_of_lt (d.phiNeg b.1 b.2)))
  obtain ⟨mp, hmp, hp⟩ := hK.exists_forall_le' hcPos.continuousOn hp0
  obtain ⟨mn, hmn, hn⟩ := hK.exists_forall_le' hcNeg.continuousOn hn0
  refine ⟨min mp mn, lt_min hmp hmn, ?_⟩
  intro T hT
  have heq := phiOf_eq_of_mem_autOrbit (mem_section_orbit d T)
  rw [heq]
  cases hs : sheet d T
  · have h := (min_le_right mp mn).trans (hn (chart d T) hT)
    simpa [branchSection, fNeg] using h
  · have h := (min_le_left mp mn).trans (hp (chart d T) hT)
    simpa [branchSection, fPos] using h

end
end Glennie.Compact.NativeQ20AdapterR01
