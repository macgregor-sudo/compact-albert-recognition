/- Genuine quotient topology of the admitted local ordered-frame domain by the
actual simultaneous product-and-trace automorphism action. -/
module
public import Glennie.Compact.NearbyOrbitsClosed

@[expose] public section
namespace Glennie.Compact.LocalOrbitQuotientR01
noncomputable section
open Glennie Glennie.Compact.Affine20 Glennie.Compact.FlatOrbit
open Glennie.Compact.Sections Glennie.Compact.NearbyOrbits
open Glennie.Compact.FrameTopology
set_option autoImplicit false

abbrev ChartPoint := Fin 20 → ℝ

/-- Only the exact section and whole-fibre facts needed for the quotient. -/
structure LocalData where
  V : Set ChartPoint
  openV : IsOpen V
  base : encode20 (ledger54 flatBase) ∈ V
  pos : ChartPoint → Triple
  neg : ChartPoint → Triple
  contPos : ContinuousOn pos V
  contNeg : ContinuousOn neg V
  framePos : ∀ b ∈ V, ∀ a : Fin 3, Frame (pos b a)
  frameNeg : ∀ b ∈ V, ∀ a : Fin 3, Frame (neg b a)
  chartPos : ∀ b ∈ V, encode20 (ledger54 (pos b)) = b
  chartNeg : ∀ b ∈ V, encode20 (ledger54 (neg b)) = b
  phiPos : ∀ b ∈ V, 0 < phiOf (pos b)
  phiNeg : ∀ b ∈ V, phiOf (neg b) < 0
  cover : ∀ b ∈ V, fibre54 b = autOrbit (neg b) ∪ autOrbit (pos b)

/-- The existing unconditional native two-orbit theorem supplies the exact domain. -/
theorem exists_localData : Nonempty LocalData := by
  obtain ⟨V, ho, hb, p, n, hcp, hcn, hfp, hfn, hep, hen, _, _, hpp, hnn,
    hcover, _, _⟩ := NearbyOrbitsClosed.nearby_fibres_two_orbits_unconditional
  exact ⟨⟨V, ho, hb, p, n, hcp, hcn, hfp, hfn, hep, hen, hpp, hnn, hcover⟩⟩

def localData : LocalData := Classical.choice exists_localData

/-- All actual ordered triples admitted by the chosen exact local domain. -/
abbrev Admitted (d : LocalData) :=
  {T : Triple // (∀ a : Fin 3, Frame (T a)) ∧ encode20 (ledger54 T) ∈ d.V}

/-- One actual automorphism acts simultaneously on every labeled atom. -/
def orbitSetoid (d : LocalData) : Setoid (Admitted d) where
  r T S := ∃ g : CompactAutomorphism, mapAtoms g T.1 = S.1
  iseqv := by
    constructor
    · intro T
      exact ⟨CompactAutomorphism.refl, mapAtoms_refl T.1⟩
    · intro T S h
      obtain ⟨g, hg⟩ := h
      refine ⟨g.symm, ?_⟩
      rw [← hg, mapAtoms_symm_mapAtoms]
    · intro T S R hTS hSR
      obtain ⟨g, hg⟩ := hTS
      obtain ⟨h, hh⟩ := hSR
      refine ⟨h.comp g, ?_⟩
      rw [← mapAtoms_comp, hg, hh]

abbrev OrbitQuotient (d : LocalData) := Quotient (orbitSetoid d)

instance (d : LocalData) : Setoid (Admitted d) := orbitSetoid d

/-- The explicit twenty-coordinate chart is continuous on the complete ledger. -/
theorem continuous_encode20 : Continuous (encode20 : Ledger54 → ChartPoint) := by
  apply continuous_pi
  intro i
  fin_cases i <;> dsimp [encode20, Glennie.Compact.Affine20.centred] <;> fun_prop

/-- The chart on all native triples is continuous. -/
theorem continuous_chart :
    Continuous (fun T : Triple => encode20 (ledger54 T)) :=
  continuous_encode20.comp continuous_ledger54


/-- The admitted coordinate, retaining proof that it lies in the exact V. -/
def chart (d : LocalData) (T : Admitted d) : d.V :=
  ⟨encode20 (ledger54 T.1), T.2.2⟩

/-- All admitted actual frame triples belong to the full fibre over their own chart. -/
theorem admitted_mem_fibre (d : LocalData) (T : Admitted d) :
    T.1 ∈ fibre54 (chart d T).1 := by
  exact ⟨T.2.1, NearbyOrbits.ledger54_eq_decode20 T.2.1 rfl⟩

/-- The two chosen sections really land in the entire admitted subtype. -/
def posSection (d : LocalData) (b : d.V) : Admitted d :=
  ⟨d.pos b.1, d.framePos b.1 b.2, by rw [d.chartPos b.1 b.2]; exact b.2⟩

def negSection (d : LocalData) (b : d.V) : Admitted d :=
  ⟨d.neg b.1, d.frameNeg b.1 b.2, by rw [d.chartNeg b.1 b.2]; exact b.2⟩

theorem chart_posSection (d : LocalData) (b : d.V) : chart d (posSection d b) = b := by
  apply Subtype.ext
  exact d.chartPos b.1 b.2

theorem chart_negSection (d : LocalData) (b : d.V) : chart d (negSection d b) = b := by
  apply Subtype.ext
  exact d.chartNeg b.1 b.2

/-- The whole-fibre theorem covers every admitted actual triple, not merely section images. -/
theorem admitted_cover (d : LocalData) (T : Admitted d) :
    T.1 ∈ autOrbit (d.neg (chart d T).1) ∪ autOrbit (d.pos (chart d T).1) := by
  rw [← d.cover (chart d T).1 (chart d T).2]
  exact admitted_mem_fibre d T

theorem phi_ne_zero (d : LocalData) (T : Admitted d) : phiOf T.1 ≠ 0 := by
  rcases admitted_cover d T with hn | hp
  · rw [phiOf_eq_of_mem_autOrbit hn]
    exact ne_of_lt (d.phiNeg _ (chart d T).2)
  · rw [phiOf_eq_of_mem_autOrbit hp]
    exact ne_of_gt (d.phiPos _ (chart d T).2)

/-- Sign selects the orbit within the exact admitted fibre. -/
theorem mem_pos_of_phi_pos (d : LocalData) (T : Admitted d)
    (h : 0 < phiOf T.1) : T.1 ∈ autOrbit (d.pos (chart d T).1) := by
  rcases admitted_cover d T with hn | hp
  · have heq := phiOf_eq_of_mem_autOrbit hn
    have hneg := d.phiNeg _ (chart d T).2
    linarith
  · exact hp

theorem mem_neg_of_phi_neg (d : LocalData) (T : Admitted d)
    (h : phiOf T.1 < 0) : T.1 ∈ autOrbit (d.neg (chart d T).1) := by
  rcases admitted_cover d T with hn | hp
  · exact hn
  · have heq := phiOf_eq_of_mem_autOrbit hp
    have hpos := d.phiPos _ (chart d T).2
    linarith

/-- The sign tag has no zero ambiguity anywhere in the admitted domain. -/
def sheet (d : LocalData) (T : Admitted d) : Bool := decide (0 < phiOf T.1)

theorem sheet_true_iff (d : LocalData) (T : Admitted d) :
    sheet d T = true ↔ 0 < phiOf T.1 := by
  simp [sheet]

theorem sheet_false_iff (d : LocalData) (T : Admitted d) :
    sheet d T = false ↔ phiOf T.1 < 0 := by
  simp only [sheet, decide_eq_false_iff_not]
  constructor
  · intro h
    have hn := phi_ne_zero d T
    exact lt_of_le_of_ne (le_of_not_gt h) hn
  · exact fun h => not_lt.mpr h.le

/-- Actual simultaneous automorphisms preserve both coordinate and Phi. -/
theorem chart_eq_of_rel (d : LocalData) {T S : Admitted d}
    (h : (orbitSetoid d).r T S) : chart d T = chart d S := by
  obtain ⟨g, hg⟩ := h
  apply Subtype.ext
  change encode20 (ledger54 T.1) = encode20 (ledger54 S.1)
  rw [← hg, ledger54_map]

theorem sheet_eq_of_rel (d : LocalData) {T S : Admitted d}
    (h : (orbitSetoid d).r T S) : sheet d T = sheet d S := by
  obtain ⟨g, hg⟩ := h
  simp only [sheet, ← hg, phiOf_mapAtoms]


/-- Equal chart and sheet imply an actual automorphism, using whole-fibre cover. -/
theorem rel_of_chart_sheet_eq (d : LocalData) {T S : Admitted d}
    (hc : chart d T = chart d S) (hs : sheet d T = sheet d S) :
    (orbitSetoid d).r T S := by
  by_cases hp : 0 < phiOf T.1
  · have hsT : sheet d T = true := (sheet_true_iff d T).2 hp
    have hsS : sheet d S = true := hs.symm.trans hsT
    have hpS : 0 < phiOf S.1 := (sheet_true_iff d S).1 hsS
    have hT := mem_pos_of_phi_pos d T hp
    have hS := mem_pos_of_phi_pos d S hpS
    have hS' : S.1 ∈ autOrbit (d.pos (chart d T).1) := by
      rw [hc]
      exact hS
    change S.1 ∈ autOrbit T.1
    rw [autOrbit_eq_of_mem hT]
    exact hS'
  · have hsT : sheet d T = false := by simp [sheet, hp]
    have hsS : sheet d S = false := hs.symm.trans hsT
    have hnT : phiOf T.1 < 0 := (sheet_false_iff d T).1 hsT
    have hnS : phiOf S.1 < 0 := (sheet_false_iff d S).1 hsS
    have hT := mem_neg_of_phi_neg d T hnT
    have hS := mem_neg_of_phi_neg d S hnS
    have hS' : S.1 ∈ autOrbit (d.neg (chart d T).1) := by
      rw [hc]
      exact hS
    change S.1 ∈ autOrbit T.1
    rw [autOrbit_eq_of_mem hT]
    exact hS'

/-- Thus classification is orbit equivalence, not coordinate equality by definition. -/
theorem rel_iff_chart_sheet_eq (d : LocalData) (T S : Admitted d) :
    (orbitSetoid d).r T S ↔ chart d T = chart d S ∧ sheet d T = sheet d S := by
  constructor
  · intro h
    exact ⟨chart_eq_of_rel d h, sheet_eq_of_rel d h⟩
  · rintro ⟨hc, hs⟩
    exact rel_of_chart_sheet_eq d hc hs

/-- The sign sheet is continuous because the two strict signs exhaust the domain. -/
theorem continuous_sheet (d : LocalData) : Continuous (sheet d) := by
  rw [continuous_bool_rng true]
  have hc : Continuous (fun T : Admitted d => phiOf T.1) :=
    continuous_phiOf.comp continuous_subtype_val
  have hpos : IsOpen {T : Admitted d | 0 < phiOf T.1} :=
    isOpen_lt continuous_const hc
  have hneg : IsOpen {T : Admitted d | phiOf T.1 < 0} :=
    isOpen_lt hc continuous_const
  have hpreeq : sheet d ⁻¹' ({true} : Set Bool) =
      {T : Admitted d | 0 < phiOf T.1} := by
    ext T
    simp [sheet]
  have hcompeq : (sheet d ⁻¹' ({true} : Set Bool))ᶜ =
      {T : Admitted d | phiOf T.1 < 0} := by
    ext T
    simp only [Set.mem_compl_iff, Set.mem_preimage, Set.mem_singleton_iff,
      Set.mem_setOf_eq]
    have hb : ¬ sheet d T = true ↔ sheet d T = false := by
      cases h : sheet d T <;> simp [h]
    exact hb.trans (sheet_false_iff d T)
  rw [hpreeq]
  refine ⟨?_, hpos⟩
  have hneg' : IsOpen (({T : Admitted d | 0 < phiOf T.1} : Set (Admitted d))ᶜ) := by
    rw [← hpreeq, hcompeq]
    exact hneg
  exact isOpen_compl_iff.mp hneg'

/-- The complete orbit invariant has both a continuous coordinate and a continuous sign. -/
def invariant (d : LocalData) (T : Admitted d) : d.V × Bool :=
  (chart d T, sheet d T)

theorem invariant_eq_of_rel (d : LocalData) {T S : Admitted d}
    (h : (orbitSetoid d).r T S) : invariant d T = invariant d S := by
  exact Prod.ext (chart_eq_of_rel d h) (sheet_eq_of_rel d h)

theorem continuous_invariant (d : LocalData) : Continuous (invariant d) := by
  apply Continuous.prodMk
  · exact (continuous_chart.comp continuous_subtype_val).subtype_mk _
  · exact continuous_sheet d


/-- The forward map is a lift from the actual automorphism-orbit quotient. -/
def forward (d : LocalData) : OrbitQuotient d → d.V × Bool :=
  Quotient.lift (invariant d) (fun _ _ h => invariant_eq_of_rel d h)

theorem continuous_forward (d : LocalData) : Continuous (forward d) :=
  (continuous_invariant d).quotient_lift (fun _ _ h => invariant_eq_of_rel d h)

theorem continuous_posSection (d : LocalData) : Continuous (posSection d) :=
  d.contPos.domRestrict.subtype_mk _

theorem continuous_negSection (d : LocalData) : Continuous (negSection d) :=
  d.contNeg.domRestrict.subtype_mk _

/-- The inverse uses the two actual continuous section orbits, with Bool discrete. -/
def inverse (d : LocalData) (z : d.V × Bool) : OrbitQuotient d :=
  if z.2 then Quotient.mk' (posSection d z.1) else Quotient.mk' (negSection d z.1)

theorem continuous_inverse (d : LocalData) : Continuous (inverse d) := by
  have hp : Continuous (fun b : d.V => (Quotient.mk' (posSection d b) : OrbitQuotient d)) :=
    continuous_quotient_mk'.comp (continuous_posSection d)
  have hn : Continuous (fun b : d.V => (Quotient.mk' (negSection d b) : OrbitQuotient d)) :=
    continuous_quotient_mk'.comp (continuous_negSection d)
  apply continuous_prod_of_discrete_right.mpr
  intro s
  cases s
  · simpa [inverse] using hn
  · simpa [inverse] using hp

/-- The section inverse returns exactly the requested admitted coordinate and sign. -/
theorem forward_inverse (d : LocalData) (z : d.V × Bool) :
    forward d (inverse d z) = z := by
  rcases z with ⟨b, s⟩
  cases s
  · simp only [inverse, forward, ↓reduceIte, Quotient.lift_mk]
    change invariant d (negSection d b) = (b, false)
    apply Prod.ext
    · exact chart_negSection d b
    · exact (sheet_false_iff d (negSection d b)).2 (d.phiNeg b.1 b.2)
  · simp only [inverse, forward, ↓reduceIte, Quotient.lift_mk]
    change invariant d (posSection d b) = (b, true)
    apply Prod.ext
    · exact chart_posSection d b
    · exact (sheet_true_iff d (posSection d b)).2 (d.phiPos b.1 b.2)

/-- Every quotient point is represented by the section orbit of its chart and sign. -/
theorem inverse_forward (d : LocalData) (q : OrbitQuotient d) :
    inverse d (forward d q) = q := by
  refine Quotient.inductionOn q ?_
  intro T
  by_cases hp : 0 < phiOf T.1
  · have hs : sheet d T = true := (sheet_true_iff d T).2 hp
    simp only [forward, inverse, Quotient.lift_mk, invariant, hs, ↓reduceIte]
    apply Quotient.sound
    exact mem_pos_of_phi_pos d T hp
  · have hs : sheet d T = false := by simp [sheet, hp]
    have hn : phiOf T.1 < 0 := (sheet_false_iff d T).1 hs
    simp only [forward, inverse, Quotient.lift_mk, invariant, hs, ↓reduceIte]
    apply Quotient.sound
    exact mem_neg_of_phi_neg d T hn

/-- Genuine local orbit quotient topology: exactly two signed sheets over the admitted V. -/
def localOrbitHomeomorph (d : LocalData) : OrbitQuotient d ≃ₜ d.V × Bool where
  toFun := forward d
  invFun := inverse d
  left_inv := inverse_forward d
  right_inv := forward_inverse d
  continuous_toFun := continuous_forward d
  continuous_invFun := continuous_inverse d

/-- The closed existing native theorem provides a concrete choice of the exact V. -/
def chosenLocalOrbitHomeomorph :
    OrbitQuotient localData ≃ₜ localData.V × Bool := localOrbitHomeomorph localData

end
end Glennie.Compact.LocalOrbitQuotientR01
