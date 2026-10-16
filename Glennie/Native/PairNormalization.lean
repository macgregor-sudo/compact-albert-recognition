/- Explicit two-slot normalization by constructed native related triples.
All unit roots are supplied by the proved native complex-line construction.
-/
module

public import Glennie.ComplexLine

@[expose] public section

namespace Glennie
noncomputable section

set_option maxHeartbeats 2000000

/-- Two arbitrary unit octonions can be sent to the unit by an actual related triple. -/
theorem octTwoUnitSlots (p q : Octonion) (hp : octNormSq p = 1)
    (hq : octNormSq q = 1) :
    ∃ g : OctRelatedTriple, g.A p = octScalar 1 ∧ g.B q = octScalar 1 := by
  let r := octMul q (octConj p)
  have hr : octNormSq r = 1 := by
    simp [r, octNormSq_mul, hp, hq]
  obtain ⟨a, ha, _, hcancel⟩ := octUnit_normalizing_cube r hr
  let m := octMiddleTriple (octConj p) (by simpa using hp)
  let t := OctRelatedTriple.unitStabilizerTriple a ha
  refine ⟨t.comp m, ?_, ?_⟩
  · change t.A (octMul (octConj p) p) = octScalar 1
    rw [octMul_conj_self, hp]
    exact OctRelatedTriple.unitStabilizer_fix_unit a ha
  · change t.B r = octScalar 1
    rw [OctRelatedTriple.unitStabilizer_B, octMul_right_alternative]
    exact hcancel

/-- Positive scaling also includes zero, using the literal unit for that case. -/
theorem octUnit_scaling (x : Octonion) :
    ∃ a : Octonion, ∃ r : ℝ, octNormSq a = 1 ∧ 0 ≤ r ∧ x = r • a := by
  by_cases hx : x = 0
  · refine ⟨octScalar 1,0,?_,le_rfl,?_⟩
    · norm_num [octNormSq, octScalar, Quaternion.normSq_def']
    · simpa using hx
  · obtain ⟨a,r,hr,ha,hx⟩ := octUnit_decomposition x hx
    exact ⟨a,r,ha,hr.le,hx⟩

/-- Arbitrary 01 and 12 slots, including zeros, become nonnegative real slots.
The corresponding native Albert automorphism fixes every diagonal entry. -/
theorem octTwoSlotsReal (u w : Octonion) :
    ∃ g : OctRelatedTriple, ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧
      g.A u = octScalar a ∧ g.B w = octScalar b := by
  obtain ⟨p,a,hp,ha,hu⟩ := octUnit_scaling u
  obtain ⟨q,b,hq,hb,hw⟩ := octUnit_scaling w
  obtain ⟨g,hgu,hgw⟩ := octTwoUnitSlots p q hp hq
  refine ⟨g,a,b,ha,hb,?_,?_⟩
  · rw [hu,map_smul,hgu,octScalar_smul,mul_one]
  · rw [hw,map_smul,hgw,octScalar_smul,mul_one]

/-- The actual compact Albert normalization of two slots, with all degeneracies included. -/
theorem albertTwoSlotsReal (x : Albert) :
    ∃ g : CompactAutomorphism, ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧
      (g.equiv x).d0 = x.d0 ∧ (g.equiv x).d1 = x.d1 ∧
      (g.equiv x).d2 = x.d2 ∧ (g.equiv x).o01 = octScalar a ∧
      (g.equiv x).o12 = octScalar b := by
  obtain ⟨t,a,b,ha,hb,h01,h12⟩ := octTwoSlotsReal x.o01 x.o12
  exact ⟨t.compactAutomorphism,a,b,ha,hb,rfl,rfl,rfl,h01,h12⟩

end
end Glennie
