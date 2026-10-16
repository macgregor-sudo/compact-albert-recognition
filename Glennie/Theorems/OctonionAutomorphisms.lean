module

public import Glennie.Native.Triality
public import Glennie.Native.Statements

/- Genuine compact octonion automorphisms from order-three unit stabilizers.
All multiplication is the declared octMul; the alias's inherited product is unused.
The sixth-root conjugation principle is classical (Dixon, hep-th/9604116 Eq.8).
-/

public section
namespace Glennie
noncomputable section
set_option maxHeartbeats 2000000

private theorem g2_re_add (x y : Octonion) : octRe (x+y) = octRe x+octRe y := by
  simp [octRe]
private theorem g2_re_smul (r : ℝ) (x : Octonion) : octRe (r • x) = r*octRe x := by
  simp [octRe, smul_eq_mul]
private theorem g2_re_sub (x y : Octonion) : octRe (x-y) = octRe x-octRe y := by
  simp [octRe]
private theorem g2_dot_unit_left (x : Octonion) : octDot (octScalar 1) x = octRe x := by
  simp [octDot_coordinates, octScalar, octRe]
private theorem g2_dot_unit_right (x : Octonion) : octDot x (octScalar 1) = octRe x := by
  rw [octDot_comm, g2_dot_unit_left]
private theorem g2_dot_add_right (x y z : Octonion) :
    octDot x (y+z) = octDot x y+octDot x z := by
  rw [octDot_comm, octDot_add_left, octDot_comm y x, octDot_comm z x]
private theorem g2_dot_smul_right (r : ℝ) (x y : Octonion) :
    octDot x (r • y) = r*octDot x y := by
  rw [octDot_comm, octDot_smul_left, octDot_comm y x]
private theorem g2_mul_neg_left (x y : Octonion) : octMul (-x) y = -octMul x y := by
  simpa using octMul_smul_left (-1 : ℝ) x y
private theorem g2_mul_neg_right (x y : Octonion) : octMul x (-y) = -octMul x y := by
  simpa using octMul_smul_right (-1 : ℝ) x y
private theorem g2_mul_sub_left (x y z : Octonion) :
    octMul (x-y) z = octMul x z-octMul y z := by
  simp [sub_eq_add_neg, octMul_add_left, g2_mul_neg_left]
private theorem g2_mul_sub_right (x y z : Octonion) :
    octMul x (y-z) = octMul x y-octMul x z := by
  simp [sub_eq_add_neg, octMul_add_right, g2_mul_neg_right]
private theorem g2_norm_sub (x y : Octonion) :
    octNormSq (x-y) = octNormSq x+octNormSq y-2*octDot x y := by
  simp [octNormSq, Quaternion.normSq_def', octDot_coordinates]
  ring
private theorem g2_norm_unit : octNormSq (octScalar 1) = 1 := by
  norm_num [octNormSq, octScalar, Quaternion.normSq_def']
private theorem g2_conj_formula (x : Octonion) :
    octConj x = (2*octRe x) • octScalar 1-x := by
  have h := octAdd_conj x
  rw [octScalar_smul] at h
  have h' : octConj x = octScalar (2*octRe x)-x := by
    apply eq_sub_iff_add_eq.mpr
    simpa only [add_comm] using h
  simpa only [octScalar_smul, mul_one] using h'
private theorem g2_conj_pure (x : Octonion) (hx : octRe x = 0) : octConj x = -x := by
  rw [g2_conj_formula, hx]
  simp
private theorem g2_pure_mul_re (x y : Octonion) (hx : octRe x = 0)
    (hy : octRe y = 0) : octRe (octMul x y) = -octDot x y := by
  have h : octRe (octMul x y)+octDot x y = 2*octRe x*octRe y := by
    simp [octRe, octMul, octDot_coordinates, Quaternion.re_mul]
    ring
  rw [hx, hy] at h
  linarith

/-- These equalities make the actual related triple an octonion automorphism. -/
@[expose] def DiagonalOctTriple (g : OctRelatedTriple) : Prop :=
  (∀ x, g.B x = g.A x) ∧ (∀ x, g.C x = g.A x) ∧
    g.A (octScalar 1) = octScalar 1

theorem diagonalOctTriple_mul (g : OctRelatedTriple) (hg : DiagonalOctTriple g)
    (x y : Octonion) : g.A (octMul x y) = octMul (g.A x) (g.A y) := by
  calc
    _ = g.C (octMul x y) := (hg.2.1 _).symm
    _ = octMul (g.A x) (g.B y) := (g.product x y).symm
    _ = _ := by rw [hg.1 y]

theorem diagonalOctTriple_comp (g h : OctRelatedTriple)
    (hg : DiagonalOctTriple g) (hh : DiagonalOctTriple h) :
    DiagonalOctTriple (g.comp h) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x
    change g.B (h.B x) = g.A (h.A x)
    rw [hh.1, hg.1]
  · intro x
    change g.C (h.C x) = g.A (h.A x)
    rw [hh.2.1, hg.2.1]
  · change g.A (h.A (octScalar 1)) = octScalar 1
    rw [hh.2.2, hg.2.2]

/-- No associativity is assumed: conjugate-right reassociation follows from flexibility. -/
private theorem g2_assoc_conj_right (a x : Octonion) :
    octMul a (octMul x (octConj a)) = octMul (octMul a x) (octConj a) := by
  simp only [g2_conj_formula, g2_mul_sub_right, octMul_smul_right,
    octMul_scalar_right, octMul_flexible]

/-- The actual order-three unit produces one map in all three triality slots. -/
theorem orderThree_diagonalTriple (q : Octonion) (hn : octNormSq q = 1)
    (hr : octRe q = -1 / 2) :
    DiagonalOctTriple (OctRelatedTriple.unitStabilizerTriple q hn) := by
  have hs : octMul q q = octConj q := by
    rw [octMul_self_eq, g2_conj_formula, hn, hr]
    norm_num <;> module
  exact ⟨OctRelatedTriple.unitStabilizer_B_eq_A q hn hs,
    OctRelatedTriple.unitStabilizer_C_eq_A q hn hs,
    OctRelatedTriple.unitStabilizer_fix_unit q hn⟩

/-- A fully explicit small-angle map, including x=y and dot(x,y)=-1/2. -/
theorem exists_orderThree_map (x y : Octonion) (hx : octRe x = 0)
    (hy : octRe y = 0) (hxn : octNormSq x = 1) (hyn : octNormSq y = 1)
    (ht : -(1 / 2 : ℝ) ≤ octDot x y) :
    ∃ g : OctRelatedTriple, DiagonalOctTriple g ∧ g.A x = y := by
  let t := octDot x y
  let w := x+y
  let z := octMul x y+t • octScalar 1
  let a := Real.sqrt (1+2*t)/(2*(1+t))
  let b := 1/(2*(1+t))
  let q := (-1/2 : ℝ) • octScalar 1+a • w-b • z
  have ht' : -(1 / 2 : ℝ) ≤ t := ht
  have ht0 : 1+t ≠ 0 := by linarith
  have hden : 2*(1+t) ≠ 0 := by linarith
  have hsqrt : Real.sqrt (1+2*t)^2 = 1+2*t := Real.sq_sqrt (by linarith)
  have hb : b*(1+t) = 1/2 := by dsimp [b]; field_simp [ht0] <;> ring
  have hx2 : octMul x x = (-1 : ℝ) • octScalar 1 := by
    simpa only [octScalar_smul, mul_one] using octMul_pure_unit_self x hx hxn
  have hy2 : octMul y y = (-1 : ℝ) • octScalar 1 := by
    simpa only [octScalar_smul, mul_one] using octMul_pure_unit_self y hy hyn
  have hxyre : octRe (octMul x y) = -t := g2_pure_mul_re x y hx hy
  have hyx : octMul y x = (-2*t) • octScalar 1-octMul x y := by
    calc
      _ = octConj (octMul x y) := by
        rw [octConj_mul, g2_conj_pure x hx, g2_conj_pure y hy,
          g2_mul_neg_left, g2_mul_neg_right, neg_neg]
      _ = _ := by
        rw [g2_conj_formula, hxyre]
        have hc : 2*(-t) = -2*t := by ring
        rw [hc]
  have hwre : octRe w = 0 := by dsimp only [w]; rw [g2_re_add, hx, hy]; ring
  have hzre : octRe z = 0 := by
    dsimp only [z]
    rw [g2_re_add, hxyre, g2_re_smul]
    norm_num [octRe, octScalar]
  have hwn : octNormSq w = 2+2*t := by
    dsimp only [w]
    rw [octNormSq_add, hxn, hyn]
    ring
  have hxxy : octDot x (octMul x y) = 0 := by
    rw [octDot_comm, octDot_mul_left, octMul_conj_self, hxn,
      g2_dot_unit_right, hy]
  have hyxy : octDot y (octMul x y) = 0 := by
    rw [octDot_comm, octDot_mul_right, octMul_self_conj, hyn,
      g2_dot_unit_right, hx]
  have hwz : octDot w z = 0 := by
    simp only [w, z, octDot_add_left, g2_dot_add_right, g2_dot_smul_right,
      hxxy, hyxy, g2_dot_unit_right, g2_re_add, hx, hy]
    ring
  have hzn : octNormSq z = 1-t^2 := by
    dsimp only [z]
    rw [octNormSq_add, octNormSq_mul, hxn, hyn, octNormSq_smul,
      g2_norm_unit, g2_dot_smul_right, g2_dot_unit_right, hxyre]
    ring
  have hzx : octMul z x = y-t • x := by
    simp only [z, octMul_add_left, octMul_scalar_left,
      octMul_smul_left, octMul_flexible, hyx, g2_mul_sub_right,
      octMul_smul_right, octMul_scalar_right, octMul_left_alternative, hx2]
    module
  have hyz : octMul y z = x-t • y := by
    dsimp only [z]
    rw [octMul_add_right, octMul_smul_right, octMul_scalar_right,
      ← octMul_flexible y x, hyx, g2_mul_sub_left, octMul_smul_left,
      octMul_scalar_left, octMul_right_alternative, hy2, octMul_smul_right,
      octMul_scalar_right]
    module
  have hwx : octMul w x = octMul y w := by
    dsimp only [w]
    rw [octMul_add_left, octMul_add_right, hx2, hy2]
    module
  have hqre : octRe q = -1/2 := by
    dsimp only [q]
    rw [g2_re_sub, g2_re_add, g2_re_smul, g2_re_smul, g2_re_smul, hwre, hzre]
    norm_num [octRe, octScalar]
  have hqn : octNormSq q = 1 := by
    have hQ : octNormSq q = 1/4+a^2*(2+2*t)+b^2*(1-t^2) := by
      simp only [q, g2_norm_sub, octNormSq_add, octNormSq_smul, g2_norm_unit,
        octDot_add_left, octDot_smul_left, g2_dot_smul_right,
        g2_dot_unit_left, hwre, hzre, hwz, hwn, hzn]
      ring
    rw [hQ]
    simp only [a, b, div_pow, hsqrt, one_pow]
    field_simp [hden, ht0] <;> ring
  have hqx : octMul q x = octMul y q := by
    have hdiff : octMul q x-octMul y q =
        ((-1/2 : ℝ)+b*t+b) • (x-y) := by
      simp only [q, g2_mul_sub_left, g2_mul_sub_right, octMul_add_left,
        octMul_add_right, octMul_smul_left, octMul_smul_right,
        octMul_scalar_left, octMul_scalar_right, hwx, hzx, hyz]
      module
    have hcoef : (-1/2 : ℝ)+b*t+b = 0 := by linarith [hb]
    apply sub_eq_zero.mp
    rw [hdiff, hcoef, zero_smul]
  refine ⟨OctRelatedTriple.unitStabilizerTriple q hqn,
    orderThree_diagonalTriple q hqn hqre, ?_⟩
  rw [OctRelatedTriple.unitStabilizer_A, g2_assoc_conj_right, hqx,
    octMul_conj_right_cancel, hqn, one_smul]

/-- Every prescribed imaginary unit is transported to standard i by a genuine
native octonion automorphism; the antipodal and zero-midpoint cases are covered. -/
theorem exists_octAutomorphism_to_i (I : Octonion) (hi : octRe I = 0)
    (hn : octNormSq I = 1) :
    ∃ g : OctRelatedTriple, DiagonalOctTriple g ∧ g.A I = octI := by
  have hire : octRe octI = 0 := rfl
  have hin : octNormSq octI = 1 := by
    norm_num [octI, quatI, octNormSq, Quaternion.normSq_def']
  by_cases hz : I+octI = 0
  · have hI : I = -octI := eq_neg_iff_add_eq_zero.mpr hz
    have hjre : octRe octJ = 0 := rfl
    have hjn : octNormSq octJ = 1 := by
      norm_num [octJ, quatJ, octNormSq, Quaternion.normSq_def']
    have hd1 : -(1 / 2 : ℝ) ≤ octDot I octJ := by
      norm_num [hI, octDot_coordinates, octI, octJ, quatI, quatJ]
    have hd2 : -(1 / 2 : ℝ) ≤ octDot octJ octI := by
      norm_num [octDot_coordinates, octI, octJ, quatI, quatJ]
    obtain ⟨g1, hg1, h1⟩ := exists_orderThree_map I octJ hi hjre hn hjn hd1
    obtain ⟨g2, hg2, h2⟩ := exists_orderThree_map octJ octI hjre hire hjn hin hd2
    refine ⟨g2.comp g1, diagonalOctTriple_comp g2 g1 hg2 hg1, ?_⟩
    change g2.A (g1.A I) = octI
    rw [h1, h2]
  · obtain ⟨K,r,hr,hkn,hdecomp⟩ := octUnit_decomposition (I+octI) hz
    have hre : octRe K = 0 := by
      have h := congrArg octRe hdecomp
      rw [g2_re_add, hi, hire, g2_re_smul] at h
      simp only [zero_add] at h
      exact (mul_eq_zero.mp h.symm).resolve_left (ne_of_gt hr)
    have hwpos : 0 < octNormSq (I+octI) := lt_of_le_of_ne
      (octNormSq_nonneg _) (Ne.symm (fun h => hz ((octNormSq_eq_zero _).mp h)))
    have ht : 0 < 1+octDot I octI := by
      rw [octNormSq_add, hn, hin] at hwpos
      linarith
    have hdot1 : 0 < octDot I K := by
      have h := congrArg (fun w => octDot I w) hdecomp
      rw [g2_dot_add_right, octDot_self, hn, g2_dot_smul_right] at h
      have hp : 0 < r*octDot I K := by linarith
      rcases mul_pos_iff.mp hp with hpos | hneg
      · exact hpos.2
      · linarith [hneg.1]
    have hdot2 : 0 < octDot K octI := by
      have h := congrArg (fun w => octDot w octI) hdecomp
      rw [octDot_add_left, octDot_self, hin, octDot_smul_left] at h
      have hp : 0 < r*octDot K octI := by linarith
      rcases mul_pos_iff.mp hp with hpos | hneg
      · exact hpos.2
      · linarith [hneg.1]
    obtain ⟨g1,hg1,h1⟩ := exists_orderThree_map I K hi hre hn hkn (by linarith)
    obtain ⟨g2,hg2,h2⟩ := exists_orderThree_map K octI hre hire hkn hin (by linarith)
    refine ⟨g2.comp g1, diagonalOctTriple_comp g2 g1 hg2 hg1, ?_⟩
    change g2.A (g1.A I) = octI
    rw [h1, h2]

end
end Glennie
