/- Native compact Albert square cone. No positivity conclusion is assumed. -/
module
public import Glennie.Diagonalization
public import Glennie.Compact.OperationalPhi

@[expose] public section
namespace Glennie.NativeSquareConeR01
open Glennie
noncomputable section
set_option autoImplicit false

/-- The actual cone of single native Jordan squares. -/
def Positive (x : Albert) : Prop := ∃ y : Albert, jordan y y = x

theorem positive_square (x : Albert) : Positive (jordan x x) := ⟨x, rfl⟩

theorem positive_zero : Positive (0 : Albert) := ⟨0, jordan_zero_left 0⟩

theorem positive_idempotent (p : Albert) (hp : jordan p p = p) : Positive p :=
  ⟨p, hp⟩

theorem positive_map (g : CompactAutomorphism) (x : Albert) (hx : Positive x) :
    Positive (g.equiv x) := by
  obtain ⟨y, rfl⟩ := hx
  exact ⟨g.equiv y, (g.map_jordan y y).symm⟩

theorem positive_map_iff (g : CompactAutomorphism) (x : Albert) :
    Positive (g.equiv x) ↔ Positive x := by
  constructor
  · intro hx
    simpa only [CompactAutomorphism.symm_apply, LinearEquiv.symm_apply_apply]
      using positive_map g.symm (g.equiv x) hx
  · exact positive_map g x

theorem square_diagonal_nonneg (y : Albert) :
    0 ≤ (jordan y y).d0 ∧ 0 ≤ (jordan y y).d1 ∧ 0 ≤ (jordan y y).d2 := by
  simp only [jordan_d0, jordan_d1, jordan_d2, octDot_self]
  exact ⟨add_nonneg (add_nonneg (mul_self_nonneg y.d0)
      (octNormSq_nonneg y.o01)) (octNormSq_nonneg y.o02),
    add_nonneg (add_nonneg (mul_self_nonneg y.d1)
      (octNormSq_nonneg y.o01)) (octNormSq_nonneg y.o12),
    add_nonneg (add_nonneg (mul_self_nonneg y.d2)
      (octNormSq_nonneg y.o02)) (octNormSq_nonneg y.o12)⟩

theorem positive_diagonal_nonneg (x : Albert) (hx : Positive x) :
    0 ≤ x.d0 ∧ 0 ≤ x.d1 ∧ 0 ≤ x.d2 := by
  obtain ⟨y, rfl⟩ := hx
  exact square_diagonal_nonneg y

theorem square_isDiagonal (x : Albert) (hx : IsDiagonal x) :
    IsDiagonal (jordan x x) := by
  rcases hx with ⟨h01, h02, h12⟩
  simp [IsDiagonal, jordan_o01, jordan_o02, jordan_o12,
    h01, h02, h12, octMul, octConj]

/-- Coordinate square root; this is where Euclidean real nonnegativity enters. -/
theorem positive_of_diagonal_nonneg (x : Albert) (hx : IsDiagonal x)
    (h0 : 0 ≤ x.d0) (h1 : 0 ≤ x.d1) (h2 : 0 ≤ x.d2) : Positive x := by
  refine ⟨⟨Real.sqrt x.d0, Real.sqrt x.d1, Real.sqrt x.d2, 0, 0, 0⟩, ?_⟩
  apply Albert.ext
  all_goals simp [jordan_d0, jordan_d1, jordan_d2, jordan_o01,
    jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj,
    octNormSq, Quaternion.normSq_def',
    ← pow_two, Real.sq_sqrt h0, Real.sq_sqrt h1, Real.sq_sqrt h2,
    hx.1, hx.2.1, hx.2.2]

theorem inner_diagonal_square_nonneg (d y : Albert) (hd : IsDiagonal d)
    (h0 : 0 ≤ d.d0) (h1 : 0 ≤ d.d1) (h2 : 0 ≤ d.d2) :
    0 ≤ inner d (jordan y y) := by
  have hy := square_diagonal_nonneg y
  have heq : inner d (jordan y y) =
      d.d0 * (jordan y y).d0 + d.d1 * (jordan y y).d1 +
        d.d2 * (jordan y y).d2 := by
    simp [inner_coordinates, hd.1, hd.2.1, hd.2.2, octDot_coordinates]
  rw [heq]
  exact add_nonneg (add_nonneg (mul_nonneg h0 hy.1)
    (mul_nonneg h1 hy.2.1)) (mul_nonneg h2 hy.2.2)

theorem inner_squares_nonneg (x y : Albert) :
    0 ≤ inner (jordan x x) (jordan y y) := by
  obtain ⟨g, hg⟩ := native_diagonalization x
  have hn := square_diagonal_nonneg (g.equiv x)
  have h := inner_diagonal_square_nonneg (jordan (g.equiv x) (g.equiv x))
    (g.equiv y) (square_isDiagonal (g.equiv x) hg) hn.1 hn.2.1 hn.2.2
  simpa only [← g.map_jordan, g.inner_map] using h

theorem inner_nonneg (x y : Albert) (hx : Positive x) (hy : Positive y) :
    0 ≤ inner x y := by
  obtain ⟨u, rfl⟩ := hx
  obtain ⟨v, rfl⟩ := hy
  exact inner_squares_nonneg u v

/-- Self-duality is proved, not included in the definition of the cone. -/
theorem positive_iff_dual_squares (x : Albert) :
    Positive x ↔ ∀ y : Albert, 0 ≤ inner x (jordan y y) := by
  constructor
  · intro hx y
    exact inner_nonneg x (jordan y y) hx (positive_square y)
  · intro h
    obtain ⟨g, hg⟩ := native_diagonalization x
    have htest (i : Fin 3) : 0 ≤ inner (g.equiv x) (standardFrame i) := by
      let p := g.symm.equiv (standardFrame i)
      have hp : jordan p p = p := by
        dsimp only [p]
        rw [← g.symm.map_jordan, standardFrame_isFrame.idempotent]
      have ht := h p
      rw [hp, ← g.inner_map x p] at ht
      simpa only [p, CompactAutomorphism.symm_apply, LinearEquiv.apply_symm_apply]
        using ht
    have h0 : 0 ≤ (g.equiv x).d0 := by
      simpa [inner_coordinates, standardFrame, octDot_coordinates] using htest 0
    have h1 : 0 ≤ (g.equiv x).d1 := by
      simpa [inner_coordinates, standardFrame, octDot_coordinates] using htest 1
    have h2 : 0 ≤ (g.equiv x).d2 := by
      simpa [inner_coordinates, standardFrame, octDot_coordinates] using htest 2
    exact (positive_map_iff g x).mp (positive_of_diagonal_nonneg _ hg h0 h1 h2)

theorem positive_add (x y : Albert) (hx : Positive x) (hy : Positive y) :
    Positive (x + y) := by
  apply (positive_iff_dual_squares (x + y)).mpr
  intro z
  rw [inner_add_left]
  exact add_nonneg ((positive_iff_dual_squares x).mp hx z)
    ((positive_iff_dual_squares y).mp hy z)

theorem positive_smul (t : ℝ) (x : Albert) (ht : 0 ≤ t) (hx : Positive x) :
    Positive (t • x) := by
  apply (positive_iff_dual_squares (t • x)).mpr
  intro z
  rw [inner_smul_left]
  exact mul_nonneg ht ((positive_iff_dual_squares x).mp hx z)

theorem positive_and_neg_eq_zero (x : Albert) (hx : Positive x)
    (hnx : Positive (-x)) : x = 0 := by
  have h := inner_nonneg x (-x) hx hnx
  rw [inner_neg_right] at h
  exact (inner_self_eq_zero x).mp (by linarith [inner_self_nonneg x])

/-- An explicit native order relation, without installing a global instance. -/
def ConeLE (x y : Albert) : Prop := Positive (y - x)

theorem coneLE_refl (x : Albert) : ConeLE x x := by
  simpa only [ConeLE, sub_self] using positive_zero

theorem coneLE_trans (x y z : Albert) (hxy : ConeLE x y) (hyz : ConeLE y z) :
    ConeLE x z := by
  have h := positive_add (y - x) (z - y) hxy hyz
  have heq : (y - x) + (z - y) = z - x := by abel
  change Positive (z - x)
  simpa only [heq] using h

theorem coneLE_antisymm (x y : Albert) (hxy : ConeLE x y) (hyx : ConeLE y x) :
    x = y := by
  have hneg : Positive (-(y - x)) := by
    change Positive (x - y) at hyx
    simpa only [neg_sub] using hyx
  have hz := positive_and_neg_eq_zero (y - x) hxy hneg
  exact (sub_eq_zero.mp hz).symm

theorem trace_nonneg (x : Albert) (hx : Positive x) : 0 ≤ trace x := by
  obtain ⟨y, rfl⟩ := hx
  exact inner_self_nonneg y

/-- A nonnegative quasi-idempotent has an explicit square root, including zero. -/
theorem positive_of_quasiIdempotent (b : Albert) (t : ℝ)
    (ht : 0 ≤ t) (hb : jordan b b = t • b) : Positive b := by
  by_cases ht0 : t = 0
  · have hs : jordan b b = 0 := by simpa [ht0] using hb
    have hi : inner b b = 0 := by rw [inner, hs, trace_zero]
    rw [(inner_self_eq_zero b).mp hi]
    exact positive_zero
  · refine ⟨(Real.sqrt t)⁻¹ • b, ?_⟩
    simp only [jordan_smul_left, jordan_smul_right, hb, smul_smul]
    simp only [← mul_assoc]
    have hc : (Real.sqrt t)⁻¹ * (Real.sqrt t)⁻¹ * t = 1 := by
      calc
        _ = (Real.sqrt t * Real.sqrt t)⁻¹ * t := by rw [mul_inv_rev]
        _ = t⁻¹ * t := by rw [← pow_two, Real.sq_sqrt ht]
        _ = 1 := inv_mul_cancel₀ ht0
    rw [hc, one_smul]

theorem U_unit_argument (a : Albert) : U a 1 = jordan a a := by
  simp only [U, jordan_unit_right]
  module

theorem trace_U (a x : Albert) : trace (U a x) = inner (jordan a a) x := by
  rw [← inner_unit_left (U a x),
    Glennie.Compact.OperationalPhi.U_pairing_selfadjoint, U_unit_argument]

/-- The order hypothesis is exactly a² ≤ 1 in the native square cone. -/
theorem trace_U_le (a x : Albert) (hx : Positive x)
    (ha : Positive ((1 : Albert) - jordan a a)) : trace (U a x) ≤ trace x := by
  have h := inner_nonneg ((1 : Albert) - jordan a a) x ha hx
  rw [inner_sub_left, inner_unit_left] at h
  rw [trace_U]
  linarith

theorem effect_pairing_bounds (e x : Albert) (he : Positive e)
    (he1 : Positive ((1 : Albert) - e)) (hx : Positive x)
    (htr : trace x ≤ 1) : 0 ≤ inner e x ∧ inner e x ≤ 1 := by
  refine ⟨inner_nonneg e x he hx, ?_⟩
  have h := inner_nonneg ((1 : Albert) - e) x he1 hx
  rw [inner_sub_left, inner_unit_left] at h
  linarith

end
end Glennie.NativeSquareConeR01
