/- Rational coordinates on the literal compact-Albert tracefree subspace.
No norm or inner-product instance is introduced. -/
module

public import AlbertRecognition.Reference
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

@[expose] public section
namespace AlbertRecognition
noncomputable section
open Glennie

abbrev TraceFreeCoordinates := ℝ × ℝ × Octonion × Octonion × Octonion

/-- The diagonal basis is (1,-1,0),(1,1,-2), followed by the three native slots. -/
def rationalCoordinates : V ≃ₗ[ℝ] TraceFreeCoordinates where
  toFun x :=
    (((x : Albert).d0 - (x : Albert).d1) / 2,
      ((x : Albert).d0 + (x : Albert).d1) / 2,
      (x : Albert).o01, (x : Albert).o02, (x : Albert).o12)
  invFun c :=
    ⟨⟨c.1 + c.2.1, -c.1 + c.2.1, -2 * c.2.1,
      c.2.2.1, c.2.2.2.1, c.2.2.2.2⟩, by
      change (c.1 + c.2.1) + (-c.1 + c.2.1) + (-2 * c.2.1) = 0
      ring⟩
  left_inv x := by
    apply Subtype.ext
    apply Albert.ext
    · change ((x : Albert).d0 - (x : Albert).d1) / 2 +
        ((x : Albert).d0 + (x : Albert).d1) / 2 = (x : Albert).d0
      ring
    · change -(((x : Albert).d0 - (x : Albert).d1) / 2) +
        ((x : Albert).d0 + (x : Albert).d1) / 2 = (x : Albert).d1
      ring
    · change -2 * (((x : Albert).d0 + (x : Albert).d1) / 2) = (x : Albert).d2
      have htrace := trace_V x
      change (x : Albert).d0 + (x : Albert).d1 + (x : Albert).d2 = 0 at htrace
      linarith
    · rfl
    · rfl
    · rfl
  right_inv c := by
    rcases c with ⟨a, b, u, v, w⟩
    change ((a + b - (-a + b)) / 2, (a + b + (-a + b)) / 2, u, v, w) =
      (a, b, u, v, w)
    have ha : (a + b - (-a + b)) / 2 = a := by ring
    have hb : (a + b + (-a + b)) / 2 = b := by ring
    rw [ha, hb]
  map_add' x y := by
    change (((x : Albert).d0 + (y : Albert).d0 -
        ((x : Albert).d1 + (y : Albert).d1)) / 2,
      ((x : Albert).d0 + (y : Albert).d0 +
        ((x : Albert).d1 + (y : Albert).d1)) / 2,
      (x : Albert).o01 + (y : Albert).o01,
      (x : Albert).o02 + (y : Albert).o02,
      (x : Albert).o12 + (y : Albert).o12) =
      (((x : Albert).d0 - (x : Albert).d1) / 2 +
        ((y : Albert).d0 - (y : Albert).d1) / 2,
      ((x : Albert).d0 + (x : Albert).d1) / 2 +
        ((y : Albert).d0 + (y : Albert).d1) / 2,
      (x : Albert).o01 + (y : Albert).o01,
      (x : Albert).o02 + (y : Albert).o02,
      (x : Albert).o12 + (y : Albert).o12)
    have ha : ((x : Albert).d0 + (y : Albert).d0 -
        ((x : Albert).d1 + (y : Albert).d1)) / 2 =
        ((x : Albert).d0 - (x : Albert).d1) / 2 +
          ((y : Albert).d0 - (y : Albert).d1) / 2 := by ring
    have hb : ((x : Albert).d0 + (y : Albert).d0 +
        ((x : Albert).d1 + (y : Albert).d1)) / 2 =
        ((x : Albert).d0 + (x : Albert).d1) / 2 +
          ((y : Albert).d0 + (y : Albert).d1) / 2 := by ring
    rw [ha, hb]
  map_smul' r x := by
    simp only [RingHom.id_apply]
    change ((r * (x : Albert).d0 - r * (x : Albert).d1) / 2,
      (r * (x : Albert).d0 + r * (x : Albert).d1) / 2,
      r • (x : Albert).o01, r • (x : Albert).o02, r • (x : Albert).o12) =
      (r * (((x : Albert).d0 - (x : Albert).d1) / 2),
        r * (((x : Albert).d0 + (x : Albert).d1) / 2),
        r • (x : Albert).o01, r • (x : Albert).o02, r • (x : Albert).o12)
    have ha : (r * (x : Albert).d0 - r * (x : Albert).d1) / 2 =
        r * (((x : Albert).d0 - (x : Albert).d1) / 2) := by ring
    have hb : (r * (x : Albert).d0 + r * (x : Albert).d1) / 2 =
        r * (((x : Albert).d0 + (x : Albert).d1) / 2) := by ring
    rw [ha, hb]

instance : FiniteDimensional ℝ V := rationalCoordinates.symm.finiteDimensional

theorem finrank_V : Module.finrank ℝ V = 26 := by
  rw [rationalCoordinates.finrank_eq]
  simp [TraceFreeCoordinates, Octonion, Quaternion.finrank_eq_four]

end
end AlbertRecognition
