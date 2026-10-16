/- Combining the exact native factor and metric budgets. -/
module
public import Glennie.UnitShifts
public import Glennie.SectorBudgets

@[expose] public section
namespace Glennie
noncomputable section

theorem phi_diagonal_complex_product_bound (a b c d e f : ℝ)
    (u v w : ℂ) (z : Albert) (ha : a+b+c=0) :
    23328*phi (diagonalAlbert a b c) (complexAlbert d e f u v w) z^2 ≤
      (inner (diagonalAlbert a b c) (diagonalAlbert a b c)*
        inner (complexAlbert d e f u v w) (complexAlbert d e f u v w)*inner z z)^3 := by
  let V := (a-b)*(b-c)*(c-a)
  let t := (u*w*star v).im
  let D := (hiddenMatrix z).det.im
  let A := inner (diagonalAlbert a b c) (diagonalAlbert a b c)
  let B := inner (complexAlbert d e f u v w) (complexAlbert d e f u v w)
  let C := inner z z
  have hv : 2*V^2 ≤ A^3 := by
    have h := ScalarEstimates.discriminant_le a b c ha
    dsimp [V,A]
    rw [diagonalAlbert_inner]
    have he : ((a-b)*(b-c)*(c-a))^2 = ((a-b)*(a-c)*(b-c))^2 := by ring
    rw [he]
    linarith
  have ht : 216*t^2 ≤ B^3 := complex_coefficient_bound d e f u v w
  have hd : 216*D^2 ≤ C^3 := hidden_determinant_bound z
  have hvt : (2*V^2)*(216*t^2) ≤ A^3*B^3 :=
    mul_le_mul hv ht (by positivity) (pow_nonneg (inner_self_nonneg _) 3)
  have hvtd : ((2*V^2)*(216*t^2))*(216*D^2) ≤ A^3*B^3*C^3 :=
    mul_le_mul hvt hd (by positivity)
      (mul_nonneg (pow_nonneg (inner_self_nonneg _) 3)
        (pow_nonneg (inner_self_nonneg _) 3))
  rw [phi_diagonal_complex_factor]
  have hfactor :
      2*(a-b)*(b-c)*(c-a)*(u*w*star v).im*(hiddenMatrix z).det.im =
        2*V*t*D := by
    dsimp [V,t,D]
    ring
  rw [hfactor]
  change 23328*(2*V*t*D)^2 ≤ (A*B*C)^3
  nlinarith [hvtd]

/-- The native product-of-norms estimate. The Gram version follows from the
proved shears and Gram–Schmidt; no orthogonality premise is hidden here. -/
theorem phi_product_bound (x y z : Albert) (hx : trace x = 0) :
    23328*phi x y z^2 ≤ (inner x x*inner y y*inner z z)^3 := by
  obtain ⟨g, hgx, hgy⟩ := universal_pair_reduction x y
  have ha : (g.equiv x).d0+(g.equiv x).d1+(g.equiv x).d2=0 := by
    change trace (g.equiv x) = 0
    rw [g.map_trace, hx]
  have h := phi_diagonal_complex_product_bound
    (g.equiv x).d0 (g.equiv x).d1 (g.equiv x).d2
    (g.equiv y).d0 (g.equiv y).d1 (g.equiv y).d2
    (complexPart (g.equiv y).o01) (complexPart (g.equiv y).o02)
    (complexPart (g.equiv y).o12) (g.equiv z) ha
  rw [diagonalAlbert_eq _ hgx, complexAlbert_eq _ hgy,
    g.phi_map, g.inner_map, g.inner_map, g.inner_map] at h
  exact h

end
end Glennie
