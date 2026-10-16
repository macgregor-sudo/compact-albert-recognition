/- Invariances of the actual native scalar obtained from the proved pair
reduction and literal sector factor. No covariance conclusion is assumed. -/
module
public import Glennie.UnitShifts
public import Glennie.SectorSubspace
public import Glennie.ShearReverse

@[expose] public section
namespace Glennie
noncomputable section

theorem phi_third_add_first (x y z : Albert) (t : ℝ) :
    phi x y (z+t • x) = phi x y z := by
  obtain ⟨g, hx, hy⟩ := universal_pair_reduction x y
  rw [← g.phi_map x y (z+t • x), ← g.phi_map x y z, map_add, map_smul]
  rw [phi_of_diagonal_complex _ _ _ hx hy, phi_of_diagonal_complex _ _ _ hx hy]
  have hm : hiddenMatrix (g.equiv z+t • g.equiv x) = hiddenMatrix (g.equiv z) := by
    change hiddenMatrixLinear (g.equiv z+t • g.equiv x) = hiddenMatrixLinear (g.equiv z)
    rw [map_add, map_smul]
    change hiddenMatrix (g.equiv z)+t • hiddenMatrix (g.equiv x) = hiddenMatrix (g.equiv z)
    rw [hiddenMatrix_eq_zero _ (diagonal_inComplex _ hx), smul_zero, add_zero]
  rw [hm]

theorem phi_third_add_second (x y z : Albert) (t : ℝ) :
    phi x y (z+t • y) = phi x y z := by
  rw [phi_swap_first_two, phi_third_add_first, phi_swap_first_two, neg_neg]

theorem phi_first_add_third (x y z : Albert) (t : ℝ) :
    phi (x+t • z) y z = phi x y z := by
  apply reverse_shear_of_cubic (fun a b => phi a y b)
  · intro a b c
    refine ⟨phi a y c,
      inner (crossU a b (U y c)-U y (crossU a b c)) (U c (jordan a y))+
        inner (U a (U y c)-U y (U a c)) (U c (jordan b y)),
      inner (U b (U y c)-U y (U b c)) (U c (jordan a y))+
        inner (crossU a b (U y c)-U y (crossU a b c)) (U c (jordan b y)),
      phi b y c, fun s => ?_⟩
    rw [phi_line_first]
    ring
  · exact fun a b s => phi_smul_third s a y b
  · exact fun a b s => phi_third_add_first a y b s

theorem phi_swap_first_third (x y z : Albert) : phi z y x = -phi x y z := by
  have h1 := phi_first_add_third x y z 1
  have h2 := phi_third_add_first (x+z) y z (-1)
  have h3 := phi_first_add_third (x+z) y (-x) 1
  have ha : z+(-1 : ℝ) • (x+z) = -x := by module
  have hb : x+z+(1 : ℝ) • (-x) = z := by module
  rw [ha] at h2
  rw [hb] at h3
  simp only [one_smul] at h1
  have hn : phi z y (-x) = -phi z y x := by
    have h := phi_smul_third (-1) z y x
    rw [neg_smul, one_smul] at h
    rw [h]
    ring
  rw [hn] at h3
  linarith

theorem phi_first_add_second (x y z : Albert) (t : ℝ) :
    phi (x+t • y) y z = phi x y z := by
  rw [phi_swap_first_third, phi_third_add_second, phi_swap_first_third, neg_neg]

theorem phi_second_add_first (x y z : Albert) (t : ℝ) :
    phi x (y+t • x) z = phi x y z := by
  rw [phi_swap_first_two, phi_first_add_second, phi_swap_first_two, neg_neg]

theorem phi_second_add_third (x y z : Albert) (t : ℝ) :
    phi x (y+t • z) z = phi x y z := by
  rw [phi_swap_first_two, phi_first_add_third, phi_swap_first_two, neg_neg]


end
end Glennie
