/- Exact real two-by-two diagonal energy improvement, including equal diagonals. -/
module
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity

@[expose] public section
namespace Glennie

theorem exists_rotation_improving_energy (a b n : ℝ) (hn : 0 < n) :
    ∃ c s : ℝ, c^2+s^2=1 ∧
      (c^2*a+s^2*b+2*c*s*n)^2 + (s^2*a+c^2*b-2*c*s*n)^2 =
        a^2+b^2+2*n^2 := by
  let D := Real.sqrt ((a-b)^2+4*n^2)
  have hrad : 0 < (a-b)^2+4*n^2 := by nlinarith [sq_nonneg (a-b)]
  have hD : 0 < D := Real.sqrt_pos.mpr hrad
  have hD2 : D^2 = (a-b)^2+4*n^2 := Real.sq_sqrt (le_of_lt hrad)
  have hp : 0 < D+(a-b) := by nlinarith
  have hm : 0 < D-(a-b) := by nlinarith
  let c := Real.sqrt ((D+(a-b))/(2*D))
  let s := Real.sqrt ((D-(a-b))/(2*D))
  have hc : 0 ≤ c := Real.sqrt_nonneg _
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hc2 : 2*D*c^2 = D+(a-b) := by
    have h := Real.sq_sqrt (le_of_lt (div_pos hp (by positivity : 0 < 2*D)))
    change c^2 = _ at h
    have h' := (eq_div_iff (by positivity : (2*D) ≠ 0)).mp h
    nlinarith
  have hs2 : 2*D*s^2 = D-(a-b) := by
    have h := Real.sq_sqrt (le_of_lt (div_pos hm (by positivity : 0 < 2*D)))
    change s^2 = _ at h
    have h' := (eq_div_iff (by positivity : (2*D) ≠ 0)).mp h
    nlinarith
  have hnorm : c^2+s^2=1 := by
    apply mul_left_cancel₀ (by positivity : (2*D) ≠ 0)
    nlinarith [hc2, hs2]
  have hprod : (2*D*c*s)^2 = (2*n)^2 := by
    calc
      _ = (2*D*c^2)*(2*D*s^2) := by ring
      _ = (D+(a-b))*(D-(a-b)) := by rw [hc2, hs2]
      _ = (2*n)^2 := by nlinarith [hD2]
  have hcs : 2*D*c*s = 2*n := by
    have hnonneg : 0 ≤ 2*D*c*s := by positivity
    nlinarith [hprod]
  let A := c^2*a+s^2*b+2*c*s*n
  let B := s^2*a+c^2*b-2*c*s*n
  have hsum : A+B = a+b := by
    change c^2*a+s^2*b+2*c*s*n + (s^2*a+c^2*b-2*c*s*n) = a+b
    calc
      _ = (c^2+s^2)*(a+b) := by ring
      _ = a+b := by rw [hnorm, one_mul]
  have hdiff : A-B = D := by
    apply mul_left_cancel₀ (by positivity : (2*D) ≠ 0)
    calc
      2*D*(A-B) = (2*D*c^2-2*D*s^2)*(a-b)+4*(2*D*c*s)*n := by
        dsimp [A, B]
        ring
      _ = ((D+(a-b))-(D-(a-b)))*(a-b)+4*(2*n)*n := by rw [hc2, hs2, hcs]
      _ = 2*D*D := by nlinarith [hD2]
  refine ⟨c, s, hnorm, ?_⟩
  change A^2+B^2 = a^2+b^2+2*n^2
  have hsquare := congrArg (fun r : ℝ => r^2) hsum
  have hdsquare := congrArg (fun r : ℝ => r^2) hdiff
  nlinarith [hsquare, hdsquare, hD2]

end Glennie
