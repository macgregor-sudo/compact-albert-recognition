/- A univariate coefficient proof of reverse shear invariance.
This is a general polynomial lemma, not an assumed native Glennie identity. -/
module
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Module.LinearMap.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith

@[expose] public section
namespace Glennie
noncomputable section

theorem reverse_shear_of_cubic {E : Type*} [AddCommGroup E] [Module ℝ E]
    (F : E → E → ℝ)
    (hline : ∀ x z v, ∃ a b c d : ℝ, ∀ t : ℝ,
      F (x + t • z) v = a + b*t + c*t^2 + d*t^3)
    (hhom : ∀ x z (t : ℝ), F x (t • z) = t^3 * F x z)
    (hforward : ∀ x z (t : ℝ), F x (z + t • x) = F x z)
    (x z : E) (t : ℝ) : F (x + t • z) z = F x z := by
  have hzero (u : E) : F u 0 = 0 := by
    simpa using hhom u 0 0
  have hdiag (u : E) : F u u = 0 := by
    simpa [hzero] using hforward u 0 1
  have hbalance (r : ℝ) : r^3 * F (x + r • z) z = -F (x + r • z) x := by
    by_cases hr : r = 0
    · simp [hr, hdiag]
    have hv : z + (-r⁻¹) • (x + r • z) = (-r⁻¹) • x := by
      simp only [smul_add, smul_smul, neg_mul, inv_mul_cancel₀ hr,
        neg_one_smul]
      abel
    calc
      r^3 * F (x + r • z) z =
          r^3 * F (x + r • z) (z + (-r⁻¹) • (x + r • z)) := by
            rw [hforward]
      _ = r^3 * ((-r⁻¹)^3 * F (x + r • z) x) := by rw [hv, hhom]
      _ = -F (x + r • z) x := by field_simp
  obtain ⟨a, b, c, d, hp⟩ := hline x z z
  obtain ⟨a', b', c', d', hq⟩ := hline x z x
  have heq (r : ℝ) : r^3 * (a + b*r + c*r^2 + d*r^3) =
      -(a' + b'*r + c'*r^2 + d'*r^3) := by
    simpa only [hp r, hq r] using hbalance r
  have ha' : a' = 0 := by simpa [hdiag] using (hq 0).symm
  have h1 := heq 1
  have hm1 := heq (-1)
  have h2 := heq 2
  have hm2 := heq (-2)
  have h3 := heq 3
  have hm3 := heq (-3)
  norm_num [ha'] at h1 hm1 h2 hm2 h3 hm3
  -- Exact interpolation of the universally established degree-six identity.
  -- These evaluations are sufficient because the cubic line expansion is proved.
  have hb : b = 0 := by linarith
  have hc : c = 0 := by linarith
  have hd : d = 0 := by linarith
  have hconstant : F x z = a := by simpa using hp 0
  rw [hp t, hb, hc, hd]
  simpa using hconstant.symm

end
end Glennie
