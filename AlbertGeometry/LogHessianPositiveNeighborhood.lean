/-
Continuity of the actual log-Hessian CLM and
finite-dimensional continuation of an explicitly positive base-point form.
No positivity is inferred merely from N > 0. Arbitrary homogeneous-polynomial
representation and the native norm dictionary remain separate obligations.
-/
module

public import AlbertGeometry.CubicThirdDerivative
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Module.Normalize
public import Mathlib.Topology.Order.Compact
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Tactic.Linarith

@[expose] public section

open scoped Topology
open Filter

namespace AlbertGeometry.Cubic
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Continuity of the actual DN map follows from its proved derivative. -/
theorem continuous_fderiv_diagonalCubic (P : SymmetricTrilinearForm E) :
    Continuous (fun x : E => fderiv ℝ (diagonalCubic P.form) x) := by
  exact (show Differentiable ℝ
    (fun x : E => fderiv ℝ (diagonalCubic P.form) x) from
      fun x => (hasFDerivAt_fderiv_diagonalCubic_actual P x).differentiableAt).continuous

/-- The reciprocal derivative is continuous at each actual positive point. -/
theorem continuousAt_inverseCubicDerivative (P : SymmetricTrilinearForm E) {x : E}
    (hx : 0 < diagonalCubic P.form x) :
    ContinuousAt (inverseCubicDerivative P) x := by
  have hN := (differentiable_diagonalCubic P.form).continuous.continuousAt (x := x)
  have hD := (continuous_fderiv_diagonalCubic P).continuousAt (x := x)
  change ContinuousAt
    (fun z : E => (-(diagonalCubic P.form z ^ 2)⁻¹) •
      fderiv ℝ (diagonalCubic P.form) z) x
  exact ((hN.pow 2).inv₀ (pow_ne_zero 2 (ne_of_gt hx))).neg.smul hD

/-- CLM-valued continuity of the derivative-certified rational formula. -/
theorem continuousAt_logHessianFormula (P : SymmetricTrilinearForm E) {x : E}
    (hx : 0 < diagonalCubic P.form x) :
    ContinuousAt (logHessianFormula P) x := by
  letI : NormedAddCommGroup (E →L[ℝ] ℝ) :=
    ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
      (E := E) (F := ℝ) (σ₁₂ := RingHom.id ℝ)
  letI : NormedSpace ℝ (E →L[ℝ] ℝ) :=
    ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℝ)
      (E := E) (F := ℝ) (σ₁₂ := RingHom.id ℝ)
  letI : IsTopologicalAddGroup (E →L[ℝ] ℝ) :=
    ContinuousLinearMap.isTopologicalAddGroup (𝕜₁ := ℝ) (𝕜₂ := ℝ)
      (E := E) (F := ℝ) (σ := RingHom.id ℝ)
  letI : ContinuousAdd (E →L[ℝ] ℝ) :=
    (inferInstance : IsTopologicalAddGroup (E →L[ℝ] ℝ)).toContinuousAdd
  letI : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
    ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
      (E := E) (F := E →L[ℝ] ℝ) (σ₁₂ := RingHom.id ℝ)
  letI : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
    ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℝ)
      (E := E) (F := E →L[ℝ] ℝ) (σ₁₂ := RingHom.id ℝ)
  letI : IsTopologicalAddGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
    ContinuousLinearMap.isTopologicalAddGroup (𝕜₁ := ℝ) (𝕜₂ := ℝ)
      (E := E) (F := E →L[ℝ] ℝ) (σ := RingHom.id ℝ)
  letI : ContinuousAdd (E →L[ℝ] E →L[ℝ] ℝ) :=
    (inferInstance : IsTopologicalAddGroup (E →L[ℝ] E →L[ℝ] ℝ)).toContinuousAdd
  letI : ContinuousSub (E →L[ℝ] E →L[ℝ] ℝ) :=
    IsTopologicalAddGroup.to_continuousSub (G := E →L[ℝ] E →L[ℝ] ℝ)
  have hN := (differentiable_diagonalCubic P.form).continuous.continuousAt (x := x)
  have hD := (continuous_fderiv_diagonalCubic P).continuousAt (x := x)
  have hH := (differentiable_cubicHessian P).continuous.continuousAt (x := x)
  have hI := continuousAt_inverseCubicDerivative P hx
  have hR : ContinuousAt
      (fun z : E => (inverseCubicDerivative P z).smulRight
        (fderiv ℝ (diagonalCubic P.form) z)) x :=
    ((ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)).continuous.continuousAt.comp
      hI).clm_apply hD
  have hS : ContinuousAt
      (fun z : E => (diagonalCubic P.form z)⁻¹ • cubicHessian P z) x :=
    ContinuousAt.smul (M := ℝ) (X := E →L[ℝ] E →L[ℝ] ℝ) (Y := E)
      (hN.inv₀ (ne_of_gt hx)) hH
  exact ContinuousAt.add (M := E →L[ℝ] E →L[ℝ] ℝ) (X := E) hS hR

/-- The identity is used on a proved positive neighborhood before transporting
continuity to the actual second derivative of log N. -/
theorem continuousAt_logHessian (P : SymmetricTrilinearForm E) {x : E}
    (hx : 0 < diagonalCubic P.form x) :
    ContinuousAt (logHessian P) x :=
  (continuousAt_logHessianFormula P hx).congr_of_eventuallyEq
    ((eventually_positive P hx).mono (fun z hz => logHessian_eq_formula P hz))

theorem continuousAt_logHessianForm (P : SymmetricTrilinearForm E) {x : E}
    (hx : 0 < diagonalCubic P.form x) :
    ContinuousAt (logHessianForm P) x := by
  change ContinuousAt (fun z : E => (-1 / 3 : ℝ) • logHessian P z) x
  exact ContinuousAt.smul (M := ℝ) (X := E →L[ℝ] E →L[ℝ] ℝ) (Y := E)
    (show ContinuousAt (fun _ : E => (-1 / 3 : ℝ)) x from continuousAt_const)
    (continuousAt_logHessian P hx)

theorem continuousOn_logHessianForm_positiveLocus (P : SymmetricTrilinearForm E) :
    ContinuousOn (logHessianForm P) (positiveLocus P) := by
  intro x hx
  exact (continuousAt_logHessianForm P hx).continuousWithinAt

/-- Actual continuous bilinear forms have a uniform strictly positive lower
bound on a finite-dimensional space when positive on every nonzero vector.
The compact minimum theorem also handles the empty sphere without division. -/
theorem exists_coercivity_of_positive [FiniteDimensional ℝ E]
    (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hB : ∀ u : E, u ≠ 0 → 0 < B u u) :
    ∃ c : ℝ, 0 < c ∧ ∀ u : E, c * ‖u‖ ^ 2 ≤ B u u := by
  letI : ProperSpace E := FiniteDimensional.proper ℝ E
  have hq : Continuous (fun u : E => B u u) :=
    B.continuous.clm_apply continuous_id
  obtain ⟨c, hc, hmin⟩ := (isCompact_sphere (0 : E) 1).exists_forall_le'
    hq.continuousOn (show ∀ u ∈ Metric.sphere (0 : E) 1, (0 : ℝ) < B u u from by
      intro u hu
      have hn : ‖u‖ = 1 := by simpa [Metric.mem_sphere, dist_eq_norm] using hu
      apply hB u
      intro hzero
      simpa [hzero] using hn)
  refine ⟨c, hc, fun u => ?_⟩
  by_cases hu : u = 0
  · simp [hu]
  · have hn : ‖NormedSpace.normalize u‖ = 1 := NormedSpace.norm_normalize hu
    have hs : NormedSpace.normalize u ∈ Metric.sphere (0 : E) 1 := by
      simpa [Metric.mem_sphere, dist_eq_norm] using hn
    have hm := hmin (NormedSpace.normalize u) hs
    have heq : B u u = ‖u‖ ^ 2 *
        B (NormedSpace.normalize u) (NormedSpace.normalize u) := by
      calc
        B u u = B (‖u‖ • NormedSpace.normalize u)
            (‖u‖ • NormedSpace.normalize u) := by
              simp only [NormedSpace.norm_smul_normalize]
        _ = ‖u‖ ^ 2 * B (NormedSpace.normalize u)
            (NormedSpace.normalize u) := by
              simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
              ring
    rw [heq]
    have hb := mul_le_mul_of_nonneg_left hm (sq_nonneg ‖u‖)
    simpa only [mul_comm c (‖u‖ ^ 2)] using hb

/-- Operator-norm perturbation controls the genuine quadratic evaluation; no
matrix norm, inherited Pi norm or unproved Euclidean norm dictionary is used. -/
theorem coercivity_of_operatorNorm_perturbation
    (B₀ B : E →L[ℝ] E →L[ℝ] ℝ) (c : ℝ)
    (hbase : ∀ u : E, c * ‖u‖ ^ 2 ≤ B₀ u u)
    (hnear : ‖B - B₀‖ < c / 2) :
    ∀ u : E, (c / 2) * ‖u‖ ^ 2 ≤ B u u := by
  intro u
  have hnorm : |B u u - B₀ u u| ≤ ‖B - B₀‖ * ‖u‖ * ‖u‖ := by
    simpa only [ContinuousLinearMap.sub_apply, Real.norm_eq_abs] using
      (B - B₀).le_opNorm₂ u u
  have hdiff := (abs_le.mp hnorm).1
  have hsmall := mul_le_mul_of_nonneg_right (le_of_lt hnear) (sq_nonneg ‖u‖)
  have hzero := hbase u
  nlinarith

/-- A single open neighborhood has both actual N > 0 and a uniform positive
lower bound for the actual normalized ambient log-Hessian. Base-point positive
definiteness is the original explicit input, never a consequence of N > 0. -/
theorem exists_uniform_positive_logHessian_neighborhood [FiniteDimensional ℝ E]
    (P : SymmetricTrilinearForm E) (e : E)
    (hN : 0 < diagonalCubic P.form e)
    (hpos : ∀ u : E, u ≠ 0 → 0 < logHessianForm P e u u) :
    ∃ c : ℝ, 0 < c ∧ ∃ U : Set E, IsOpen U ∧ e ∈ U ∧
      ∀ x ∈ U, 0 < diagonalCubic P.form x ∧
        ∀ u : E, c * ‖u‖ ^ 2 ≤ logHessianForm P x u u := by
  letI : NormedAddCommGroup (E →L[ℝ] ℝ) :=
    ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
      (E := E) (F := ℝ) (σ₁₂ := RingHom.id ℝ)
  letI : NormedSpace ℝ (E →L[ℝ] ℝ) :=
    ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℝ)
      (E := E) (F := ℝ) (σ₁₂ := RingHom.id ℝ)
  letI : IsTopologicalAddGroup (E →L[ℝ] ℝ) :=
    ContinuousLinearMap.isTopologicalAddGroup (𝕜₁ := ℝ) (𝕜₂ := ℝ)
      (E := E) (F := ℝ) (σ := RingHom.id ℝ)
  letI : ContinuousAdd (E →L[ℝ] ℝ) :=
    (inferInstance : IsTopologicalAddGroup (E →L[ℝ] ℝ)).toContinuousAdd
  letI : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
    ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
      (E := E) (F := E →L[ℝ] ℝ) (σ₁₂ := RingHom.id ℝ)
  letI : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
    ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℝ)
      (E := E) (F := E →L[ℝ] ℝ) (σ₁₂ := RingHom.id ℝ)
  letI : IsTopologicalAddGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
    ContinuousLinearMap.isTopologicalAddGroup (𝕜₁ := ℝ) (𝕜₂ := ℝ)
      (E := E) (F := E →L[ℝ] ℝ) (σ := RingHom.id ℝ)
  letI : ContinuousAdd (E →L[ℝ] E →L[ℝ] ℝ) :=
    (inferInstance : IsTopologicalAddGroup (E →L[ℝ] E →L[ℝ] ℝ)).toContinuousAdd
  letI : ContinuousSub (E →L[ℝ] E →L[ℝ] ℝ) :=
    IsTopologicalAddGroup.to_continuousSub (G := E →L[ℝ] E →L[ℝ] ℝ)
  obtain ⟨c, hc, hbase⟩ := exists_coercivity_of_positive (logHessianForm P e) hpos
  have hcont : ContinuousAt
      (fun x : E => ‖logHessianForm P x - logHessianForm P e‖) e :=
    (ContinuousAt.sub (G := E →L[ℝ] E →L[ℝ] ℝ) (X := E)
      (continuousAt_logHessianForm P hN)
      (show ContinuousAt (fun _ : E => logHessianForm P e) e from
        continuousAt_const)).norm
  have hnear : ∀ᶠ x in 𝓝 e,
      ‖logHessianForm P x - logHessianForm P e‖ < c / 2 :=
    hcont.eventually_lt
      (show ContinuousAt (fun _ : E => (c / 2 : ℝ)) e from continuousAt_const)
      (by
        have hzero : logHessianForm P e - logHessianForm P e =
            (0 : E →L[ℝ] E →L[ℝ] ℝ) := by
          apply ContinuousLinearMap.ext
          intro u
          apply ContinuousLinearMap.ext
          intro v
          simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.zero_apply]
          exact sub_self (logHessianForm P e u v)
        rw [hzero, ContinuousLinearMap.opNorm_zero]
        exact half_pos hc)
  have hlocal : ∀ᶠ x in 𝓝 e, 0 < diagonalCubic P.form x ∧
      ∀ u : E, (c / 2) * ‖u‖ ^ 2 ≤ logHessianForm P x u u :=
    ((eventually_positive P hN).and hnear).mono (fun x hx =>
      ⟨hx.1, coercivity_of_operatorNorm_perturbation
        (logHessianForm P e) (logHessianForm P x) c hbase hx.2⟩)
  obtain ⟨U, hU, hOpen, heU⟩ := eventually_nhds_iff.mp hlocal
  exact ⟨c / 2, half_pos hc, U, hOpen, heU, hU⟩

/-- Strict positivity of every nonzero vector throughout a common open set,
with symmetry supplied by the true log-Hessian formula on that set. -/
theorem exists_positive_definite_logHessian_neighborhood [FiniteDimensional ℝ E]
    (P : SymmetricTrilinearForm E) (e : E)
    (hN : 0 < diagonalCubic P.form e)
    (hpos : ∀ u : E, u ≠ 0 → 0 < logHessianForm P e u u) :
    ∃ U : Set E, IsOpen U ∧ e ∈ U ∧ ∀ x ∈ U,
      0 < diagonalCubic P.form x ∧
      (∀ u v : E, logHessianForm P x u v = logHessianForm P x v u) ∧
      ∀ u : E, u ≠ 0 → 0 < logHessianForm P x u u := by
  obtain ⟨c, hc, U, hOpen, heU, hU⟩ :=
    exists_uniform_positive_logHessian_neighborhood P e hN hpos
  refine ⟨U, hOpen, heU, fun x hx => ?_⟩
  obtain ⟨hxN, hxbound⟩ := hU x hx
  refine ⟨hxN, logHessianForm_symm P hxN, fun u hu => ?_⟩
  exact lt_of_lt_of_le (mul_pos hc (sq_pos_of_pos (norm_pos_iff.mpr hu))) (hxbound u)

end
end AlbertGeometry.Cubic
