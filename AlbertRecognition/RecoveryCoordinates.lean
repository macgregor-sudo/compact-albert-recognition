/- Literal gA-normalized algebraic basis for the native trace kernel.
No norm/inner-product instance on V is introduced or replaced. -/
module

public import AlbertRecognition.FixedFrame.FrameCoordinates
public import AlbertRecognition.ReferenceCoordinates
public import AlbertRecognition.CubicOperators
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Analysis.SpecialFunctions.Sqrt

@[expose] public section
namespace AlbertRecognition.RecoveryCoordinates
noncomputable section
open Module Glennie FixedFrame
open scoped BigOperators

abbrev RawIndex := Fin 2 ⊕ (Fin 3 × Fin 8)

def slots : Fin 3 → (Octonion →ₗ[ℝ] V) := ![X01, X02, X12]

def rawVector : RawIndex → V
  | Sum.inl i => ![h 0, frameD] i
  | Sum.inr (s,t) => slots s (octBasis t)

def rawWeight (i : RawIndex) : ℝ := if i = Sum.inl 0 then 2 else 2/3

theorem octBasis_gram (i j : Fin 8) :
    octDot (octBasis i) (octBasis j) = if i = j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;>
    norm_num [octBasis, octDot_coordinates, octNormSq, Quaternion.normSq_def',
      octScalar, qi, qj, qk]

theorem slots_gram (s t : Fin 3) (u v : Octonion) :
    gA (slots s u) (slots t v) =
      if s = t then (2/3 : ℝ) * octDot u v else 0 := by
  have hnorm : octNormSq (0 : Octonion) = 0 := (octNormSq_eq_zero 0).mpr rfl
  fin_cases s <;> fin_cases t <;>
    simp [slots, X01, X02, X12, gA, inner_coordinates, octDot_coordinates, hnorm] <;> ring

theorem diagonal_gram (i j : Fin 2) :
    gA (![h 0, frameD] i) (![h 0, frameD] j) =
      if i = j then (if i = 0 then (2 : ℝ) else 2/3) else 0 := by
  fin_cases i <;> fin_cases j <;>
    norm_num [gA, inner_coordinates, h, e, unit, frameD,
      octDot_coordinates, octNormSq, Quaternion.normSq_def']

theorem diagonal_slots_gram (i : Fin 2) (s : Fin 3) (u : Octonion) :
    gA (![h 0, frameD] i) (slots s u) = 0 := by
  have hnorm : octNormSq (0 : Octonion) = 0 := (octNormSq_eq_zero 0).mpr rfl
  fin_cases i <;> fin_cases s <;>
    simp [slots, X01, X02, X12, gA, inner_coordinates, h, e, unit, frameD,
      octDot_coordinates, hnorm]

theorem rawVector_gram (i j : RawIndex) :
    gA (rawVector i) (rawVector j) = if i = j then rawWeight i else 0 := by
  rcases i with i | ⟨s,t⟩
  · rcases j with j | ⟨s,t⟩
    · simpa [rawVector, rawWeight] using diagonal_gram i j
    · simp [rawVector, diagonal_slots_gram]
  · rcases j with j | ⟨p,u⟩
    · rw [gA_comm]
      simp [rawVector, diagonal_slots_gram]
    · simp only [rawVector, slots_gram, octBasis_gram]
      by_cases hs : s = p <;> by_cases ht : t = u <;>
        simp [rawWeight, hs, ht]

/-- The h0 direction has weight2; every other raw coordinate has weight2/3. -/
def normalization (i : RawIndex) : ℝ :=
  if i = Sum.inl 0 then (Real.sqrt 2)⁻¹ else Real.sqrt (3/2)

theorem normalization_weight (i : RawIndex) :
    normalization i * normalization i * rawWeight i = 1 := by
  by_cases hi : i = Sum.inl 0
  · have hn : Real.sqrt (2 : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
    have hs : (Real.sqrt (2 : ℝ))^2 = 2 := Real.sq_sqrt (by norm_num)
    simp only [normalization, rawWeight, if_pos hi]
    field_simp [hn]
    nlinarith
  · have hs : (Real.sqrt (3/2 : ℝ))^2 = 3/2 := Real.sq_sqrt (by norm_num)
    simp only [normalization, rawWeight, if_neg hi]
    nlinarith

def normalizedVector (i : RawIndex) : V := normalization i • rawVector i

theorem normalizedVector_gram (i j : RawIndex) :
    gA (normalizedVector i) (normalizedVector j) = if i = j then 1 else 0 := by
  rw [normalizedVector, normalizedVector, gA_smul_left, gA_smul_right,
    rawVector_gram]
  by_cases hij : i = j
  · subst j
    simpa [mul_assoc] using normalization_weight i
  · simp [hij]

/-- Only the order of the already explicit26 normalized vectors is chosen. -/
def indexEquiv : RawIndex ≃ Fin 26 := Fintype.equivOfCardEq (by simp [RawIndex])

def beta (i : Fin 26) : V := normalizedVector (indexEquiv.symm i)

theorem beta_gram (i j : Fin 26) : gA (beta i) (beta j) = if i = j then 1 else 0 := by
  rw [beta, beta, normalizedVector_gram]
  by_cases hij : i = j
  · subst j
    simp
  · have hn : indexEquiv.symm i ≠ indexEquiv.symm j :=
      fun heq => hij (indexEquiv.symm.injective heq)
    simp [hij, hn]

/-- The actual Gram identity proves independence; orthonormality is not a field. -/
theorem beta_linearIndependent : LinearIndependent ℝ beta := by
  apply Fintype.linearIndependent_iff.mpr
  intro c hc i
  have hp := congrArg (fun x : V => gA x (beta i)) hc
  change (metricBilin.flip (beta i)) (∑ j, c j • beta j) =
    (metricBilin.flip (beta i)) 0 at hp
  simpa [map_sum, map_smul, LinearMap.flip_apply, metricBilin_apply, beta_gram] using hp

/-- Dimension26 is proved in rational native coordinates. -/
def basis : Basis (Fin 26) ℝ V := Basis.mk beta_linearIndependent
  (by
    have hs := beta_linearIndependent.span_eq_top_of_card_eq_finrank'
      (by simpa using finrank_V.symm)
    exact hs.ge)

@[simp] theorem basis_apply (i : Fin 26) : basis i = beta i := Basis.mk_apply _ _ i

/-- Coordinates really pair against the gA-normalized basis, with trace/3. -/
theorem repr_eq_pairing (x : V) (i : Fin 26) : basis.repr x i = gA x (beta i) := by
  conv_rhs => rw [← basis.sum_repr x]
  change basis.repr x i = (metricBilin.flip (beta i))
    (∑ j, basis.repr x j • basis j)
  simp [map_sum, map_smul, LinearMap.flip_apply, metricBilin_apply, basis_apply, beta_gram]

/-- A bilinear Euclidean isometry certificate, without an inner-product instance. -/
theorem metric_coordinates (x y : V) :
    gA x y = ∑ i : Fin 26, basis.repr x i * basis.repr y i := by
  conv_lhs => rw [← basis.sum_repr x]
  change (metricBilin.flip y) (∑ i, basis.repr x i • basis i) = _
  simp only [map_sum, map_smul, smul_eq_mul, LinearMap.flip_apply,
    metricBilin_apply, basis_apply]
  apply Finset.sum_congr rfl
  intro i hi
  change basis.repr x i * gA (beta i) y = basis.repr x i * basis.repr y i
  rw [gA_comm (beta i) y, ← repr_eq_pairing y i]

end
end AlbertRecognition.RecoveryCoordinates
