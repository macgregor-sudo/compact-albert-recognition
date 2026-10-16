/- Native right-multiplication commutants in the compact quaternion-pair model.
All octonion products retain their displayed parentheses. -/
module

public import AlbertRecognition.FixedFrame.QuaternionFacts
public import Mathlib.LinearAlgebra.Prod

@[expose] public section

namespace AlbertRecognition.FixedFrame
noncomputable section

open Glennie
open scoped Quaternion

/-- The actual real coordinate basis of compact native octonions. -/
def octBasis : Fin 8 → Octonion :=
  ![octScalar 1, (qi, 0), (qj, 0), (qk, 0), (0, 1), (0, qi), (0, qj), (0, qk)]

@[simp] theorem octBasis_zero : octBasis 0 = octScalar 1 := rfl

theorem octBasis_conj_imag (t : Fin 8) (ht : t ≠ 0) :
    octConj (octBasis t) = -octBasis t := by
  fin_cases t <;> simp_all [octBasis, octConj]

/-- Literal eight-coordinate reconstruction; no spanning hypothesis is assumed. -/
theorem oct_decompose (x : Octonion) :
    x = x.1.re • octBasis 0 + x.1.imI • octBasis 1 +
      x.1.imJ • octBasis 2 + x.1.imK • octBasis 3 +
      x.2.re • octBasis 4 + x.2.imI • octBasis 5 +
      x.2.imJ • octBasis 6 + x.2.imK • octBasis 7 := by
  apply Prod.ext <;> apply Quaternion.ext <;>
    simp [octBasis, octScalar, qi, qj, qk, smul_eq_mul]

theorem oct_linear_ext (f g : Octonion →ₗ[ℝ] Octonion)
    (h : ∀ t : Fin 8, f (octBasis t) = g (octBasis t)) : f = g := by
  apply LinearMap.ext
  intro x
  rw [oct_decompose x]
  simp only [map_add, map_smul, h]

/-- Right multiplication, with the native nonassociative product. -/
def octRight (a : Octonion) : Module.End ℝ Octonion where
  toFun x := octMul x a
  map_add' x y := octMul_add_left x y a
  map_smul' r x := by
    simpa only [RingHom.id_apply] using octMul_smul_left r x a

/-- Left multiplication, used only as a real-linear map. -/
def octLeft (a : Octonion) : Module.End ℝ Octonion where
  toFun x := octMul a x
  map_add' x y := octMul_add_right a x y
  map_smul' r x := by
    simpa only [RingHom.id_apply] using octMul_smul_right r a x

def octConjLinear : Module.End ℝ Octonion where
  toFun := octConj
  map_add' := octConj_add
  map_smul' r x := by
    simpa only [RingHom.id_apply] using octConj_smul r x

@[simp] theorem octMul_zero_left (a : Octonion) : octMul 0 a = 0 := by
  simp [octMul]
@[simp] theorem octMul_zero_right (a : Octonion) : octMul a 0 = 0 := by
  simp [octMul]

@[simp] theorem octRight_apply (a x : Octonion) : octRight a x = octMul x a := rfl
@[simp] theorem octLeft_apply (a x : Octonion) : octLeft a x = octMul a x := rfl
@[simp] theorem octConjLinear_apply (x : Octonion) : octConjLinear x = octConj x := rfl

/-- The native left nucleus is the real line, via two quaternion-pair tests. -/
theorem oct_left_nucleus_scalar (c : Octonion)
    (hc : ∀ x a : Octonion, octMul c (octMul x a) = octMul (octMul c x) a) :
    ∃ b : ℝ, c = octScalar b := by
  rcases c with ⟨p, q⟩
  have hq := congrArg Prod.snd (hc (qi, 0) (qj, 0))
  have hqk : -(q * qk) = q * qk := by
    simpa [octMul, mul_assoc] using hq
  have hq0 : q = 0 := quat_right_k_zero q (quat_neg_eq_self_zero (q * qk) hqk)
  have hpi := congrArg Prod.snd (hc (0, 1) (qi, 0))
  have hpj := congrArg Prod.snd (hc (0, 1) (qj, 0))
  have hi : qi * p = p * qi := by
    simpa [octMul, neg_mul, mul_neg] using congrArg Neg.neg hpi
  have hj : qj * p = p * qj := by
    simpa [octMul, neg_mul, mul_neg] using congrArg Neg.neg hpj
  refine ⟨p.re, ?_⟩
  exact Prod.ext (quat_comm_i_j_real p hi hj) hq0

/-- The reverse associator identity needed for the imaginary anticommutant. -/
theorem oct_reverse_identity_zero (d : Octonion)
    (hd : ∀ a x : Octonion, octMul d (octMul a x) = octMul (octMul d x) a) :
    d = 0 := by
  rcases d with ⟨p, q⟩
  have hp := congrArg Prod.fst (hd (qi, 0) (qj, 0))
  have hpk : -(p * qk) = p * qk := by
    simpa [octMul, mul_assoc] using hp.symm
  have hp0 : p = 0 := quat_right_k_zero p (quat_neg_eq_self_zero (p * qk) hpk)
  have hqi := congrArg Prod.fst (hd (0, 1) (qi, 0))
  have hqj := congrArg Prod.fst (hd (0, 1) (qj, 0))
  have hqk := congrArg Prod.fst (hd (0, 1) (qk, 0))
  have hi : qi * q = -(q * qi) := by
    simpa [octMul, neg_mul, mul_neg] using congrArg Neg.neg hqi
  have hj : qj * q = -(q * qj) := by
    simpa [octMul, neg_mul, mul_neg] using congrArg Neg.neg hqj
  have hk : qk * q = -(q * qk) := by
    simpa [octMul, neg_mul, mul_neg] using congrArg Neg.neg hqk
  exact Prod.ext hp0 (quat_anticomm_i_j_k_zero q hi hj hk)

/-- Commutation with the literal eight right multiplications forces a scalar. -/
theorem oct_right_commutant_scalar (P : Module.End ℝ Octonion)
    (hP : ∀ t : Fin 8, ∀ x : Octonion,
      P (octMul x (octBasis t)) = octMul (P x) (octBasis t)) :
    ∃ b : ℝ, P = b • LinearMap.id := by
  have hall (x a : Octonion) : P (octMul x a) = octMul (P x) a := by
    have heq : P.comp (octLeft x) = octLeft (P x) :=
      oct_linear_ext _ _ (fun t => hP t x)
    exact LinearMap.congr_fun heq a
  let c := P (octScalar 1)
  have hx (x : Octonion) : P x = octMul c x := by
    simpa [c] using hall (octScalar 1) x
  have hn : ∀ x a : Octonion, octMul c (octMul x a) = octMul (octMul c x) a := by
    intro x a
    calc
      octMul c (octMul x a) = P (octMul x a) := (hx _).symm
      _ = octMul (P x) a := hall x a
      _ = octMul (octMul c x) a := by rw [hx x]
  obtain ⟨b, hb⟩ := oct_left_nucleus_scalar c hn
  refine ⟨b, ?_⟩
  apply LinearMap.ext
  intro x
  simpa [hb] using hx x

/-- Anticommutation with seven imaginary right multiplications forces zero. -/
theorem oct_imaginary_right_anticommutant_zero (Q : Module.End ℝ Octonion)
    (hQ : ∀ t : Fin 8, t ≠ 0 → ∀ x : Octonion,
      Q (octMul x (octBasis t)) = -octMul (Q x) (octBasis t)) : Q = 0 := by
  have hall (x a : Octonion) : Q (octMul x a) = octMul (Q x) (octConj a) := by
    have heq : Q.comp (octLeft x) = (octLeft (Q x)).comp octConjLinear := by
      apply oct_linear_ext
      intro t
      by_cases ht : t = 0
      · subst t
        change Q (octMul x (octScalar 1)) = octMul (Q x) (octConj (octScalar 1))
        simp only [octConj_scalar, octMul_scalar_right, one_smul]
      · change Q (octMul x (octBasis t)) = octMul (Q x) (octConj (octBasis t))
        rw [octBasis_conj_imag t ht, hQ t ht x]
        exact (map_neg (octLeft (Q x)) (octBasis t)).symm
    exact LinearMap.congr_fun heq a
  let d := Q (octScalar 1)
  have hx (x : Octonion) : Q x = octMul d (octConj x) := by
    simpa [d] using hall (octScalar 1) x
  have hd : ∀ a x : Octonion, octMul d (octMul a x) = octMul (octMul d x) a := by
    intro a x
    have h := hall (octConj x) (octConj a)
    rw [hx (octMul (octConj x) (octConj a)), hx (octConj x)] at h
    simpa only [octConj_mul, octConj_conj] using h
  have hd0 : d = 0 := oct_reverse_identity_zero d hd
  apply LinearMap.ext
  intro x
  change Q x = (0 : Octonion)
  rw [hx x, hd0, octMul_zero_left]

end
end AlbertRecognition.FixedFrame
