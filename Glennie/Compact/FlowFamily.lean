/- The C^1 family and its derivative formula.
  * For directions D_1 .. D_k (Jordan derivations, trace-free) and parameters
    s in R^k, `familyAut D s` is the compact automorphism exp(sum_n s_n D_n)
    (`flowAut` at time 1). On coordinates this is
    `familyC D s = exp (spanCoord D s)`, and s |-> familyC D s has strict
    Frechet derivative `spanCoord D` at s = 0 (exp has strict derivative 1 at 0).
    It is continuous in s everywhere.
  * Each frame a of a triple T is moved by its own direction family D a. Every
    ledger entry of the moved triple is a map of s with strict Frechet derivative
    at 0; its value in direction h is
      T((D0(h) T0i o T1j) o T2l) + T((T0i o D1(h) T1j) o T2l) + T((T0i o T1j) o D2(h) T2l)
    with Da(h) = sum_n h_n D_{a,n} (`movedLedgerDeriv_apply`).
  * Specialization: twenty directions [L_t, L_b] with t = basis 1 and
    b = basis (partnerIndex n), read through the dictionary
    (`extDecode (extUnit m)` gives the basis vectors), sixteen on the
    first frame and four on the second. The twenty selected rows have strict
    derivative at 0 whose (r, n) entry is the `jacobianEntry`
    (`flow_family_derivative`). This holds for every triple T; the flat base is one instance. No rank or determinant claim is made here. -/
module

public import Glennie.Compact.Flows
public import Glennie.Compact.NativeDictionaryLiteral
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

@[expose] public section

namespace Glennie.Compact.FlowFamily

open Glennie.Compact.NativeDictionary Glennie.Compact.Flows

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

/-! ## The parameter-to-generator map -/

/-- s |-> sum_n s_n D_n, read on coordinates, as a continuous linear map. -/
def spanCoord {k : ℕ} (D : Fin k → Albert →ₗ[ℝ] Albert) :
    (Fin k → ℝ) →L[ℝ] ((Fin 27 → ℝ) →L[ℝ] (Fin 27 → ℝ)) :=
  ∑ n, (ContinuousLinearMap.proj n : (Fin k → ℝ) →L[ℝ] ℝ).smulRight (toCoord (D n))

theorem spanCoord_apply {k : ℕ} (D : Fin k → Albert →ₗ[ℝ] Albert) (s : Fin k → ℝ) :
    spanCoord D s = ∑ n, s n • toCoord (D n) := by
  simp only [spanCoord, sum_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.proj_apply]

/-- The real-linear combination sum_n s_n D_n on Albert. -/
def spanDer {k : ℕ} (D : Fin k → Albert →ₗ[ℝ] Albert) (s : Fin k → ℝ) :
    Albert →ₗ[ℝ] Albert :=
  ∑ n, s n • D n

theorem spanDer_apply {k : ℕ} (D : Fin k → Albert →ₗ[ℝ] Albert) (s : Fin k → ℝ)
    (x : Albert) : spanDer D s x = ∑ n, s n • D n x := by
  simp only [spanDer, LinearMap.sum_apply, LinearMap.smul_apply]

theorem toCoord_spanDer {k : ℕ} (D : Fin k → Albert →ₗ[ℝ] Albert) (s : Fin k → ℝ) :
    toCoord (spanDer D s) = spanCoord D s := by
  refine ContinuousLinearMap.ext fun a => ?_
  simp only [toCoord_apply, spanDer_apply, map_sum, map_smul, spanCoord_apply, sum_apply,
    smul_apply]

theorem spanDer_single {k : ℕ} (D : Fin k → Albert →ₗ[ℝ] Albert) (n : Fin k) (x : Albert) :
    spanDer D (Pi.single n 1) x = D n x := by
  rw [spanDer_apply, Finset.sum_eq_single n]
  · rw [Pi.single_eq_same, one_smul]
  · intro m _ hm
    rw [Pi.single_eq_of_ne hm, zero_smul]
  · intro hn
    exact absurd (Finset.mem_univ n) hn

theorem spanDer_isJordanDerivation {k : ℕ} {D : Fin k → Albert →ₗ[ℝ] Albert}
    (hD : ∀ n, IsJordanDerivation (D n)) (s : Fin k → ℝ) :
    IsJordanDerivation (spanDer D s) :=
  IsJordanDerivation.sum Finset.univ (fun n => s n • D n) (fun n _ => (hD n).smul (s n))

theorem spanDer_traceFree {k : ℕ} {D : Fin k → Albert →ₗ[ℝ] Albert}
    (hT : ∀ n, TraceFree (D n)) (s : Fin k → ℝ) : TraceFree (spanDer D s) :=
  TraceFree.sum Finset.univ (fun n => s n • D n) (fun n _ => (hT n).smul (s n))

/-! ## The family exp(sum_n s_n D_n) -/

/-- exp(sum_n s_n D_n) on coordinates. -/
def familyC {k : ℕ} (D : Fin k → Albert →ₗ[ℝ] Albert) (s : Fin k → ℝ) :
    (Fin 27 → ℝ) →L[ℝ] (Fin 27 → ℝ) :=
  NormedSpace.exp (spanCoord D s)

theorem flowC_spanDer {k : ℕ} (D : Fin k → Albert →ₗ[ℝ] Albert) (s : Fin k → ℝ) :
    flowC (spanDer D s) 1 = familyC D s := by
  rw [flowC, one_smul, toCoord_spanDer, familyC]

theorem familyC_zero {k : ℕ} (D : Fin k → Albert →ₗ[ℝ] Albert) : familyC D 0 = 1 := by
  rw [familyC, map_zero, NormedSpace.exp_zero]

theorem familyC_zero_apply {k : ℕ} (D : Fin k → Albert →ₗ[ℝ] Albert) (v : Fin 27 → ℝ) :
    familyC D 0 v = v := by
  rw [familyC_zero, one_apply_eq_self]

/-- The family has strict Frechet derivative `spanCoord D` at s = 0. -/
theorem hasStrictFDerivAt_familyC {k : ℕ} (D : Fin k → Albert →ₗ[ℝ] Albert) :
    HasStrictFDerivAt (familyC D) (spanCoord D) 0 := by
  have h0 : spanCoord D 0 = 0 := map_zero _
  have hexp : HasStrictFDerivAt
      (NormedSpace.exp : ((Fin 27 → ℝ) →L[ℝ] (Fin 27 → ℝ)) → ((Fin 27 → ℝ) →L[ℝ] (Fin 27 → ℝ)))
      (1 : ((Fin 27 → ℝ) →L[ℝ] (Fin 27 → ℝ)) →L[ℝ] ((Fin 27 → ℝ) →L[ℝ] (Fin 27 → ℝ)))
      (spanCoord D 0) := by
    rw [h0]
    exact hasStrictFDerivAt_exp_zero
  refine (hexp.comp (0 : Fin k → ℝ) (spanCoord D).hasStrictFDerivAt).congr_fderiv ?_
  exact ContinuousLinearMap.ext fun h => by
    rw [ContinuousLinearMap.comp_apply, one_apply_eq_self]

theorem hasStrictFDerivAt_familyC_apply {k : ℕ} (D : Fin k → Albert →ₗ[ℝ] Albert)
    (v : Fin 27 → ℝ) :
    HasStrictFDerivAt (fun s => familyC D s v) ((spanCoord D).flip v) 0 := by
  refine ((hasStrictFDerivAt_familyC D).clm_apply
    (hasStrictFDerivAt_const v (0 : Fin k → ℝ))).congr_fderiv ?_
  rw [ContinuousLinearMap.comp_zero, zero_add]

theorem spanCoord_flip_apply {k : ℕ} (D : Fin k → Albert →ₗ[ℝ] Albert) (v : Fin 27 → ℝ)
    (h : Fin k → ℝ) :
    (spanCoord D).flip v h = extEquiv.symm (spanDer D h (extEquiv v)) := by
  rw [ContinuousLinearMap.flip_apply, ← toCoord_spanDer, toCoord_apply]

/-- The family is continuous in s everywhere (needed by the later sections). -/
theorem continuous_familyC {k : ℕ} (D : Fin k → Albert →ₗ[ℝ] Albert) :
    Continuous (familyC D) := by
  let +nondep : NormedAlgebra ℚ ((Fin 27 → ℝ) →L[ℝ] (Fin 27 → ℝ)) :=
    .restrictScalars ℚ ℝ _
  exact NormedSpace.exp_continuous.comp (spanCoord D).continuous

theorem continuous_familyC_apply {k : ℕ} (D : Fin k → Albert →ₗ[ℝ] Albert)
    (v : Fin 27 → ℝ) : Continuous fun s => familyC D s v :=
  (continuous_familyC D).clm_apply continuous_const

/-! ## The family as compact automorphisms -/

/-- exp(sum_n s_n D_n) as a compact automorphism (flowAut at time 1). -/
def familyAut {k : ℕ} (D : Fin k → Albert →ₗ[ℝ] Albert)
    (hD : ∀ n, IsJordanDerivation (D n)) (hT : ∀ n, TraceFree (D n)) (s : Fin k → ℝ) :
    CompactAutomorphism :=
  flowAut (spanDer D s) (spanDer_isJordanDerivation hD s) (spanDer_traceFree hT s) 1

theorem familyAut_apply {k : ℕ} (D : Fin k → Albert →ₗ[ℝ] Albert)
    (hD : ∀ n, IsJordanDerivation (D n)) (hT : ∀ n, TraceFree (D n)) (s : Fin k → ℝ)
    (x : Albert) :
    (familyAut D hD hT s).equiv x = extEquiv (familyC D s (extEquiv.symm x)) := by
  rw [familyAut, flowAut_apply, flow_apply, flowC_spanDer]

/-! ## Moved frames -/

/-- Frame a of the triple T, moved by the family automorphism of its own directions D a. -/
def movedFrame {k : ℕ} (D : Fin 3 → Fin k → Albert →ₗ[ℝ] Albert)
    (hD : ∀ a n, IsJordanDerivation (D a n)) (hT : ∀ a n, TraceFree (D a n))
    (T : Fin 3 → Fin 3 → Albert) (a : Fin 3) (s : Fin k → ℝ) : Fin 3 → Albert :=
  fun i => (familyAut (D a) (hD a) (hT a) s).equiv (T a i)

theorem movedFrame_frame {k : ℕ} (D : Fin 3 → Fin k → Albert →ₗ[ℝ] Albert)
    (hD : ∀ a n, IsJordanDerivation (D a n)) (hT : ∀ a n, TraceFree (D a n))
    (T : Fin 3 → Fin 3 → Albert) (a : Fin 3) (hF : Frame (T a)) (s : Fin k → ℝ) :
    Frame (movedFrame D hD hT T a s) :=
  (familyAut (D a) (hD a) (hT a) s).map_frame (T a) hF

theorem movedFrame_encoder {k : ℕ} (D : Fin 3 → Fin k → Albert →ₗ[ℝ] Albert)
    (hD : ∀ a n, IsJordanDerivation (D a n)) (hT : ∀ a n, TraceFree (D a n))
    (T : Fin 3 → Fin 3 → Albert) (a : Fin 3) (s : Fin k → ℝ) :
    encoder (movedFrame D hD hT T a s) =
      (familyAut (D a) (hD a) (hT a) s).equiv (encoder (T a)) :=
  (familyAut (D a) (hD a) (hT a) s).encoder_map (T a)

theorem movedFrame_zero {k : ℕ} (D : Fin 3 → Fin k → Albert →ₗ[ℝ] Albert)
    (hD : ∀ a n, IsJordanDerivation (D a n)) (hT : ∀ a n, TraceFree (D a n))
    (T : Fin 3 → Fin 3 → Albert) (a : Fin 3) : movedFrame D hD hT T a 0 = T a := by
  funext i
  show (familyAut (D a) (hD a) (hT a) 0).equiv (T a i) = T a i
  rw [familyAut_apply, familyC_zero_apply, LinearEquiv.apply_symm_apply]

theorem movedFrame_coord {k : ℕ} (D : Fin 3 → Fin k → Albert →ₗ[ℝ] Albert)
    (hD : ∀ a n, IsJordanDerivation (D a n)) (hT : ∀ a n, TraceFree (D a n))
    (T : Fin 3 → Fin 3 → Albert) (a : Fin 3) (s : Fin k → ℝ) (i : Fin 3) :
    extEquiv.symm (movedFrame D hD hT T a s i) = familyC (D a) s (extEquiv.symm (T a i)) := by
  show extEquiv.symm ((familyAut (D a) (hD a) (hT a) s).equiv (T a i)) = _
  rw [familyAut_apply, LinearEquiv.symm_apply_apply]

/-- Every atom of a moved frame depends continuously on s (in coordinates). -/
theorem continuous_movedFrame_coord {k : ℕ} (D : Fin 3 → Fin k → Albert →ₗ[ℝ] Albert)
    (hD : ∀ a n, IsJordanDerivation (D a n)) (hT : ∀ a n, TraceFree (D a n))
    (T : Fin 3 → Fin 3 → Albert) (a i : Fin 3) :
    Continuous fun s : Fin k → ℝ => extEquiv.symm (movedFrame D hD hT T a s i) := by
  simp only [movedFrame_coord]
  exact continuous_familyC_apply (D a) _

/-! ## Ledger entries and their strict derivative -/

theorem ledger_movedFrame {k : ℕ} (D : Fin 3 → Fin k → Albert →ₗ[ℝ] Albert)
    (hD : ∀ a n, IsJordanDerivation (D a n)) (hT : ∀ a n, TraceFree (D a n))
    (T : Fin 3 → Fin 3 → Albert) (s : Fin k → ℝ) (i j l : Fin 3) :
    ledger (movedFrame D hD hT T 0 s) (movedFrame D hD hT T 1 s) (movedFrame D hD hT T 2 s)
        i j l =
      traceC (prodC (prodC (familyC (D 0) s (extEquiv.symm (T 0 i)))
        (familyC (D 1) s (extEquiv.symm (T 1 j)))) (familyC (D 2) s (extEquiv.symm (T 2 l)))) := by
  simp only [ledger, movedFrame, familyAut_apply, traceC_apply, prodC_apply,
    LinearEquiv.apply_symm_apply]

/-- Chain rule for one coordinate ledger entry along three strictly differentiable curves. -/
theorem hasStrictFDerivAt_ledgerC {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f0 f1 f2 : E → (Fin 27 → ℝ)} {f0' f1' f2' : E →L[ℝ] (Fin 27 → ℝ)} {x : E}
    (h0 : HasStrictFDerivAt f0 f0' x) (h1 : HasStrictFDerivAt f1 f1' x)
    (h2 : HasStrictFDerivAt f2 f2' x) :
    HasStrictFDerivAt (fun y => traceC (prodC (prodC (f0 y) (f1 y)) (f2 y)))
      (traceC.comp ((prodC (prodC (f0 x) (f1 x))).comp f2' +
        (prodC.comp ((prodC (f0 x)).comp f1' + (prodC.comp f0').flip (f1 x))).flip (f2 x))) x :=
  traceC.hasStrictFDerivAt.comp x
    ((prodC.hasStrictFDerivAt.comp x
      ((prodC.hasStrictFDerivAt.comp x h0).clm_apply h1)).clm_apply h2)

theorem ledgerDerivC_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p q r : Fin 27 → ℝ) (f0' f1' f2' : E →L[ℝ] (Fin 27 → ℝ)) (h : E) :
    (traceC.comp ((prodC (prodC p q)).comp f2' +
        (prodC.comp ((prodC p).comp f1' + (prodC.comp f0').flip q)).flip r)) h =
      traceC (prodC (prodC (f0' h) q) r) + traceC (prodC (prodC p (f1' h)) r) +
        traceC (prodC (prodC p q) (f2' h)) := by
  simp only [ContinuousLinearMap.comp_apply, add_apply, ContinuousLinearMap.flip_apply,
    map_add]
  ring

/-- The strict derivative at 0 of one moved ledger entry, as a functional of h. -/
def movedLedgerDeriv {k : ℕ} (D : Fin 3 → Fin k → Albert →ₗ[ℝ] Albert)
    (T : Fin 3 → Fin 3 → Albert) (i j l : Fin 3) : (Fin k → ℝ) →L[ℝ] ℝ :=
  traceC.comp ((prodC (prodC (extEquiv.symm (T 0 i)) (extEquiv.symm (T 1 j)))).comp
      ((spanCoord (D 2)).flip (extEquiv.symm (T 2 l))) +
    (prodC.comp ((prodC (extEquiv.symm (T 0 i))).comp
        ((spanCoord (D 1)).flip (extEquiv.symm (T 1 j))) +
      (prodC.comp ((spanCoord (D 0)).flip (extEquiv.symm (T 0 i)))).flip
        (extEquiv.symm (T 1 j)))).flip (extEquiv.symm (T 2 l)))

theorem hasStrictFDerivAt_ledger_movedFrame {k : ℕ} (D : Fin 3 → Fin k → Albert →ₗ[ℝ] Albert)
    (hD : ∀ a n, IsJordanDerivation (D a n)) (hT : ∀ a n, TraceFree (D a n))
    (T : Fin 3 → Fin 3 → Albert) (i j l : Fin 3) :
    HasStrictFDerivAt
      (fun s => ledger (movedFrame D hD hT T 0 s) (movedFrame D hD hT T 1 s)
        (movedFrame D hD hT T 2 s) i j l)
      (movedLedgerDeriv D T i j l) 0 := by
  have h := hasStrictFDerivAt_ledgerC
    (hasStrictFDerivAt_familyC_apply (D 0) (extEquiv.symm (T 0 i)))
    (hasStrictFDerivAt_familyC_apply (D 1) (extEquiv.symm (T 1 j)))
    (hasStrictFDerivAt_familyC_apply (D 2) (extEquiv.symm (T 2 l)))
  simp only [familyC_zero_apply] at h
  have hfun : (fun s => ledger (movedFrame D hD hT T 0 s) (movedFrame D hD hT T 1 s)
      (movedFrame D hD hT T 2 s) i j l) = fun s =>
      traceC (prodC (prodC (familyC (D 0) s (extEquiv.symm (T 0 i)))
        (familyC (D 1) s (extEquiv.symm (T 1 j)))) (familyC (D 2) s (extEquiv.symm (T 2 l)))) :=
    funext fun s => ledger_movedFrame D hD hT T s i j l
  rw [hfun]
  exact h

/-- The derivative in direction h: each atom of frame a moves by D_a(h) = sum_n h_n D_{a,n}. -/
theorem movedLedgerDeriv_apply {k : ℕ} (D : Fin 3 → Fin k → Albert →ₗ[ℝ] Albert)
    (T : Fin 3 → Fin 3 → Albert) (i j l : Fin 3) (h : Fin k → ℝ) :
    movedLedgerDeriv D T i j l h =
      trace (jordan (jordan (spanDer (D 0) h (T 0 i)) (T 1 j)) (T 2 l)) +
        trace (jordan (jordan (T 0 i) (spanDer (D 1) h (T 1 j))) (T 2 l)) +
        trace (jordan (jordan (T 0 i) (T 1 j)) (spanDer (D 2) h (T 2 l))) := by
  rw [movedLedgerDeriv, ledgerDerivC_apply]
  simp only [ContinuousLinearMap.flip_apply, ← toCoord_spanDer, toCoord_apply, traceC_apply,
    prodC_apply, LinearEquiv.apply_symm_apply]

/-! ## The twenty directions, read through the dictionary -/

/-- The partner full27 indices, in the minor-column order. -/
def partnerIndex : Fin 20 → Fin 27 :=
  ![3, 4, 5, 6, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20,
    11, 12, 13, 14]

/-- Sixteen first-frame and four second-frame directions; none third-frame. -/
def contextIndex : Fin 20 → Fin 3 :=
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1]

/-- The twenty selected ordered triple-ledger rows. -/
def rowIndex : Fin 20 → Fin 3 × Fin 3 × Fin 3 :=
  ![(0,0,0), (0,0,1), (0,0,2), (0,1,0), (0,1,1), (0,1,2),
    (0,2,0), (0,2,1), (1,0,0), (1,0,1), (1,0,2), (1,1,0),
    (1,1,1), (1,1,2), (1,2,0), (1,2,1), (2,0,0), (2,0,1),
    (2,1,0), (2,1,1)]

/-- [L_t, L_b] with t = basis 1 and b = basis (partnerIndex n), halved native product,
no factor 4. Basis vectors are `extDecode (extUnit m)`. -/
def direction (n : Fin 20) : Albert →ₗ[ℝ] Albert :=
  innerDerLinear (extDecode (extUnit 1)) (extDecode (extUnit (partnerIndex n)))

/-- The direction family of frame a: direction n if it belongs to frame a, else 0. -/
def contextDirection (a : Fin 3) (n : Fin 20) : Albert →ₗ[ℝ] Albert :=
  if a = contextIndex n then direction n else 0

theorem contextDirection_isJordanDerivation (a : Fin 3) (n : Fin 20) :
    IsJordanDerivation (contextDirection a n) := by
  unfold contextDirection
  split_ifs
  · exact isJordanDerivation_innerDerLinear _ _
  · exact IsJordanDerivation.zero

theorem contextDirection_traceFree (a : Fin 3) (n : Fin 20) :
    TraceFree (contextDirection a n) := by
  unfold contextDirection
  split_ifs
  · exact traceFree_innerDerLinear _ _
  · exact TraceFree.zero

theorem contextDirection_apply (a : Fin 3) (n : Fin 20) (x : Albert) :
    contextDirection a n x = if a = contextIndex n then direction n x else 0 := by
  unfold contextDirection
  split_ifs <;> rfl

/-- The atom tangent. -/
def atomTangent (T : Fin 3 → Fin 3 → Albert) (n : Fin 20) (a i : Fin 3) : Albert :=
  if a = contextIndex n then direction n (T a i) else 0

/-- The literal scalar `jacobianEntry`, with its `let`s inlined. -/
def jacobianEntry (T : Fin 3 → Fin 3 → Albert) (r n : Fin 20) : ℝ :=
  trace (jordan (jordan (atomTangent T n 0 (rowIndex r).1) (T 1 (rowIndex r).2.1))
      (T 2 (rowIndex r).2.2) +
    jordan (jordan (T 0 (rowIndex r).1) (atomTangent T n 1 (rowIndex r).2.1))
      (T 2 (rowIndex r).2.2) +
    jordan (jordan (T 0 (rowIndex r).1) (T 1 (rowIndex r).2.1))
      (atomTangent T n 2 (rowIndex r).2.2))

/-- The twenty selected ledger rows of the moved triple, as a map of s in R^20. -/
def rowLedger (T : Fin 3 → Fin 3 → Albert) (s : Fin 20 → ℝ) : Fin 20 → ℝ := fun r =>
  ledger (movedFrame contextDirection contextDirection_isJordanDerivation
      contextDirection_traceFree T 0 s)
    (movedFrame contextDirection contextDirection_isJordanDerivation
      contextDirection_traceFree T 1 s)
    (movedFrame contextDirection contextDirection_isJordanDerivation
      contextDirection_traceFree T 2 s)
    (rowIndex r).1 (rowIndex r).2.1 (rowIndex r).2.2

/-- Its strict derivative at 0, row by row. -/
def rowLedgerDeriv (T : Fin 3 → Fin 3 → Albert) : (Fin 20 → ℝ) →L[ℝ] (Fin 20 → ℝ) :=
  ContinuousLinearMap.pi fun r =>
    movedLedgerDeriv contextDirection T (rowIndex r).1 (rowIndex r).2.1 (rowIndex r).2.2

theorem rowLedger_zero (T : Fin 3 → Fin 3 → Albert) :
    rowLedger T 0 =
      fun r => ledger (T 0) (T 1) (T 2) (rowIndex r).1 (rowIndex r).2.1 (rowIndex r).2.2 := by
  funext r
  simp only [rowLedger, movedFrame_zero]

theorem hasStrictFDerivAt_rowLedger (T : Fin 3 → Fin 3 → Albert) :
    HasStrictFDerivAt (rowLedger T) (rowLedgerDeriv T) 0 := by
  refine hasStrictFDerivAt_pi'.2 fun r => ?_
  rw [rowLedgerDeriv, ContinuousLinearMap.proj_pi]
  exact hasStrictFDerivAt_ledger_movedFrame contextDirection contextDirection_isJordanDerivation
    contextDirection_traceFree T _ _ _

theorem rowLedgerDeriv_single (T : Fin 3 → Fin 3 → Albert) (r n : Fin 20) :
    rowLedgerDeriv T (Pi.single n 1) r = jacobianEntry T r n := by
  rw [rowLedgerDeriv, ContinuousLinearMap.pi_apply, movedLedgerDeriv_apply, jacobianEntry,
    trace_add, trace_add]
  simp only [spanDer_single, contextDirection_apply, atomTangent]

/-- For every triple T, the twenty selected triple-ledger
rows of the moved triple (sixteen directions exp-flowing the first frame, four the
second) form a map of s in R^20 that equals the rows of T at s = 0 and has a strict
Frechet derivative at 0 whose (r, n) entry is the `jacobianEntry`. -/
theorem flow_family_derivative (T : Fin 3 → Fin 3 → Albert) :
    rowLedger T 0 =
        (fun r => ledger (T 0) (T 1) (T 2) (rowIndex r).1 (rowIndex r).2.1 (rowIndex r).2.2) ∧
      HasStrictFDerivAt (rowLedger T) (rowLedgerDeriv T) 0 ∧
      ∀ r n : Fin 20, rowLedgerDeriv T (Pi.single n 1) r = jacobianEntry T r n :=
  ⟨rowLedger_zero T, hasStrictFDerivAt_rowLedger T, rowLedgerDeriv_single T⟩

end
end Glennie.Compact.FlowFamily
