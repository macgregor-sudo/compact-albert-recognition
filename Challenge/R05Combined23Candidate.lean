/- Unified independent native and admitted orbit-quotient statement surface. -/
module
public import Mathlib.Algebra.Quaternion
public import Mathlib.Analysis.Quaternion
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Algebra.Module.TransferInstance
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Real.Sqrt
public import Mathlib.Topology.Basic
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Maps.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Normed.Module.Multilinear.Curry
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
public import Mathlib.RingTheory.Finiteness.Prod
@[expose] public section
open scoped BigOperators Quaternion
namespace Glennie
noncomputable section
instance atLeastTwoOneAddOne : Nat.AtLeastTwo (1 + 1) := ⟨Nat.le_refl 2⟩
instance neZeroTwoAddOne : NeZero (2 + 1 : Nat) := ⟨by decide⟩
set_option autoImplicit false
/-- Compact octonions in the Cayley-Dickson convention with parameter -1. -/
abbrev Octonion := Quaternion ℝ × Quaternion ℝ
def octMul (x y : Octonion) : Octonion :=
  (x.1 * y.1 - star y.2 * x.2, y.2 * x.1 + x.2 * star y.1)
def octConj (x : Octonion) : Octonion := (star x.1, -x.2)
def octRe (x : Octonion) : ℝ := x.1.re
def octScalar (r : ℝ) : Octonion := ((r : Quaternion ℝ), 0)
/-- Three real diagonal coordinates and three octonionic off-diagonal entries. -/
@[ext] structure Albert where
  d0 : ℝ
  d1 : ℝ
  d2 : ℝ
  o01 : Octonion
  o02 : Octonion
  o12 : Octonion
namespace Albert
theorem extExplicit (x y : Albert)
    (h0 : x.d0 = y.d0) (h1 : x.d1 = y.d1) (h2 : x.d2 = y.d2)
    (h01 : x.o01 = y.o01) (h02 : x.o02 = y.o02) (h12 : x.o12 = y.o12) : x = y := by
  cases x
  cases y
  cases h0
  cases h1
  cases h2
  cases h01
  cases h02
  cases h12
  rfl
abbrev Coordinates := ℝ × ℝ × ℝ × Octonion × Octonion × Octonion
def coordinateEquiv : Albert ≃ Coordinates where
  toFun x := (x.d0, x.d1, x.d2, x.o01, x.o02, x.o12)
  invFun x := ⟨x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
instance : AddCommGroup Albert := coordinateEquiv.addCommGroup
def coordinateAddEquiv : Albert ≃+ Coordinates where
  toEquiv := coordinateEquiv
  map_add' _ _ := rfl
instance : Module ℝ Albert := coordinateAddEquiv.module ℝ
end Albert
def unit : Albert := ⟨1,1,1,0,0,0⟩
instance : One Albert := ⟨unit⟩
def toMatrix (x : Albert) : Matrix (Fin 3) (Fin 3) Octonion :=
  ![![octScalar x.d0, x.o01, x.o02],
    ![octConj x.o01, octScalar x.d1, x.o12],
    ![octConj x.o02, octConj x.o12, octScalar x.d2]]
def matrixMul (A B : Matrix (Fin 3) (Fin 3) Octonion) : Matrix (Fin 3) (Fin 3) Octonion := fun i j => ∑ k, octMul (A i k) (B k j)
def fromMatrix (A : Matrix (Fin 3) (Fin 3) Octonion) : Albert :=
  ⟨octRe (A 0 0), octRe (A 1 1), octRe (A 2 2), A 0 1, A 0 2, A 1 2⟩
/-- Binary symmetrized matrix product, without an associative matrix assumption. -/
def jordan (x y : Albert) : Albert :=
  fromMatrix ((1/2 : ℝ) • (matrixMul (toMatrix x) (toMatrix y) +
    matrixMul (toMatrix y) (toMatrix x)))
def trace (x : Albert) : ℝ := x.d0+x.d1+x.d2
def inner (x y : Albert) : ℝ := trace (jordan x y)
def U (x z : Albert) : Albert :=
  (2 : ℝ) • jordan x (jordan x z) - jordan (jordan x x) z
/-- The signed degree-nine scalar, using the native product and trace pairing. -/
def phi (x y z : Albert) : ℝ :=
  inner (U x (U y z) - U y (U x z)) (U z (jordan x y))
/-- An ordered triple of trace-one orthogonal idempotents summing to the unit. -/
structure Frame (p : Fin 3 → Albert) : Prop where
  trace_one : ∀ i, trace (p i) = 1
  idempotent : ∀ i, jordan (p i) (p i) = p i
  orthogonal : ∀ i j, i ≠ j → jordan (p i) (p j) = 0
  sum_unit : p 0 + p 1 + p 2 = 1
/-- A simultaneous product-and-trace automorphism of the native algebra. -/
structure CompactAutomorphism where
  equiv : Albert ≃ₗ[ℝ] Albert
  map_jordan : ∀ x y, equiv (jordan x y) = jordan (equiv x) (equiv y)
  map_trace : ∀ x, trace (equiv x) = trace x
def encoder (p : Fin 3 → Albert) : Albert := p 2 - p 0
def ledger (p q r : Fin 3 → Albert) (i j k : Fin 3) : ℝ :=
  trace (jordan (jordan (p i) (q j)) (r k))
end
end Glennie
namespace Glennie.Compact.Affine20
/-- Three ordered frames with all nine labels fixed. -/
abbrev Triple := Fin 3 → Fin 3 → Glennie.Albert
/-- Complete raw 54-trace observation type. -/
abbrev Ledger54 :=
  (Fin 3 → Fin 3 → Fin 3 → ℝ) × (Fin 3 → Fin 3 → ℝ) ×
  (Fin 3 → Fin 3 → ℝ) × (Fin 3 → Fin 3 → ℝ)
end Glennie.Compact.Affine20
namespace Glennie.SubmissionR03
noncomputable section
open Glennie
open Glennie.Compact.Affine20
/-- Named Fin indices avoid compiler-generated numeral witnesses in the statement. -/
def f0 : Fin 3 := ⟨0, Nat.zero_lt_succ 2⟩
def f1 : Fin 3 := ⟨1, Nat.lt_succ_of_le (Nat.le_succ 1)⟩
def f2 : Fin 3 := ⟨2, Nat.lt_succ_self 2⟩
def b0 : Fin 2 := ⟨0, Nat.zero_lt_succ 1⟩
def b1 : Fin 2 := ⟨1, Nat.lt_succ_self 1⟩
/-- The complete triple-trace block and three pair-trace blocks. -/
def fullLedger (T : Triple) : Ledger54 :=
  (ledger (T f0) (T f1) (T f2),
   fun i j => inner (T f0 i) (T f1 j),
   fun j k => inner (T f1 j) (T f2 k),
   fun k i => inner (T f2 k) (T f0 i))
/-- The fixed frame encoder or its Jordan square. -/
def framePower (p : Fin 3 → Albert) (s : Fin 2) : Albert :=
  if s = b0 then encoder p else jordan (encoder p) (encoder p)
def qSingle (T : Triple) (v : Fin 3) (s : Fin 2) : ℝ :=
  inner (framePower (T v) b0) (framePower (T v) s)
def qPair (T : Triple) (v w : Fin 3) (s t : Fin 2) : ℝ :=
  inner (framePower (T v) s) (framePower (T w) t)
def qTriple (T : Triple) (s t u : Fin 2) : ℝ :=
  trace (jordan (jordan (framePower (T f0) s) (framePower (T f1) t))
    (framePower (T f2) u))
/-- Six single-frame readings, twelve pair readings and eight triple readings. -/
def q26 (T : Triple) : Fin 26 → ℝ := ![
  qSingle T f0 b0, qSingle T f0 b1, qSingle T f1 b0, qSingle T f1 b1,
  qSingle T f2 b0, qSingle T f2 b1,
  qPair T f0 f1 b0 b0, qPair T f0 f1 b0 b1,
  qPair T f0 f1 b1 b0, qPair T f0 f1 b1 b1,
  qPair T f1 f2 b0 b0, qPair T f1 f2 b0 b1,
  qPair T f1 f2 b1 b0, qPair T f1 f2 b1 b1,
  qPair T f2 f0 b0 b0, qPair T f2 f0 b0 b1,
  qPair T f2 f0 b1 b0, qPair T f2 f0 b1 b1,
  qTriple T b0 b0 b0, qTriple T b0 b0 b1,
  qTriple T b0 b1 b0, qTriple T b0 b1 b1,
  qTriple T b1 b0 b0, qTriple T b1 b0 b1,
  qTriple T b1 b1 b0, qTriple T b1 b1 b1]
/-- The signed scalar of the three fixed-orientation frame encoders. -/
def phiOf (T : Triple) : ℝ :=
  phi (encoder (T f0)) (encoder (T f1)) (encoder (T f2))
/-- An explicit flat reference with ordered outcomes. -/
def quatI : Quaternion ℝ := ⟨0,1,0,0⟩
def quatJ : Quaternion ℝ := ⟨0,0,1,0⟩
def quatK : Quaternion ℝ := ⟨0,0,0,1⟩
def octI : Octonion := (quatI,0)
def octK : Octonion := (quatK,0)
def octL : Octonion := (0,1)
def octJL : Octonion := (0,quatJ)
def witnessZ : Albert := ⟨0,0,0,octJL,-octL,-octK⟩
def flatScale : ℝ := 1 / Real.sqrt 3
def flatXN : Albert := ⟨1, 0, -1, 0, 0, 0⟩
def flatY1 : Albert := ⟨0, 0, 0, octScalar 1, -octI, octScalar 1⟩
def projectorFrame (x : Albert) : Fin 3 → Albert :=
  ![(1 / (Nat.cast 2 : ℝ)) • (jordan x x - x), 1 - jordan x x,
    (1 / (Nat.cast 2 : ℝ)) • (jordan x x + x)]
def flatBase : Triple := ![projectorFrame flatXN,
  projectorFrame (flatScale • flatY1), projectorFrame (flatScale • witnessZ)]
/-- A single automorphism acts on every label of all three frames. -/
def mapAtoms (g : CompactAutomorphism) (T : Triple) : Triple :=
  fun a i => g.equiv (T a i)
/-- Six algebraic readings use an unnormalized input y. -/
def contrast (x y z v : Albert) : ℝ :=
  inner z (U y (U x (U z v)) - U x (U y (U z v)))
def halfAmplitude (x : Albert) : Albert :=
  (1 / (Nat.cast 2 : ℝ)) • ((1 : Albert) + x)
def delta (x y z a rho : Albert) : ℝ := contrast x y z (U a rho)
def score (T : Triple) : ℝ :=
  let x := encoder (T f0)
  let y := encoder (T f1)
  let z := encoder (T f2)
  4 * delta x y z (halfAmplitude x) y -
    delta x y z x y - delta x y z 1 y
/-- Nonzero Phi for arbitrary native elements forces full unital generation
and fixes the pointwise simultaneous automorphism stabilizer. -/
theorem phi_nonzero_generation_stabilizer (x y z : Albert) (hphi : phi x y z ≠ 0) : (∀ K : Submodule ℝ Albert, (1 : Albert) ∈ K → (∀ p ∈ K, ∀ q ∈ K, jordan p q ∈ K) → x ∈ K → y ∈ K → z ∈ K → K = ⊤) ∧ (∀ g : CompactAutomorphism, g.equiv x = x → g.equiv y = y → g.equiv z = z → g.equiv = LinearEquiv.refl ℝ Albert) ∧ (∀ D : Albert →ₗ[ℝ] Albert, (∀ p q, D (jordan p q) = jordan (D p) q + jordan p (D q)) → D x = 0 → D y = 0 → D z = 0 → D = 0) := by
  sorry
/-- On actual ordered frames, Q26 and the complete 54 raw traces determine one another. -/
theorem q26_eq_iff_fullLedger_eq (T S : Triple) (hT : ∀ a, Frame (T a)) (hS : ∀ a, Frame (S a)) : q26 T = q26 S ↔ fullLedger T = fullLedger S := by sorry
/-- Q20 is the final twenty Q26 readings; the first six are fixed on actual frames. -/
def q20 (T : Triple) : Fin 20 → ℝ :=
  fun i => q26 T ⟨i.val + 6, Nat.add_lt_add_right i.2 6⟩
/-- On actual ordered frames, Q20 still determines the complete 54-trace ledger. -/
theorem q20_eq_iff_fullLedger_eq (T S : Triple) (hT : ∀ a, Frame (T a)) (hS : ∀ a, Frame (S a)) : q20 T = q20 S ↔ fullLedger T = fullLedger S := by sorry
/-- The algebraic six-term score equals twice the signed scalar, without division. -/
theorem division_free (x y z : Albert) : 4 * delta x y z (halfAmplitude x) y - delta x y z x y - delta x y z 1 y = 2 * phi x y z := by sorry
/-- The same identity on all three ordered frame encoders. -/
theorem score_eq_two_phi (T : Triple) : score T = 2 * phiOf T := by sorry
/-- Every actual frame triple with nonzero score generates the full unital algebra. -/
theorem atoms_generate_of_score (T : Triple) (hT : ∀ a, Frame (T a)) (hs : score T ≠ 0) (K : Submodule ℝ Albert) (hJ : ∀ p ∈ K, ∀ q ∈ K, jordan p q ∈ K) (hAtoms : ∀ a i, T a i ∈ K) : K = ⊤ := by sorry
/-- Near the flat reference, equal complete ledgers and equal nonzero signs
    imply one simultaneous automorphism on all nine ordered atoms. -/
theorem nearby_sign_rigidity : ∃ V : Set Ledger54, IsOpen V ∧ fullLedger flatBase ∈ V ∧ ∀ T S : Triple, (∀ a : Fin 3, Frame (T a)) → (∀ a : Fin 3, Frame (S a)) → fullLedger T ∈ V → fullLedger T = fullLedger S → ((phiOf T < 0 ∧ phiOf S < 0) ∨ (0 < phiOf T ∧ 0 < phiOf S)) → ∃ k : CompactAutomorphism, mapAtoms k S = T := by sorry
/-- A specific native near-flat full-fiber margin in a supplied open ledger neighborhood. -/
theorem near_flat_scalar_margin : ∃ V : Set Ledger54, IsOpen V ∧ fullLedger flatBase ∈ V ∧ ∀ T : Triple, (∀ a : Fin 3, Frame (T a)) → fullLedger T ∈ V → 1 / 27 < |phiOf T| := by
  sorry
/-- The fixed twenty-coordinate affine chart of complete overlap ledgers. -/
def centred (L : Ledger54) (i j k : Fin 3) : ℝ :=
  L.1 i j k - (L.2.1 i j + L.2.2.1 j k + L.2.2.2 k i) / (Nat.cast 3 : ℝ) + (Nat.cast 2 : ℝ) / (Nat.cast 9 : ℝ)
def encode20 (L : Ledger54) : Fin 20 → ℝ :=
  ![L.2.1 f0 f0 - 1 / (Nat.cast 3 : ℝ), L.2.1 f0 f1 - 1 / (Nat.cast 3 : ℝ), L.2.1 f1 f0 - 1 / (Nat.cast 3 : ℝ), L.2.1 f1 f1 - 1 / (Nat.cast 3 : ℝ),
    L.2.2.1 f0 f0 - 1 / (Nat.cast 3 : ℝ), L.2.2.1 f0 f1 - 1 / (Nat.cast 3 : ℝ), L.2.2.1 f1 f0 - 1 / (Nat.cast 3 : ℝ), L.2.2.1 f1 f1 - 1 / (Nat.cast 3 : ℝ),
    L.2.2.2 f0 f0 - 1 / (Nat.cast 3 : ℝ), L.2.2.2 f0 f1 - 1 / (Nat.cast 3 : ℝ), L.2.2.2 f1 f0 - 1 / (Nat.cast 3 : ℝ), L.2.2.2 f1 f1 - 1 / (Nat.cast 3 : ℝ),
    centred L f0 f0 f0, centred L f0 f0 f1, centred L f0 f1 f0, centred L f0 f1 f1,
    centred L f1 f0 f0, centred L f1 f0 f1, centred L f1 f1 f0, centred L f1 f1 f1]
/-- The chart decoder uses zero-margin 2-by-2 and 2-by-2-by-2 lifts. -/
def ext3 (x y : ℝ) : Fin 3 → ℝ := ![x, y, -(x + y)]
def lift4 (a b c d : ℝ) (i j : Fin 3) : ℝ := ext3 (ext3 a b j) (ext3 c d j) i
def lift8 (h000 h001 h010 h011 h100 h101 h110 h111 : ℝ) (i j k : Fin 3) : ℝ :=
  ext3 (ext3 (ext3 h000 h001 k) (ext3 h010 h011 k) j)
    (ext3 (ext3 h100 h101 k) (ext3 h110 h111 k) j) i
def decP (v : Fin 20 → ℝ) (i j : Fin 3) : ℝ := 1 / (Nat.cast 3 : ℝ) + lift4 (v 0) (v 1) (v 2) (v 3) i j
def decQ (v : Fin 20 → ℝ) (j k : Fin 3) : ℝ := 1 / (Nat.cast 3 : ℝ) + lift4 (v 4) (v 5) (v 6) (v 7) j k
def decR (v : Fin 20 → ℝ) (k i : Fin 3) : ℝ := 1 / (Nat.cast 3 : ℝ) + lift4 (v 8) (v 9) (v 10) (v 11) k i
def decC (v : Fin 20 → ℝ) (i j k : Fin 3) : ℝ :=
  lift8 (v 12) (v 13) (v 14) (v 15) (v 16) (v 17) (v 18) (v 19) i j k +
    (decP v i j + decQ v j k + decR v k i) / (Nat.cast 3 : ℝ) - (Nat.cast 2 : ℝ) / (Nat.cast 9 : ℝ)
def decode20 (v : Fin 20 → ℝ) : Ledger54 := (decC v, decP v, decQ v, decR v)
/-- Full admitted fibers and the simultaneous product-and-trace automorphism orbit. -/
def fibre54 (b : Fin 20 → ℝ) : Set Triple :=
  {T | (∀ a : Fin 3, Frame (T a)) ∧ fullLedger T = decode20 b}
def fibre20 (b : Fin 20 → ℝ) : Set Triple :=
  {T | (∀ a : Fin 3, Frame (T a)) ∧ encode20 (fullLedger T) = b}
def autOrbit (S : Triple) : Set Triple :=
  {T | ∃ g : CompactAutomorphism, mapAtoms g S = T}
/-- Every admitted nearby full fiber is exactly two disjoint simultaneous
    automorphism orbits, with continuous signed sections and exact chart fibers. -/
theorem nearby_fibres_two_orbits : ∃ V : Set (Fin 20 → ℝ), IsOpen V ∧ encode20 (fullLedger flatBase) ∈ V ∧ ∃ secPos secNeg : (Fin 20 → ℝ) → Triple, ContinuousOn (fun b => fun a i => Albert.coordinateEquiv (secPos b a i)) V ∧ ContinuousOn (fun b => fun a i => Albert.coordinateEquiv (secNeg b a i)) V ∧ (∀ b ∈ V, ∀ a : Fin 3, Frame (secPos b a)) ∧ (∀ b ∈ V, ∀ a : Fin 3, Frame (secNeg b a)) ∧ (∀ b ∈ V, encode20 (fullLedger (secPos b)) = b) ∧ (∀ b ∈ V, encode20 (fullLedger (secNeg b)) = b) ∧ (∀ b ∈ V, fullLedger (secPos b) = decode20 b) ∧ (∀ b ∈ V, fullLedger (secNeg b) = decode20 b) ∧ (∀ b ∈ V, 0 < phiOf (secPos b)) ∧ (∀ b ∈ V, phiOf (secNeg b) < 0) ∧ (∀ b ∈ V, fibre54 b = autOrbit (secNeg b) ∪ autOrbit (secPos b)) ∧ (∀ b ∈ V, Disjoint (autOrbit (secNeg b)) (autOrbit (secPos b))) ∧ (∀ b ∈ V, fibre20 b = fibre54 b) := by sorry
/-- On the admitted local chart, Q26 plus the nonzero score sign classifies
all actual ordered-frame triples under one simultaneous product-and-trace action. -/
theorem local_q26_score_orbit_test : ∃ V : Set (Fin 20 → ℝ), IsOpen V ∧ encode20 (fullLedger flatBase) ∈ V ∧ ∀ T S : Triple, (∀ a, Frame (T a)) → (∀ a, Frame (S a)) → encode20 (fullLedger T) ∈ V → score T ≠ 0 ∧ ((∃ k : CompactAutomorphism, mapAtoms k S = T) ↔ q26 T = q26 S ∧ ((score T < 0 ∧ score S < 0) ∨ (0 < score T ∧ 0 < score S))) := by
  sorry
/-- Every compact region of the established admitted chart has a positive
uniform Phi margin for its entire actual ordered-frame fiber. -/
theorem compact_local_phi_margin : ∃ V : Set (Fin 20 → ℝ), IsOpen V ∧ encode20 (fullLedger flatBase) ∈ V ∧ ∀ K : Set V, IsCompact K → ∃ m > 0, ∀ T : Triple, (∀ a : Fin 3, Frame (T a)) → ∀ hb : encode20 (fullLedger T) ∈ V, (⟨encode20 (fullLedger T), hb⟩ : V) ∈ K → m ≤ |phiOf T| := by
  sorry
/-- Six raw algebraic readings, in h+, h-, x+, x-, 1+, 1- order. -/
structure Readouts where
  hPlus : ℝ
  hMinus : ℝ
  xPlus : ℝ
  xMinus : ℝ
  onePlus : ℝ
  oneMinus : ℝ
def weightedScore (r : Readouts) : ℝ :=
  4 * r.hPlus - 4 * r.hMinus - r.xPlus + r.xMinus - r.onePlus + r.oneMinus
def rawPlus (x y z a : Albert) : ℝ :=
  inner z (U y (U x (U z (U a y))))
def rawMinus (x y z a : Albert) : ℝ :=
  inner z (U x (U y (U z (U a y))))
def exactReadouts (T : Triple) : Readouts :=
  let x := encoder (T f0)
  let y := encoder (T f1)
  let z := encoder (T f2)
  ⟨rawPlus x y z (halfAmplitude x), rawMinus x y z (halfAmplitude x),
   rawPlus x y z x, rawMinus x y z x, rawPlus x y z 1, rawMinus x y z 1⟩
def ErrorsAtMost (noisy exact : Readouts) (ε : ℝ) : Prop :=
  |noisy.hPlus - exact.hPlus| ≤ ε ∧
  |noisy.hMinus - exact.hMinus| ≤ ε ∧
  |noisy.xPlus - exact.xPlus| ≤ ε ∧
  |noisy.xMinus - exact.xMinus| ≤ ε ∧
  |noisy.onePlus - exact.onePlus| ≤ ε ∧
  |noisy.oneMinus - exact.oneMinus| ≤ ε
/-- Six absolute-error bounds and a strict observed margin certify the
    native scalar sign; no probability or measurement semantics is assumed. -/
theorem signed_readout_margin (T : Triple) (noisy : Readouts) (ε : ℝ) (hε : 0 ≤ ε) (h : ErrorsAtMost noisy (exactReadouts T) ε) (hm : 12 * ε < |weightedScore noisy|) : (weightedScore noisy < 0 ∧ phiOf T < 0) ∨ (0 < weightedScore noisy ∧ 0 < phiOf T) := by sorry
/-- The native raw trace norm, used to state perturbation radii independently. -/
def nA (x : Albert) : ℝ := Real.sqrt (inner x x)
/-- On a compact feasible chart region, nearby feasible coordinates recover
an actual frame triple up to one simultaneous automorphism, atom by atom.
Both the true and proposed coordinates must belong to the compact region. -/
theorem compact_feasible_element_recovery : ∃ V : Set (Fin 20 → ℝ), IsOpen V ∧ encode20 (fullLedger flatBase) ∈ V ∧ ∃ secPos secNeg : (Fin 20 → ℝ) → Triple, ContinuousOn (fun b => fun a i => Albert.coordinateEquiv (secPos b a i)) V ∧ ContinuousOn (fun b => fun a i => Albert.coordinateEquiv (secNeg b a i)) V ∧ (∀ b ∈ V, ∀ a : Fin 3, Frame (secPos b a)) ∧ (∀ b ∈ V, ∀ a : Fin 3, Frame (secNeg b a)) ∧ (∀ b ∈ V, encode20 (fullLedger (secPos b)) = b) ∧ (∀ b ∈ V, encode20 (fullLedger (secNeg b)) = b) ∧ (∀ b ∈ V, 0 < phiOf (secPos b)) ∧ (∀ b ∈ V, phiOf (secNeg b) < 0) ∧ (∀ K : Set V, IsCompact K → ∀ ζ : ℝ, 0 < ζ → ∃ η > 0, ∀ T : Triple, (∀ a : Fin 3, Frame (T a)) → ∀ hb : encode20 (fullLedger T) ∈ V, (⟨encode20 (fullLedger T), hb⟩ : V) ∈ K → ∀ b : V, b ∈ K → dist (⟨encode20 (fullLedger T), hb⟩ : V) b < η → ∃ g : CompactAutomorphism, ∀ a i : Fin 3, nA (T a i - g.equiv ((if 0 < phiOf T then secPos b.1 else secNeg b.1) a i)) < ζ) := by
  sorry
/-- A strict six-reading margin selects the correct continuous branch for
compact feasible-coordinate recovery. The proposed chart remains feasible. -/
theorem compact_noisy_feasible_element_recovery : ∃ V : Set (Fin 20 → ℝ), IsOpen V ∧ encode20 (fullLedger flatBase) ∈ V ∧ ∃ secPos secNeg : (Fin 20 → ℝ) → Triple, ContinuousOn (fun b => fun a i => Albert.coordinateEquiv (secPos b a i)) V ∧ ContinuousOn (fun b => fun a i => Albert.coordinateEquiv (secNeg b a i)) V ∧ (∀ b ∈ V, ∀ a : Fin 3, Frame (secPos b a)) ∧ (∀ b ∈ V, ∀ a : Fin 3, Frame (secNeg b a)) ∧ (∀ b ∈ V, encode20 (fullLedger (secPos b)) = b) ∧ (∀ b ∈ V, encode20 (fullLedger (secNeg b)) = b) ∧ (∀ b ∈ V, 0 < phiOf (secPos b)) ∧ (∀ b ∈ V, phiOf (secNeg b) < 0) ∧ (∀ K : Set V, IsCompact K → ∀ ζ : ℝ, 0 < ζ → ∃ η > 0, ∀ T : Triple, (∀ a : Fin 3, Frame (T a)) → ∀ hb : encode20 (fullLedger T) ∈ V, (⟨encode20 (fullLedger T), hb⟩ : V) ∈ K → ∀ b : V, b ∈ K → dist (⟨encode20 (fullLedger T), hb⟩ : V) b < η → ∀ noisy : Readouts, ∀ ε : ℝ, 0 ≤ ε → ErrorsAtMost noisy (exactReadouts T) ε → 12 * ε < |weightedScore noisy| → ∃ g : CompactAutomorphism, ∀ a i : Fin 3, nA (T a i - g.equiv ((if 0 < weightedScore noisy then secPos b.1 else secNeg b.1) a i)) < ζ) := by
  sorry
def noisyPhi (r : Readouts) : ℝ := weightedScore r / (Nat.cast 2 : ℝ)
/-- Raw six-readout errors and three bounded input displacements certify the
sign, full unital generation, and pointwise stabilizer at the displaced inputs. -/
theorem six_readout_displaced_generation (T : Triple) (noisy : Readouts) (x' y' z' : Albert) (ε ξ R δ : ℝ) (hξ : 0 ≤ ξ) (hR : 0 ≤ R) (hreadout : ErrorsAtMost noisy (exactReadouts T) ε) (hallowance : 6 * ε ≤ ξ) (hx : nA (encoder (T f0)) ≤ R) (hy : nA (encoder (T f1)) ≤ R) (hz : nA (encoder (T f2)) ≤ R) (hx' : nA x' ≤ R) (hy' : nA y' ≤ R) (hz' : nA z' ≤ R) (hdx : nA (encoder (T f0) - x') ≤ δ) (hdy : nA (encoder (T f1) - y') ≤ δ) (hdz : nA (encoder (T f2) - z') ≤ δ) (hmargin : 18 * R^8 * δ < |noisyPhi noisy| - ξ) : ((noisyPhi noisy < 0 ∧ phi x' y' z' < 0) ∨ (0 < noisyPhi noisy ∧ 0 < phi x' y' z')) ∧ (∀ K : Submodule ℝ Albert, (1 : Albert) ∈ K → (∀ p ∈ K, ∀ q ∈ K, jordan p q ∈ K) → x' ∈ K → y' ∈ K → z' ∈ K → K = ⊤) ∧ (∀ g : CompactAutomorphism, g.equiv x' = x' → g.equiv y' = y' → g.equiv z' = z' → g.equiv = LinearEquiv.refl ℝ Albert) := by
  sorry
/-- The coordinatewise special Jordan product in arbitrary Euclidean dimension. -/
def diagonalNProduct {n : ℕ} (a b : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) := WithLp.toLp (Nat.cast 2 : ENNReal) (fun i => a i * b i)
/-- A uniform all-input defect bounds the degree-nine scalar on any
radius-bounded triple for every finite coordinatewise Euclidean target. -/
theorem diagonalN_defect_response_radius {n : ℕ} (f : Albert →ₗ[ℝ] EuclideanSpace ℝ (Fin n)) (hf : ∀ x : Albert, ‖f x‖ = nA x) (μ R : ℝ) (hμ : 0 ≤ μ) (hR : 0 ≤ R) (hdef : ∀ a b : Albert, ‖f (jordan a b) - diagonalNProduct (f a) (f b)‖ ≤ μ * nA a * nA b) (x y z : Albert) (hx : nA x ≤ R) (hy : nA y ≤ R) (hz : nA z ≤ R) : |phi x y z| ≤ 38 * μ * R^9 := by
  sorry
/-- An actual-frame noisy score forces a uniform multiplication defect for
any norm-preserving linear map into a coordinatewise Euclidean target. -/
theorem frame_noisy_diagonalN_defect_lower {n : ℕ} (f : Albert →ₗ[ℝ] EuclideanSpace ℝ (Fin n)) (hf : ∀ x : Albert, ‖f x‖ = nA x) (T : Triple) (hT : ∀ a : Fin 3, Frame (T a)) (noisy : Readouts) (ε μ : ℝ) (hμ : 0 ≤ μ) (hreadout : ErrorsAtMost noisy (exactReadouts T) ε) (hdef : ∀ a b : Albert, ‖f (jordan a b) - diagonalNProduct (f a) (f b)‖ ≤ μ * nA a * nA b) : (|weightedScore noisy| - 12 * ε) / (1216 * Real.sqrt 2) ≤ μ := by
  sorry
/-- A noisy actual-frame score also forces a defect for an associative
cyclic-trace represented target with its exact product and metric adapters. -/
theorem frame_noisy_represented_defect_lower {E N : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedRing N] [NormedAlgebra ℝ N] (jE : E →ₗ[ℝ] E →ₗ[ℝ] E) (f : Albert →ₗ[ℝ] E) (hf : ∀ x : Albert, ‖f x‖ = nA x) (ρ : E →ₗᵢ[ℝ] N) (τ : N →ₗ[ℝ] ℝ) (hj : ∀ a b : E, ρ (jE a b) = (1 / 2 : ℝ) • (ρ a * ρ b + ρ b * ρ a)) (hB : ∀ a b : E, Inner.inner ℝ a b = τ (ρ a * ρ b)) (hcyclic : ∀ a b : N, τ (a * b) = τ (b * a)) (T : Triple) (hT : ∀ a : Fin 3, Frame (T a)) (noisy : Readouts) (ε μ : ℝ) (hμ : 0 ≤ μ) (hreadout : ErrorsAtMost noisy (exactReadouts T) ε) (hdef : ∀ a b : Albert, ‖f (jordan a b) - jE (f a) (f b)‖ ≤ μ * nA a * nA b) : (|weightedScore noisy| - 12 * ε) / (1216 * Real.sqrt 2) ≤ μ := by
  sorry
/-- The same 27 fixed bracketed words evaluated in any marked product. -/
def witnessX : Albert := ⟨-1,0,1,0,0,0⟩
def witnessY : Albert := ⟨0,0,0,octScalar 1,octI,octScalar 1⟩
def nativeMarks : Fin 3 → Albert := ![witnessX,witnessY,witnessZ]
def wordValues {E : Type*} (e : E) (a : Fin 3 → E) (j : E → E → E) : Fin 27 → E :=
  let x := a f0
  let y := a f1
  let z := a f2
  let xx := j x x
  let xy := j x y
  let xz := j x z
  let yy := j y y
  let yz := j y z
  let zz := j z z
  ![e, x, y, z, xx, xy, xz, yy, yz, zz,
    j x xy, j x xz, j x yy, j x yz, j x zz,
    j y xz, j y yz, j y zz,
    j xx yy, j xx yz, j xx zz, j xy yz, j xy zz, j yy zz,
    j x (j y xz), j x (j y yz), j x (j y zz)]
def nativeWordValues : Fin 27 → Albert := wordValues 1 nativeMarks jordan
def candidateWordValues {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (e : E) (a : Fin 3 → E) (j : E →ₗ[ℝ] E →ₗ[ℝ] E) : Fin 27 → E :=
  wordValues e a (fun x y => j x y)
/-- The generated unital product-closed submodule is independent of the list. -/
def generated {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (e : E) (a : Fin 3 → E) (j : E →ₗ[ℝ] E →ₗ[ℝ] E) : Submodule ℝ E :=
  sInf {K : Submodule ℝ E | e ∈ K ∧ (∀ i, a i ∈ K) ∧
    (∀ x ∈ K, ∀ y ∈ K, j x y ∈ K)}
/-- Three fully determined families of scalar data from the fixed native words. -/
structure Match27 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (e : E) (a : Fin 3 → E) (j : E →ₗ[ℝ] E →ₗ[ℝ] E) : Prop where
  gram : ∀ i k,
    Inner.inner ℝ (candidateWordValues e a j i) (candidateWordValues e a j k) =
      inner (nativeWordValues i) (nativeWordValues k)
  mixed : ∀ i k l,
    Inner.inner ℝ (j (candidateWordValues e a j i) (candidateWordValues e a j k))
      (candidateWordValues e a j l) =
      inner (jordan (nativeWordValues i) (nativeWordValues k)) (nativeWordValues l)
  product_sq : ∀ i k,
    Inner.inner ℝ (j (candidateWordValues e a j i) (candidateWordValues e a j k))
      (j (candidateWordValues e a j i) (candidateWordValues e a j k)) =
      inner (jordan (nativeWordValues i) (nativeWordValues k))
        (jordan (nativeWordValues i) (nativeWordValues k))
/-- Exact finite scalar data uniquely recognize a marked Albert copy inside
    the ambient space, allowing unused ambient directions. -/
theorem finite_word_marked_recognition {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (e : E) (a : Fin 3 → E) (j : E →ₗ[ℝ] E →ₗ[ℝ] E) (h : Match27 e a j) : ∃! L : Albert →ₗ[ℝ] E, L 1 = e ∧ (∀ i : Fin 3, L (nativeMarks i) = a i) ∧ (∀ x y : Albert, L (jordan x y) = j (L x) (L y)) ∧ (∀ x y : Albert, Inner.inner ℝ (L x) (L y) = inner x y) ∧ Function.Injective L ∧ LinearMap.range L = generated e a j := by sorry
end
end Glennie.SubmissionR03
@[expose] public section
namespace Glennie.SubmissionR04Quotient
noncomputable section
open Glennie Glennie.Compact.Affine20 Glennie.SubmissionR03
set_option autoImplicit false
abbrev ChartPoint := Fin 20 → ℝ
abbrev TripleCoordinates := Fin 3 → Fin 3 → Albert.Coordinates
def tripleCoordinates (T : Triple) : TripleCoordinates :=
  fun a i => Albert.coordinateEquiv (T a i)
/-- The honest topology from all nine native coordinate vectors. -/
def tripleCoordinateTopology : TopologicalSpace Triple :=
  TopologicalSpace.induced tripleCoordinates inferInstance
def tripleTopologicalSpace : TopologicalSpace Triple := tripleCoordinateTopology
attribute [local instance] tripleTopologicalSpace
/-- Admission requires actual ordered frames and the exact centered chart. -/
abbrev Admitted (V : Set ChartPoint) :=
  {T : Triple // (∀ a : Fin 3, Frame (T a)) ∧
    Glennie.SubmissionR03.encode20 (fullLedger T) ∈ V}
def invariant (V : Set ChartPoint) (T : Admitted V) : V × Bool :=
  (⟨Glennie.SubmissionR03.encode20 (fullLedger T.1), T.2.2⟩,
    decide (0 < phiOf T.1))
namespace NativeAction
def refl : CompactAutomorphism where
  equiv := LinearEquiv.refl ℝ Albert
  map_jordan x y := by simp only [LinearEquiv.refl_apply]
  map_trace x := by simp only [LinearEquiv.refl_apply]
def comp (g h : CompactAutomorphism) : CompactAutomorphism where
  equiv := h.equiv.trans g.equiv
  map_jordan x y := by simp only [LinearEquiv.trans_apply, h.map_jordan, g.map_jordan]
  map_trace x := by simp only [LinearEquiv.trans_apply, g.map_trace, h.map_trace]
def symm (g : CompactAutomorphism) : CompactAutomorphism where
  equiv := g.equiv.symm
  map_jordan x y := by
    apply g.equiv.injective
    simp only [LinearEquiv.apply_symm_apply, g.map_jordan]
  map_trace x := by
    simpa only [LinearEquiv.apply_symm_apply] using (g.map_trace (g.equiv.symm x)).symm
end NativeAction
/-- One actual simultaneous product-and-trace automorphism, on fixed labels. -/
def orbitSetoid (V : Set ChartPoint) : Setoid (Admitted V) where
  r T S := ∃ g : CompactAutomorphism, Glennie.SubmissionR03.mapAtoms g T.1 = S.1
  iseqv := by
    constructor
    · intro T
      exact ⟨NativeAction.refl, by funext a i; rfl⟩
    · intro T S h
      obtain ⟨g, hg⟩ := h
      refine ⟨NativeAction.symm g, ?_⟩
      rw [← hg]
      funext a i
      exact g.equiv.symm_apply_apply (T.1 a i)
    · intro T S R hTS hSR
      obtain ⟨g, hg⟩ := hTS
      obtain ⟨h, hh⟩ := hSR
      refine ⟨NativeAction.comp h g, ?_⟩
      rw [← hh, ← hg]
      rfl
abbrev OrbitQuotient (V : Set ChartPoint) := Quotient (orbitSetoid V)
local instance (V : Set ChartPoint) : Setoid (Admitted V) := orbitSetoid V
/-- The actual automorphism quotient of all admitted ordered frames is
homeomorphic to the centered feasible chart and its two algebraic sign sheets. -/
theorem admitted_orbit_quotient_homeomorph : ∃ V : Set ChartPoint, IsOpen V ∧ Glennie.SubmissionR03.encode20 (fullLedger flatBase) ∈ V ∧ ∃ H : OrbitQuotient V ≃ₜ V × Bool, (∀ T : Admitted V, H (Quotient.mk' T) = invariant V T) ∧ (∀ T S : Admitted V, (orbitSetoid V).r T S ↔ invariant V T = invariant V S) := by
  sorry
end
end Glennie.SubmissionR04Quotient
@[expose] public section
namespace Glennie.SubmissionR04Intrinsic
noncomputable section
set_option autoImplicit false
structure BasedCubic (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  form : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ
  swap12 : ∀ x y z : E, form ![x, y, z] = form ![y, x, z]
  swap23 : ∀ x y z : E, form ![x, y, z] = form ![x, z, y]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
def cubic (P : BasedCubic E) (x : E) : ℝ := P.form (fun _ : Fin 3 => x)
def metric (P : BasedCubic E) (x : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  (-1 / 3 : ℝ) • fderiv ℝ
    (fun y : E => fderiv ℝ (fun z : E => Real.log (cubic P z)) y) x
def tangent (P : BasedCubic E) (e : E) : Submodule ℝ E :=
  (fderiv ℝ (cubic P) e).ker
def traceAt (P : BasedCubic E) (e : E) : E →L[ℝ] ℝ := fderiv ℝ (cubic P) e
def rawPair (P : BasedCubic E) (e : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  (traceAt P e).smulRight (traceAt P e) -
    fderiv ℝ (fun z : E => fderiv ℝ (cubic P) z) e
def adjoint (P : BasedCubic E) (e x : E) : E :=
  (rawPair P e).inverse (fderiv ℝ (cubic P) x)
def product (P : BasedCubic E) (e x y : E) : E :=
  (1 / 2 : ℝ) • ((adjoint P e (x + y) - adjoint P e x - adjoint P e y) +
    traceAt P e x • y + traceAt P e y • x -
    (traceAt P e x * traceAt P e y - rawPair P e x y) • e)
section TangentOperators
variable (P : BasedCubic E) (e : E)
local notation "W" => tangent P e
local instance tangentDualNormedAddCommGroup : NormedAddCommGroup (W →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := W) (F := ℝ) (σ₁₂ := RingHom.id ℝ)
local instance tangentDualNormedSpace : NormedSpace ℝ (W →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℝ)
    (E := W) (F := ℝ) (σ₁₂ := RingHom.id ℝ)
local instance tangentBilinearNormedAddCommGroup :
    NormedAddCommGroup (W →L[ℝ] W →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := W) (F := W →L[ℝ] ℝ) (σ₁₂ := RingHom.id ℝ)
local instance tangentBilinearNormedSpace : NormedSpace ℝ (W →L[ℝ] W →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℝ)
    (E := W) (F := W →L[ℝ] ℝ) (σ₁₂ := RingHom.id ℝ)
local instance tangentTrilinearNormedAddCommGroup :
    NormedAddCommGroup (W →L[ℝ] W →L[ℝ] W →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := W) (F := W →L[ℝ] W →L[ℝ] ℝ) (σ₁₂ := RingHom.id ℝ)
local instance tangentTrilinearNormedSpace :
    NormedSpace ℝ (W →L[ℝ] W →L[ℝ] W →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℝ)
    (E := W) (F := W →L[ℝ] W →L[ℝ] ℝ) (σ₁₂ := RingHom.id ℝ)
local instance tangentEndNormedAddCommGroup : NormedAddCommGroup (W →L[ℝ] W) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := W) (F := W) (σ₁₂ := RingHom.id ℝ)
local instance tangentEndNormedSpace : NormedSpace ℝ (W →L[ℝ] W) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℝ)
    (E := W) (F := W) (σ₁₂ := RingHom.id ℝ)
local instance tangentVectorBilinearNormedAddCommGroup :
    NormedAddCommGroup (W →L[ℝ] W →L[ℝ] W) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := W) (F := W →L[ℝ] W) (σ₁₂ := RingHom.id ℝ)
local instance tangentVectorBilinearNormedSpace : NormedSpace ℝ (W →L[ℝ] W →L[ℝ] W) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℝ)
    (E := W) (F := W →L[ℝ] W) (σ₁₂ := RingHom.id ℝ)
local instance tangentInverseNormedAddCommGroup :
    NormedAddCommGroup ((W →L[ℝ] ℝ) →L[ℝ] W) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := W →L[ℝ] ℝ) (F := W) (σ₁₂ := RingHom.id ℝ)
local instance tangentInverseNormedSpace : NormedSpace ℝ ((W →L[ℝ] ℝ) →L[ℝ] W) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℝ)
    (E := W →L[ℝ] ℝ) (F := W) (σ₁₂ := RingHom.id ℝ)
/-- The restricted derivative metric, viewed as the tangent-to-dual map. -/
def tangentMetricDual : W →L[ℝ] W →L[ℝ] ℝ :=
  (metric P e).bilinearComp (tangent P e).subtypeL (tangent P e).subtypeL
/-- Total Mathlib inverse; positivity will prove it is the genuine inverse. -/
def tangentMetricRaise : (W →L[ℝ] ℝ) →L[ℝ] W :=
  (tangentMetricDual P e).inverse
/-- Literal restriction of the given form, without any prescribed curvature. -/
def tangentCubicForm : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => W) ℝ :=
  P.form.compContinuousLinearMap (fun _ : Fin 3 => (tangent P e).subtypeL)
def tangentCubicCurried : W →L[ℝ] W →L[ℝ] W →L[ℝ] ℝ :=
  (((continuousMultilinearCurryFin1 ℝ W (W →L[ℝ] ℝ)).toContinuousLinearEquiv).toContinuousLinearMap).comp
    ((tangentCubicForm P e).curryRight.curryLeft)
/-- Raising the last cubic slot by the actual restricted metric. -/
def independentRaisedCubic : W →L[ℝ] W →L[ℝ] W :=
  ((ContinuousLinearMap.compL ℝ W (W →L[ℝ] ℝ) W)
    (tangentMetricRaise P e)).comp (tangentCubicCurried P e)
/-- Full basepoint formula; its equality to actual curvature is a theorem below. -/
def independentCurvature (u v w : W) : W :=
  -(tangentMetricDual P e v w) • u + (tangentMetricDual P e u w) • v -
    independentRaisedCubic P e u (independentRaisedCubic P e v w) +
    independentRaisedCubic P e v (independentRaisedCubic P e u w)
end TangentOperators
local instance taskAmbientDualNorm : NormedAddCommGroup (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ) (E := E) (F := ℝ) (σ₁₂ := RingHom.id ℝ)
local instance taskAmbientDualSpace : NormedSpace ℝ (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℝ) (E := E) (F := ℝ) (σ₁₂ := RingHom.id ℝ)
local instance taskAmbientBilinearNorm : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ) (E := E) (F := E →L[ℝ] ℝ) (σ₁₂ := RingHom.id ℝ)
local instance taskAmbientBilinearSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℝ) (E := E) (F := E →L[ℝ] ℝ) (σ₁₂ := RingHom.id ℝ)
local instance taskAmbientTrilinearNorm : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ) (E := E) (F := E →L[ℝ] E →L[ℝ] ℝ) (σ₁₂ := RingHom.id ℝ)
local instance taskAmbientTrilinearSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℝ) (E := E) (F := E →L[ℝ] E →L[ℝ] ℝ) (σ₁₂ := RingHom.id ℝ)
local instance taskAmbientEndNorm : NormedAddCommGroup (E →L[ℝ] E) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ) (E := E) (F := E) (σ₁₂ := RingHom.id ℝ)
local instance taskAmbientEndSpace : NormedSpace ℝ (E →L[ℝ] E) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℝ) (E := E) (F := E) (σ₁₂ := RingHom.id ℝ)
local instance taskAmbientVectorBilinearNorm : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ) (E := E) (F := E →L[ℝ] E) (σ₁₂ := RingHom.id ℝ)
local instance taskAmbientVectorBilinearSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℝ) (E := E) (F := E →L[ℝ] E) (σ₁₂ := RingHom.id ℝ)
local instance taskAmbientInverseNorm : NormedAddCommGroup ((E →L[ℝ] ℝ) →L[ℝ] E) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ) (E := E →L[ℝ] ℝ) (F := E) (σ₁₂ := RingHom.id ℝ)
local instance taskAmbientInverseSpace : NormedSpace ℝ ((E →L[ℝ] ℝ) →L[ℝ] E) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℝ) (E := E →L[ℝ] ℝ) (F := E) (σ₁₂ := RingHom.id ℝ)
/-- Literal derivative of the varying normalized log-Hessian metric. -/
def ambientMetricD1 (P : BasedCubic E) (x : E) : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ := fderiv ℝ (metric P) x
/-- Three-term affine Koszul covector, before any Hessian-symmetry shortcut. -/
def ambientKoszulTensor (P : BasedCubic E) (x : E) : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ :=
  (1 / 2 : ℝ) • (ambientMetricD1 P x + (ambientMetricD1 P x).flip -
    ((((ContinuousLinearMap.flipₗᵢ ℝ E E ℝ).toContinuousLinearEquiv).toContinuousLinearMap :
      (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ).comp
      (ambientMetricD1 P x).flip))
/-- Actual ambient affine connection coefficient. Positivity later proves that
the total metric inverse is the genuine inverse near the normalized base. -/
def ambientConnection (P : BasedCubic E) (x : E) : E →L[ℝ] E →L[ℝ] E :=
  ((ContinuousLinearMap.compL ℝ E (E →L[ℝ] ℝ) E)
    (metric P x).inverse).comp (ambientKoszulTensor P x)
/-- Actual covariant derivative in a constant affine direction. -/
def ambientCovariantDerivative (P : BasedCubic E) (u : E) (Y : E → E) (x : E) : E :=
  fderiv ℝ Y x u + ambientConnection P x u (Y x)
/-- Actual curvature on all ambient vectors. The constant direction fields
commute, so their Lie bracket vanishes. This is not a product definition. -/
def ambientCurvature (P : BasedCubic E) (x u v w : E) : E :=
  ambientCovariantDerivative P u (ambientCovariantDerivative P v (fun _ : E => w)) x -
    ambientCovariantDerivative P v (ambientCovariantDerivative P u (fun _ : E => w)) x
end
end Glennie.SubmissionR04Intrinsic
namespace Glennie.SubmissionR04Intrinsic.Local
noncomputable section
set_option autoImplicit false
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
abbrev Triple (E : Type*) := Fin 3 → Fin 3 → E
abbrev Ledger54 := Glennie.Compact.Affine20.Ledger54
abbrev Chart := Fin 20 → ℝ
structure Frame (e : E) (t : E → ℝ) (j : E → E → E) (p : Fin 3 → E) : Prop where
  trace_one : ∀ i, t (p i) = 1
  idempotent : ∀ i, j (p i) (p i) = p i
  orthogonal : ∀ i k, i ≠ k → j (p i) (p k) = 0
  sum_unit : p 0 + p 1 + p 2 = e
def encoder (p : Fin 3 → E) : E := p 2 - p 0
def pairing (t : E → ℝ) (j : E → E → E) (x y : E) : ℝ := t (j x y)
def quad (j : E → E → E) (x z : E) : E :=
  (2 : ℝ) • j x (j x z) - j (j x x) z
def phi (t : E → ℝ) (j : E → E → E) (x y z : E) : ℝ :=
  pairing t j (quad j x (quad j y z) - quad j y (quad j x z))
    (quad j z (j x y))
def ledger (t : E → ℝ) (j : E → E → E) (T : Triple E) : Ledger54 :=
  (fun i k l => t (j (j (T 0 i) (T 1 k)) (T 2 l)),
   fun i k => pairing t j (T 0 i) (T 1 k),
   fun k l => pairing t j (T 1 k) (T 2 l),
   fun l i => pairing t j (T 2 l) (T 0 i))
def power (j : E → E → E) (p : Fin 3 → E) (s : Fin 2) : E :=
  if s = 0 then encoder p else j (encoder p) (encoder p)
def qSingle (t : E → ℝ) (j : E → E → E) (T : Triple E) (v : Fin 3) (s : Fin 2) : ℝ :=
  pairing t j (power j (T v) 0) (power j (T v) s)
def qPair (t : E → ℝ) (j : E → E → E) (T : Triple E) (v w : Fin 3) (s r : Fin 2) : ℝ :=
  pairing t j (power j (T v) s) (power j (T w) r)
def qTriple (t : E → ℝ) (j : E → E → E) (T : Triple E) (s r u : Fin 2) : ℝ :=
  t (j (j (power j (T 0) s) (power j (T 1) r)) (power j (T 2) u))
def q26 (t : E → ℝ) (j : E → E → E) (T : Triple E) : Fin 26 → ℝ := ![
  qSingle t j T 0 0, qSingle t j T 0 1,
  qSingle t j T 1 0, qSingle t j T 1 1,
  qSingle t j T 2 0, qSingle t j T 2 1,
  qPair t j T 0 1 0 0, qPair t j T 0 1 0 1,
  qPair t j T 0 1 1 0, qPair t j T 0 1 1 1,
  qPair t j T 1 2 0 0, qPair t j T 1 2 0 1,
  qPair t j T 1 2 1 0, qPair t j T 1 2 1 1,
  qPair t j T 2 0 0 0, qPair t j T 2 0 0 1,
  qPair t j T 2 0 1 0, qPair t j T 2 0 1 1,
  qTriple t j T 0 0 0, qTriple t j T 0 0 1,
  qTriple t j T 0 1 0, qTriple t j T 0 1 1,
  qTriple t j T 1 0 0, qTriple t j T 1 0 1,
  qTriple t j T 1 1 0, qTriple t j T 1 1 1]
def half (e x : E) : E := (1 / 2 : ℝ) • (e + x)
def contrast (t : E → ℝ) (j : E → E → E) (x y z v : E) : ℝ :=
  pairing t j z
    (quad j y (quad j x (quad j z v)) - quad j x (quad j y (quad j z v)))
def delta (t : E → ℝ) (j : E → E → E) (x y z a rho : E) : ℝ :=
  contrast t j x y z (quad j a rho)
def score (e : E) (t : E → ℝ) (j : E → E → E) (T : Triple E) : ℝ :=
  let x := encoder (T 0)
  let y := encoder (T 1)
  let z := encoder (T 2)
  4 * delta t j x y z (half e x) y - delta t j x y z x y - delta t j x y z e y
structure Automorphism (t : E → ℝ) (j : E → E → E) where
  equiv : E ≃ₗ[ℝ] E
  map_product : ∀ x y, equiv (j x y) = j (equiv x) (equiv y)
  map_trace : ∀ x, t (equiv x) = t x
def mapAtoms {t : E → ℝ} {j : E → E → E} (g : Automorphism t j) (T : Triple E) : Triple E := fun a i => g.equiv (T a i)
def orbit (t : E → ℝ) (j : E → E → E) (S : Triple E) : Set (Triple E) :=
  {T | ∃ g : Automorphism t j, mapAtoms g S = T}
def fibre54 (e : E) (t : E → ℝ) (j : E → E → E) (b : Chart) : Set (Triple E) :=
  {T | (∀ a, Frame e t j (T a)) ∧ ledger t j T = Glennie.SubmissionR03.decode20 b}
def fibre20 (e : E) (t : E → ℝ) (j : E → E → E) (b : Chart) : Set (Triple E) :=
  {T | (∀ a, Frame e t j (T a)) ∧ Glennie.SubmissionR03.encode20 (ledger t j T) = b}
def SameSign (e : E) (t : E → ℝ) (j : E → E → E) (T S : Triple E) : Prop :=
  (score e t j T < 0 ∧ score e t j S < 0) ∨
    (0 < score e t j T ∧ 0 < score e t j S)
def Admitted (e : E) (t : E → ℝ) (j : E → E → E) (V : Set Chart) (T : Triple E) : Prop :=
  (∀ a, Frame e t j (T a)) ∧ Glennie.SubmissionR03.encode20 (ledger t j T) ∈ V
def TwoOrbitSections (e : E) (t : E → ℝ) (j : E → E → E) (V : Set Chart) : Prop :=
  ∃ secPos secNeg : Chart → Triple E,
    ContinuousOn secPos V ∧ ContinuousOn secNeg V ∧
    (∀ b ∈ V, ∀ a, Frame e t j (secPos b a)) ∧
    (∀ b ∈ V, ∀ a, Frame e t j (secNeg b a)) ∧
    (∀ b ∈ V, ledger t j (secPos b) = Glennie.SubmissionR03.decode20 b) ∧
    (∀ b ∈ V, ledger t j (secNeg b) = Glennie.SubmissionR03.decode20 b) ∧
    (∀ b ∈ V, 0 < score e t j (secPos b)) ∧
    (∀ b ∈ V, score e t j (secNeg b) < 0) ∧
    (∀ b ∈ V, fibre54 e t j b = orbit t j (secNeg b) ∪ orbit t j (secPos b)) ∧
    (∀ b ∈ V, Disjoint (orbit t j (secNeg b)) (orbit t j (secPos b))) ∧
    (∀ b ∈ V, fibre20 e t j b = fibre54 e t j b)
def ScoreComplete (e : E) (t : E → ℝ) (j : E → E → E) (V : Set Chart) : Prop :=
  ∀ T S : Triple E, (∀ a, Frame e t j (T a)) → (∀ a, Frame e t j (S a)) →
    Glennie.SubmissionR03.encode20 (ledger t j T) ∈ V →
    score e t j T ≠ 0 ∧
      ((T ∈ orbit t j S) ↔ q26 t j T = q26 t j S ∧ SameSign e t j T S)
/-- OUTPUT data. The final public theorem must construct this record. -/
structure Result (e : E) (N : E → ℝ) (t : E → ℝ) (a B : E → E → ℝ) (j Gamma : E → E → E) (R : E → E → E → E) (nativeN : Glennie.Albert → ℝ) where
  A : E ≃ₗ[ℝ] Glennie.Albert
  map_unit : A e = 1
  map_norm : ∀ x, nativeN (A x) = N x
  map_metric : ∀ x y, a x y = Glennie.inner (A x) (A y) / 3
  map_raw_pairing : ∀ x y, B x y = Glennie.inner (A x) (A y)
  map_trace : ∀ x, t x = Glennie.trace (A x)
  map_product : ∀ x y, A (j x y) = Glennie.jordan (A x) (A y)
  map_connection : ∀ x y, A (Gamma x y) = -Glennie.jordan (A x) (A y)
  map_curvature : ∀ u v w, A (R u v w) =
    -(Glennie.jordan (A u) (Glennie.jordan (A v) (A w)) -
      Glennie.jordan (A v) (Glennie.jordan (A u) (A w)))
  V : Set Chart
  V_open : IsOpen V
  flat_mem : Glennie.SubmissionR03.encode20
    (ledger t j (fun f i => A.symm (Glennie.SubmissionR03.flatBase f i))) ∈ V
  two_orbits : TwoOrbitSections e t j V
  score_complete : ScoreComplete e t j V
  q26_iff_ledger : ∀ T S : Triple E,
    (∀ f, Frame e t j (T f)) → (∀ f, Frame e t j (S f)) →
    (q26 t j T = q26 t j S ↔ ledger t j T = ledger t j S)
  score_eq_two_phi : ∀ T : Triple E,
    score e t j T = 2 * phi t j (encoder (T 0)) (encoder (T 1)) (encoder (T 2))
  atoms_generate : ∀ T : Triple E, Admitted e t j V T →
    ∀ K : Submodule ℝ E, (∀ p ∈ K, ∀ q ∈ K, j p q ∈ K) →
      (∀ f i, T f i ∈ K) → K = ⊤
  atom_stabilizer : ∀ T : Triple E, Admitted e t j V T →
    ∀ g : Automorphism t j, mapAtoms g T = T → g.equiv = LinearEquiv.refl ℝ E
  atom_derivation : ∀ T : Triple E, Admitted e t j V T →
    ∀ D : E →ₗ[ℝ] E, (∀ p q, D (j p q) = j (D p) q + j p (D q)) →
      (∀ f i, D (T f i) = 0) → D = 0
end
end Glennie.SubmissionR04Intrinsic.Local
@[expose] public section
namespace Glennie.SubmissionR04Intrinsic
noncomputable section
set_option autoImplicit false
def nativeCubic (x : Albert) : ℝ :=
  (Glennie.trace x ^ 3 - 3 * Glennie.trace x * Glennie.inner x x +
    2 * Glennie.inner x (jordan x x)) / 6
theorem nativeTrace_add (x y : Albert) :
    Glennie.trace (x + y) = Glennie.trace x + Glennie.trace y := by
  have h0 : (x+y).d0 = x.d0+y.d0 := rfl
  have h1 : (x+y).d1 = x.d1+y.d1 := rfl
  have h2 : (x+y).d2 = x.d2+y.d2 := rfl
  simp only [Glennie.trace, h0, h1, h2]
  ring
theorem nativeTrace_smul (r : ℝ) (x : Albert) :
    Glennie.trace (r • x) = r • Glennie.trace x := by
  have h0 : (r • x).d0 = r*x.d0 := rfl
  have h1 : (r • x).d1 = r*x.d1 := rfl
  have h2 : (r • x).d2 = r*x.d2 := rfl
  simp only [Glennie.trace, h0, h1, h2, smul_eq_mul]
  ring
def nativeTraceLinear : Albert →ₗ[ℝ] ℝ where
  toFun := Glennie.trace
  map_add' := nativeTrace_add
  map_smul' := nativeTrace_smul
abbrev NativeTangent := nativeTraceLinear.ker
def nativeProject (x : Albert) : NativeTangent := by
  refine ⟨x - (Glennie.trace x / 3) • (1 : Albert), ?_⟩
  change nativeTraceLinear (x - (Glennie.trace x / 3) • (1 : Albert)) = 0
  rw [map_sub, map_smul]
  have hu : nativeTraceLinear (1 : Albert) = 3 := by
    change (1 : ℝ) + 1 + 1 = 3
    norm_num
  rw [hu]
  change Glennie.trace x - (Glennie.trace x / 3) * 3 = 0
  ring
def nativeMetric (u v : NativeTangent) : ℝ :=
  Glennie.inner (u : Albert) (v : Albert) / 3
def nativeK (u v : NativeTangent) : NativeTangent :=
  nativeProject (Glennie.jordan (u : Albert) (v : Albert))
def nativeCurvature (u v w : NativeTangent) : NativeTangent :=
  -(nativeMetric v w) • u + (nativeMetric u w) • v -
    nativeK u (nativeK v w) + nativeK v (nativeK u w)
abbrev ReconstructionResult {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (P : BasedCubic E) (e : E) :=
  Local.Result e (cubic P) (fun x => traceAt P e x)
    (fun x y => metric P e x y) (fun x y => rawPair P e x y) (product P e)
    (fun x y => ambientConnection P e x y) (ambientCurvature P e) nativeCubic
/-- Local reconstruction from a based cubic and one full vector-curvature tangent frame. -/
theorem intrinsic_local_reconstruction {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E] (P : BasedCubic E) (e : E) (he : cubic P e = 1) (hp : ∀ x : E, x ≠ 0 → 0 < metric P e x x) (hMatch : ∃ F : NativeTangent ≃ₗ[ℝ] tangent P e, (∀ x y : NativeTangent, metric P e (F x : E) (F y : E) = nativeMetric x y) ∧ (∀ x y z : NativeTangent, independentCurvature P e (F x) (F y) (F z) = F (nativeCurvature x y z))) : Nonempty (ReconstructionResult P e) := by
  sorry
end
end Glennie.SubmissionR04Intrinsic
@[expose] public section
namespace Glennie
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

@[simp] theorem Albert.zero_d0 : (0 : Albert).d0 = 0 := rfl
@[simp] theorem Albert.zero_d1 : (0 : Albert).d1 = 0 := rfl
@[simp] theorem Albert.zero_d2 : (0 : Albert).d2 = 0 := rfl
@[simp] theorem Albert.zero_o01 : (0 : Albert).o01 = 0 := rfl
@[simp] theorem Albert.zero_o02 : (0 : Albert).o02 = 0 := rfl
@[simp] theorem Albert.zero_o12 : (0 : Albert).o12 = 0 := rfl
@[simp] theorem Albert.add_d0 (x y : Albert) : (x+y).d0 = x.d0+y.d0 := rfl
@[simp] theorem Albert.add_d1 (x y : Albert) : (x+y).d1 = x.d1+y.d1 := rfl
@[simp] theorem Albert.add_d2 (x y : Albert) : (x+y).d2 = x.d2+y.d2 := rfl
@[simp] theorem Albert.add_o01 (x y : Albert) : (x+y).o01 = x.o01+y.o01 := rfl
@[simp] theorem Albert.add_o02 (x y : Albert) : (x+y).o02 = x.o02+y.o02 := rfl
@[simp] theorem Albert.add_o12 (x y : Albert) : (x+y).o12 = x.o12+y.o12 := rfl
@[simp] theorem Albert.smul_d0 (r : ℝ) (x : Albert) : (r • x).d0 = r*x.d0 := rfl
@[simp] theorem Albert.smul_d1 (r : ℝ) (x : Albert) : (r • x).d1 = r*x.d1 := rfl
@[simp] theorem Albert.smul_d2 (r : ℝ) (x : Albert) : (r • x).d2 = r*x.d2 := rfl
@[simp] theorem Albert.smul_o01 (r : ℝ) (x : Albert) : (r • x).o01 = r • x.o01 := rfl
@[simp] theorem Albert.smul_o02 (r : ℝ) (x : Albert) : (r • x).o02 = r • x.o02 := rfl
@[simp] theorem Albert.smul_o12 (r : ℝ) (x : Albert) : (r • x).o12 = r • x.o12 := rfl

def octDot (x y : Octonion) : ℝ := octRe (octMul x (octConj y))
def octNormSq (x : Octonion) : ℝ := Quaternion.normSq x.1 + Quaternion.normSq x.2

theorem octDot_coordinates (x y : Octonion) :
    octDot x y = x.1.re*y.1.re + x.1.imI*y.1.imI + x.1.imJ*y.1.imJ +
      x.1.imK*y.1.imK + x.2.re*y.2.re + x.2.imI*y.2.imI +
      x.2.imJ*y.2.imJ + x.2.imK*y.2.imK := by
  simp [octDot, octRe, octMul, octConj, Quaternion.re_mul]
  ring

@[simp] theorem octDot_self (x : Octonion) : octDot x x = octNormSq x := by
  rw [octDot_coordinates]
  simp [octNormSq, Quaternion.normSq_def']
  ring

theorem octNormSq_nonneg (x : Octonion) : 0 ≤ octNormSq x :=
  add_nonneg (Quaternion.normSq_nonneg (a := x.1)) (Quaternion.normSq_nonneg (a := x.2))

theorem octNormSq_eq_zero (x : Octonion) : octNormSq x = 0 ↔ x = 0 := by
  rw [octNormSq, add_eq_zero_iff_of_nonneg
    (Quaternion.normSq_nonneg (a := x.1)) (Quaternion.normSq_nonneg (a := x.2))]
  constructor
  · rintro ⟨h1, h2⟩
    exact Prod.ext (Quaternion.normSq_eq_zero.mp h1) (Quaternion.normSq_eq_zero.mp h2)
  · intro h
    cases h
    exact ⟨Quaternion.normSq_eq_zero.mpr rfl, Quaternion.normSq_eq_zero.mpr rfl⟩

theorem jordan_comm (x y : Albert) : jordan x y = jordan y x := by
  unfold jordan
  rw [add_comm]

attribute [-instance] FloorSemiring.instCharZero RCLike.charZero_rclike in
theorem jordan_d0 (x y : Albert) :
    (jordan x y).d0 = x.d0*y.d0 + octDot x.o01 y.o01 + octDot x.o02 y.o02 := by
  simp [jordan, fromMatrix, matrixMul, toMatrix, Fin.sum_univ_three,
    octRe, octScalar, octMul, octConj, octDot, Quaternion.re_mul]
  ring

attribute [-instance] FloorSemiring.instCharZero RCLike.charZero_rclike in
theorem jordan_d1 (x y : Albert) :
    (jordan x y).d1 = x.d1*y.d1 + octDot x.o01 y.o01 + octDot x.o12 y.o12 := by
  simp [jordan, fromMatrix, matrixMul, toMatrix, Fin.sum_univ_three,
    octRe, octScalar, octMul, octConj, octDot, Quaternion.re_mul]
  ring

attribute [-instance] FloorSemiring.instCharZero RCLike.charZero_rclike in
theorem jordan_d2 (x y : Albert) :
    (jordan x y).d2 = x.d2*y.d2 + octDot x.o02 y.o02 + octDot x.o12 y.o12 := by
  simp [jordan, fromMatrix, matrixMul, toMatrix, Fin.sum_univ_three,
    octRe, octScalar, octMul, octConj, octDot, Quaternion.re_mul]
  ring

theorem inner_coordinates (x y : Albert) :
    inner x y = x.d0*y.d0+x.d1*y.d1+x.d2*y.d2 +
      2*(octDot x.o01 y.o01+octDot x.o02 y.o02+octDot x.o12 y.o12) := by
  simp only [inner, trace, jordan_d0, jordan_d1, jordan_d2]
  ring

theorem inner_comm (x y : Albert) : inner x y = inner y x := by
  simp only [inner, jordan_comm]

theorem inner_self_coordinates (x : Albert) :
    inner x x = x.d0^2+x.d1^2+x.d2^2 +
      2*(octNormSq x.o01+octNormSq x.o02+octNormSq x.o12) := by
  simp only [inner_coordinates, octDot_self]
  ring

theorem inner_self_nonneg (x : Albert) : 0 ≤ inner x x := by
  rw [inner_self_coordinates]
  exact add_nonneg (add_nonneg (add_nonneg (sq_nonneg x.d0) (sq_nonneg x.d1))
    (sq_nonneg x.d2)) (mul_nonneg (by norm_num)
      (add_nonneg (add_nonneg (octNormSq_nonneg x.o01) (octNormSq_nonneg x.o02))
        (octNormSq_nonneg x.o12)))

attribute [-instance] FloorSemiring.instCharZero RCLike.charZero_rclike in
theorem inner_self_eq_zero (x : Albert) : inner x x = 0 ↔ x = 0 := by
  constructor
  · intro h
    rw [inner_self_coordinates] at h
    have h01 := octNormSq_nonneg x.o01
    have h02 := octNormSq_nonneg x.o02
    have h12 := octNormSq_nonneg x.o12
    have hd0 : x.d0 = 0 := by nlinarith [sq_nonneg x.d1, sq_nonneg x.d2]
    have hd1 : x.d1 = 0 := by nlinarith [sq_nonneg x.d0, sq_nonneg x.d2]
    have hd2 : x.d2 = 0 := by nlinarith [sq_nonneg x.d0, sq_nonneg x.d1]
    have ho01 : x.o01 = 0 := (octNormSq_eq_zero _).mp
      (by nlinarith [sq_nonneg x.d0, sq_nonneg x.d1, sq_nonneg x.d2])
    have ho02 : x.o02 = 0 := (octNormSq_eq_zero _).mp
      (by nlinarith [sq_nonneg x.d0, sq_nonneg x.d1, sq_nonneg x.d2])
    have ho12 : x.o12 = 0 := (octNormSq_eq_zero _).mp
      (by nlinarith [sq_nonneg x.d0, sq_nonneg x.d1, sq_nonneg x.d2])
    apply Albert.extExplicit <;> simp [hd0, hd1, hd2, ho01, ho02, ho12]
  · rintro rfl
    simp [inner_self_coordinates, octNormSq, Quaternion.normSq_def']

theorem inner_add_left (x y z : Albert) : inner (x+y) z = inner x z+inner y z := by
  simp [inner_coordinates, octDot_coordinates]
  ring

theorem inner_add_right (x y z : Albert) : inner x (y+z) = inner x y+inner x z := by
  rw [inner_comm, inner_add_left, inner_comm x y, inner_comm x z]

theorem inner_smul_left (r : ℝ) (x y : Albert) : inner (r • x) y = r * inner x y := by
  simp [inner_coordinates, octDot_coordinates, smul_eq_mul]
  ring

theorem inner_smul_right (r : ℝ) (x y : Albert) : inner x (r • y) = r * inner x y := by
  rw [inner_comm, inner_smul_left, inner_comm x y]

def Albert.coordinateLinearEquiv : Albert ≃ₗ[ℝ] Albert.Coordinates where
  __ := Albert.coordinateAddEquiv
  map_smul' _ _ := rfl

instance : FiniteDimensional ℝ Albert := by
  letI : FiniteDimensional ℝ Albert.Coordinates := Module.Finite.prod
  exact Albert.coordinateLinearEquiv.symm.finiteDimensional

instance : Inner ℝ Albert := ⟨Glennie.inner⟩

@[instance_reducible] def nativeInnerCore : InnerProductSpace.Core ℝ Albert where
  toInner := inferInstance
  conj_inner_symm x y := by
    change inner y x = inner x y
    exact inner_comm y x
  re_inner_nonneg := inner_self_nonneg
  definite x := (inner_self_eq_zero x).mp
  add_left := inner_add_left
  smul_left x y r := by
    change inner (r • x) y = r * inner x y
    exact inner_smul_left r x y

instance : NormedAddCommGroup Albert := nativeInnerCore.toNormedAddCommGroup

instance : InnerProductSpace ℝ Albert :=
  InnerProductSpace.ofCore nativeInnerCore.toCore

section StableNativePairing
set_option backward.isDefEq.respectTransparency false
theorem nativeRealSMulComm : SMulCommClass ℝ ℝ ℝ := inferInstance
theorem nativeRealContinuousAdd : ContinuousAdd ℝ := inferInstance
theorem nativeRealContinuousSMul : ContinuousConstSMul ℝ ℝ := inferInstance
attribute [local instance 20000] nativeRealSMulComm nativeRealContinuousAdd nativeRealContinuousSMul
def nativeInnerLinear : Albert →ₗ[ℝ] Albert →ₗ[ℝ] ℝ where
  toFun x :=
    { toFun := inner x
      map_add' y z := inner_add_right x y z
      map_smul' r y := inner_smul_right r x y }
  map_add' x y := by ext z; exact inner_add_left x y z
  map_smul' r x := by ext y; exact inner_smul_left r x y

theorem nativeInnerRight_cont (x : Albert) : Continuous (fun y => inner x y) :=
  (nativeInnerLinear x).continuous_of_finiteDimensional
def nativeInnerRight (x : Albert) : Albert →L[ℝ] ℝ where
  toLinearMap := nativeInnerLinear x
  cont := nativeInnerRight_cont x
theorem nativeInnerRight_add (x y : Albert) :
    nativeInnerRight (x + y) = nativeInnerRight x + nativeInnerRight y :=
  ContinuousLinearMap.ext (fun z => inner_add_left x y z)
theorem nativeInnerRight_smul (r : ℝ) (x : Albert) :
    nativeInnerRight (r • x) = r • nativeInnerRight x :=
  ContinuousLinearMap.ext (fun y => inner_smul_left r x y)
def nativeInnerRightLinear : Albert →ₗ[ℝ] (Albert →L[ℝ] ℝ) where
  toFun := nativeInnerRight
  map_add' := nativeInnerRight_add
  map_smul' := nativeInnerRight_smul
theorem nativeInnerRightLinear_cont : Continuous nativeInnerRightLinear :=
  nativeInnerRightLinear.continuous_of_finiteDimensional
def nativeInnerContinuous : Albert →L[ℝ] Albert →L[ℝ] ℝ where
  toLinearMap := nativeInnerRightLinear
  cont := nativeInnerRightLinear_cont
end StableNativePairing

end
end Glennie
@[expose] public section
namespace Glennie.Compact.GlennieScalarPotentialR01
open Glennie
noncomputable section
set_option autoImplicit false

def commU (x y z : Albert) : Albert := U x (U y z) - U y (U x z)

def doubledTriple (a z b : Albert) : Albert :=
  (2 : ℝ) • (jordan a (jordan z b) + jordan (jordan a z) b - jordan (jordan a b) z)

def glennieVector (x y z : Albert) : Albert :=
  doubledTriple (commU x y z) z (jordan x y) - commU x y (U z (jordan x y))

end
end Glennie.Compact.GlennieScalarPotentialR01

@[expose] public section
namespace Glennie.Compact.GlennieFullDerivativeR01
open Glennie
open Glennie.Compact.GlennieScalarPotentialR01
noncomputable section
set_option autoImplicit false

abbrev NativeTriple := Albert × (Albert × Albert)

def phiTriple (p : NativeTriple) : ℝ := phi p.1 p.2.1 p.2.2

section StableFullDerivative
set_option backward.isDefEq.respectTransparency false
attribute [local instance 20000] Glennie.nativeRealSMulComm Glennie.nativeRealContinuousAdd Glennie.nativeRealContinuousSMul
def fullDerivative (x y z : Albert) : NativeTriple →L[ℝ] ℝ :=
  (nativeInnerContinuous (glennieVector y z x)).coprod
    ((nativeInnerContinuous (glennieVector z x y)).coprod
      (nativeInnerContinuous (glennieVector x y z)))
end StableFullDerivative

/-- Actual full native differential of the literal degree-nine Phi. -/
theorem hasFDerivAt_phiTriple (x y z : Albert) :
    HasFDerivAt phiTriple (fullDerivative x y z) (x, y, z) := by
  sorry

/-- A nonzero actual ambient full differential suffices for unital generation. -/
theorem eq_top_of_fderiv_phiTriple_ne_zero
    (K : Submodule ℝ Albert)
    (h1 : (1 : Albert) ∈ K)
    (hJ : ∀ p ∈ K, ∀ q ∈ K, jordan p q ∈ K)
    (x y z : Albert) (hx : x ∈ K) (hy : y ∈ K) (hz : z ∈ K)
    (hne : fderiv ℝ phiTriple (x, y, z) ≠ 0) : K = ⊤ := by
  sorry

end
end Glennie.Compact.GlennieFullDerivativeR01
