/- Unified independent native and admitted orbit-quotient statement surface. -/
module
public import Glennie.Compact.ExceptionalWorkingPackageR02
public import Mathlib.Analysis.Quaternion
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Maps.Basic
public import AlbertGeometry.IntrinsicLocalGenerationCapstoneR01
public import AlbertGeometry.BasedNormAdjointTransport
public import AlbertGeometry.ActualU2NativeGeometry
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Normed.Module.Multilinear.Curry
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Topology.Algebra.Module.FiniteDimension

@[expose] public section

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
theorem phi_nonzero_generation_stabilizer
    (x y z : Albert) (hphi : phi x y z ≠ 0) :
    (∀ K : Submodule ℝ Albert, (1 : Albert) ∈ K →
      (∀ p ∈ K, ∀ q ∈ K, jordan p q ∈ K) →
      x ∈ K → y ∈ K → z ∈ K → K = ⊤) ∧
    (∀ g : CompactAutomorphism,
      g.equiv x = x → g.equiv y = y → g.equiv z = z →
      g.equiv = LinearEquiv.refl ℝ Albert) ∧
    (∀ D : Albert →ₗ[ℝ] Albert,
      (∀ p q, D (jordan p q) = jordan (D p) q + jordan p (D q)) →
      D x = 0 → D y = 0 → D z = 0 → D = 0) := by
  refine ⟨?_, ?_, ?_⟩
  · intro K h1 hJ hx hy hz
    exact Glennie.NativeGenerationEndpointR01.eq_top_of_phi_ne_zero
      K h1 hJ x y z hx hy hz hphi
  · intro g hx hy hz
    have hg := Glennie.NativeGenerationStabilizersR01.automorphism_eq_refl_of_phi_ne_zero
      g x y z hphi hx hy hz
    rw [hg]
    rfl
  · intro D hD hx hy hz
    exact Glennie.NativeGenerationStabilizersR01.derivation_eq_zero_of_phi_ne_zero
      D hD x y z hphi hx hy hz

theorem q26_eq_iff_fullLedger_eq (T S : Triple)
    (hT : ∀ a, Frame (T a)) (hS : ∀ a, Frame (S a)) :
    q26 T = q26 S ↔ fullLedger T = fullLedger S := by
  change Glennie.Compact.NativeQFamilyLedger.q26 T =
      Glennie.Compact.NativeQFamilyLedger.q26 S ↔
      Glennie.Compact.Affine20.ledger54 T = Glennie.Compact.Affine20.ledger54 S
  exact Glennie.Compact.NativeQFamilyLedger.q26_eq_iff_ledger54_eq T S hT hS

/-- Q20 is the final twenty Q26 readings; the first six are fixed on actual frames. -/
def q20 (T : Triple) : Fin 20 → ℝ :=
  fun i => q26 T ⟨i.val + 6, Nat.add_lt_add_right i.2 6⟩

/-- On actual ordered frames, Q20 still determines the complete 54-trace ledger. -/
theorem q20_eq_iff_fullLedger_eq (T S : Triple)
    (hT : ∀ a, Frame (T a)) (hS : ∀ a, Frame (S a)) :
    q20 T = q20 S ↔ fullLedger T = fullLedger S := by
  change Glennie.Compact.NativeQ20AdapterR01.q20 T =
      Glennie.Compact.NativeQ20AdapterR01.q20 S ↔
      Glennie.Compact.Affine20.ledger54 T = Glennie.Compact.Affine20.ledger54 S
  exact Glennie.Compact.NativeQ20AdapterR01.q20_eq_iff_ledger54_eq T S hT hS

private theorem q26_eq_source (T : Triple) :
    q26 T = Glennie.Compact.NativeQFamilyLedger.q26 T := by rfl
private theorem f0_eq : f0 = (0 : Fin 3) := rfl
private theorem f1_eq : f1 = (1 : Fin 3) := rfl
private theorem f2_eq : f2 = (2 : Fin 3) := rfl
private theorem contrast_eq (x y z v : Albert) :
    contrast x y z v = Glennie.Compact.OperationalPhi.contrast x y z v := rfl
private theorem delta_eq (x y z a rho : Albert) :
    delta x y z a rho = Glennie.Compact.OperationalPhi.delta x y z a rho := rfl
private theorem halfAmplitude_eq (x : Albert) :
    halfAmplitude x = Glennie.Compact.OperationalPhi.halfAmplitude x := rfl
private theorem phiOf_eq (T : Triple) :
    phiOf T = Glennie.Compact.Sections.phiOf T := by
  simp only [phiOf, Glennie.Compact.Sections.phiOf, f0_eq, f1_eq, f2_eq]
private theorem score_eq_source (T : Triple) :
    score T = Glennie.Compact.LocalContrast.score T := by
  simp only [score, Glennie.Compact.LocalContrast.score,
    f0_eq, f1_eq, f2_eq, delta_eq, halfAmplitude_eq]

theorem division_free (x y z : Albert) :
    4 * delta x y z (halfAmplitude x) y - delta x y z x y -
      delta x y z 1 y = 2 * phi x y z := by
  rw [delta_eq, halfAmplitude_eq, delta_eq, delta_eq]
  exact Glennie.Compact.OperationalPhi.phi_division_free x y z

theorem score_eq_two_phi (T : Triple) : score T = 2 * phiOf T := by
  rw [score_eq_source, phiOf_eq]
  exact Glennie.Compact.LocalContrast.score_eq_two_phi T

theorem atoms_generate_of_score
    (T : Triple) (hT : ∀ a, Frame (T a)) (hs : score T ≠ 0)
    (K : Submodule ℝ Albert)
    (hJ : ∀ p ∈ K, ∀ q ∈ K, jordan p q ∈ K)
    (hAtoms : ∀ a i, T a i ∈ K) : K = ⊤ := by
  have hsource : Glennie.Compact.LocalContrast.score T ≠ 0 := by
    simpa only [score_eq_source] using hs
  exact Glennie.NativeOrderedFrameGenerationR01.ordered_frame_atoms_generate_of_score
    T hT hsource K hJ hAtoms

private theorem flatBase_eq_source :
    flatBase = Glennie.Compact.FrameTopology.flatBaseTriple := by rfl
private theorem fullLedger_eq_source (T : Triple) :
    fullLedger T = Glennie.Compact.Affine20.ledger54 T := by rfl
private theorem mapAtoms_eq_source (g : CompactAutomorphism) (T : Triple) :
    mapAtoms g T = Glennie.Compact.Affine20.mapAtoms g T := by rfl

theorem nearby_sign_rigidity :
    ∃ V : Set Ledger54, IsOpen V ∧ fullLedger flatBase ∈ V ∧
      ∀ T S : Triple, (∀ a : Fin 3, Frame (T a)) →
        (∀ a : Fin 3, Frame (S a)) → fullLedger T ∈ V →
        fullLedger T = fullLedger S →
        ((phiOf T < 0 ∧ phiOf S < 0) ∨ (0 < phiOf T ∧ 0 < phiOf S)) →
        ∃ k : CompactAutomorphism, mapAtoms k S = T := by
  obtain ⟨V, hopen, hbase, hrigid⟩ :=
    Glennie.Compact.NearbyOrbitsClosed.nearby_sign_rigidity_unconditional
  refine ⟨V, hopen, ?_, ?_⟩
  · rw [flatBase_eq_source, fullLedger_eq_source]
    exact hbase
  · intro T S hT hS hTV hTS hsign
    have hsourceTV : Glennie.Compact.Affine20.ledger54 T ∈ V := by
      rw [← fullLedger_eq_source]
      exact hTV
    have hsourceTS : Glennie.Compact.Affine20.ledger54 T =
        Glennie.Compact.Affine20.ledger54 S := by
      rw [← fullLedger_eq_source T, ← fullLedger_eq_source S]
      exact hTS
    have hsourceSign :
        ((Glennie.Compact.Sections.phiOf T < 0 ∧
            Glennie.Compact.Sections.phiOf S < 0) ∨
          (0 < Glennie.Compact.Sections.phiOf T ∧
            0 < Glennie.Compact.Sections.phiOf S)) := by
      simpa only [← phiOf_eq T, ← phiOf_eq S] using hsign
    obtain ⟨g, hg⟩ := hrigid T S hT hS hsourceTV hsourceTS hsourceSign
    refine ⟨g, ?_⟩
    rw [mapAtoms_eq_source]
    exact hg

/-- A specific native near-flat full-fiber margin in a supplied open ledger neighborhood. -/
theorem near_flat_scalar_margin :
    ∃ V : Set Ledger54, IsOpen V ∧ fullLedger flatBase ∈ V ∧
      ∀ T : Triple, (∀ a : Fin 3, Frame (T a)) → fullLedger T ∈ V →
        1 / 27 < |phiOf T| := by
  obtain ⟨V, ho, hb, hm⟩ := Glennie.Compact.NearbyOrbits.phi_bounded_away_near_flat
  refine ⟨V, ho, ?_, ?_⟩
  · rw [flatBase_eq_source, fullLedger_eq_source]
    exact hb
  · intro T hT hV
    rw [fullLedger_eq_source] at hV
    simpa only [phiOf_eq] using hm T hT hV

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
private theorem flatBase_eq_sections :
    flatBase = Glennie.Compact.Sections.flatBase := by rfl
private theorem encode20_eq_source (L : Ledger54) :
    encode20 L = Glennie.Compact.Affine20.encode20 L := by rfl
private theorem decode20_eq_source (b : Fin 20 → ℝ) :
    decode20 b = Glennie.Compact.Affine20.decode20 b := by rfl
private theorem fibre54_eq_source (b : Fin 20 → ℝ) :
    fibre54 b = Glennie.Compact.NearbyOrbits.fibre54 b := by
  simp only [fibre54, Glennie.Compact.NearbyOrbits.fibre54,
    fullLedger_eq_source, decode20_eq_source]
private theorem fibre20_eq_source (b : Fin 20 → ℝ) :
    fibre20 b = Glennie.Compact.NearbyOrbits.fibre20 b := by
  simp only [fibre20, Glennie.Compact.NearbyOrbits.fibre20,
    fullLedger_eq_source, encode20_eq_source]
private theorem autOrbit_eq_source (T : Triple) :
    autOrbit T = Glennie.Compact.FlatOrbit.autOrbit T := by
  simp only [autOrbit, Glennie.Compact.FlatOrbit.autOrbit, mapAtoms_eq_source]

theorem nearby_fibres_two_orbits :
    ∃ V : Set (Fin 20 → ℝ), IsOpen V ∧ encode20 (fullLedger flatBase) ∈ V ∧
      ∃ secPos secNeg : (Fin 20 → ℝ) → Triple,
        ContinuousOn (fun b => fun a i => Albert.coordinateEquiv (secPos b a i)) V ∧
        ContinuousOn (fun b => fun a i => Albert.coordinateEquiv (secNeg b a i)) V ∧
        (∀ b ∈ V, ∀ a : Fin 3, Frame (secPos b a)) ∧
        (∀ b ∈ V, ∀ a : Fin 3, Frame (secNeg b a)) ∧
        (∀ b ∈ V, encode20 (fullLedger (secPos b)) = b) ∧
        (∀ b ∈ V, encode20 (fullLedger (secNeg b)) = b) ∧
        (∀ b ∈ V, fullLedger (secPos b) = decode20 b) ∧
        (∀ b ∈ V, fullLedger (secNeg b) = decode20 b) ∧
        (∀ b ∈ V, 0 < phiOf (secPos b)) ∧
        (∀ b ∈ V, phiOf (secNeg b) < 0) ∧
        (∀ b ∈ V, fibre54 b = autOrbit (secNeg b) ∪ autOrbit (secPos b)) ∧
        (∀ b ∈ V, Disjoint (autOrbit (secNeg b)) (autOrbit (secPos b))) ∧
        (∀ b ∈ V, fibre20 b = fibre54 b) := by
  obtain ⟨V, ho, hb, p, n, hcp, hcn, hfp, hfn, hep, hen,
    hlp, hln, hpp, hnn, hcover, hdisj, heq⟩ :=
    Glennie.Compact.NearbyOrbitsClosed.nearby_fibres_two_orbits_unconditional
  have hcoordinate : Continuous
      (Albert.coordinateEquiv : Albert → Albert.Coordinates) :=
    Albert.coordinateLinearEquiv.toLinearMap.continuous_of_finiteDimensional
  have hcoord : Continuous
      (fun T : Triple => fun a i => Albert.coordinateEquiv (T a i)) := by
    apply continuous_pi
    intro a
    apply continuous_pi
    intro i
    exact hcoordinate.comp ((continuous_apply i).comp (continuous_apply a))
  refine ⟨V, ho, ?_, p, n, ?_, ?_, hfp, hfn,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [flatBase_eq_sections, fullLedger_eq_source, encode20_eq_source]
    exact hb
  · exact hcoord.comp_continuousOn hcp
  · exact hcoord.comp_continuousOn hcn
  · intro b h; rw [fullLedger_eq_source, encode20_eq_source]; exact hep b h
  · intro b h; rw [fullLedger_eq_source, encode20_eq_source]; exact hen b h
  · intro b h; rw [fullLedger_eq_source, decode20_eq_source]; exact hlp b h
  · intro b h; rw [fullLedger_eq_source, decode20_eq_source]; exact hln b h
  · intro b h; rw [phiOf_eq]; exact hpp b h
  · intro b h; rw [phiOf_eq]; exact hnn b h
  · intro b h
    rw [fibre54_eq_source, autOrbit_eq_source, autOrbit_eq_source]
    exact hcover b h
  · intro b h
    rw [autOrbit_eq_source, autOrbit_eq_source]
    exact hdisj b h
  · intro b h
    rw [fibre20_eq_source, fibre54_eq_source]
    exact heq b h

/-- On the admitted local chart, Q26 plus the nonzero score sign classifies
all actual ordered-frame triples under one simultaneous product-and-trace action. -/
theorem local_q26_score_orbit_test :
    ∃ V : Set (Fin 20 → ℝ), IsOpen V ∧ encode20 (fullLedger flatBase) ∈ V ∧
      ∀ T S : Triple, (∀ a, Frame (T a)) → (∀ a, Frame (S a)) →
        encode20 (fullLedger T) ∈ V →
        score T ≠ 0 ∧
        ((∃ k : CompactAutomorphism, mapAtoms k S = T) ↔
          q26 T = q26 S ∧
          ((score T < 0 ∧ score S < 0) ∨ (0 < score T ∧ 0 < score S))) := by
  obtain ⟨V, ho, hb, ht⟩ :=
    Glennie.Compact.LocalReconstruction.nearby_q26_score_complete
  refine ⟨V, ho, ?_, ?_⟩
  · rw [flatBase_eq_sections, fullLedger_eq_source, encode20_eq_source]
    exact hb
  · intro T S hT hS hTV
    have hsourceTV : Glennie.Compact.Affine20.encode20
        (Glennie.Compact.Affine20.ledger54 T) ∈ V := by
      rw [← encode20_eq_source, ← fullLedger_eq_source]
      exact hTV
    obtain ⟨hs, hiff⟩ := ht T S hT hS hsourceTV
    refine ⟨?_, ?_⟩
    · simpa only [score_eq_source] using hs
    · change (∃ k : CompactAutomorphism,
          Glennie.Compact.Affine20.mapAtoms k S = T) ↔
          Glennie.Compact.NativeQFamilyLedger.q26 T =
            Glennie.Compact.NativeQFamilyLedger.q26 S ∧
          ((Glennie.Compact.LocalContrast.score T < 0 ∧
            Glennie.Compact.LocalContrast.score S < 0) ∨
           (0 < Glennie.Compact.LocalContrast.score T ∧
            0 < Glennie.Compact.LocalContrast.score S)) at hiff
      simpa only [← mapAtoms_eq_source, ← score_eq_source, ← q26_eq_source] using hiff

/-- Every compact region of the established admitted chart has a positive
uniform Phi margin for its entire actual ordered-frame fiber. -/
theorem compact_local_phi_margin :
    ∃ V : Set (Fin 20 → ℝ), IsOpen V ∧ encode20 (fullLedger flatBase) ∈ V ∧
      ∀ K : Set V, IsCompact K →
        ∃ m > 0, ∀ T : Triple, (∀ a : Fin 3, Frame (T a)) →
          ∀ hb : encode20 (fullLedger T) ∈ V,
            (⟨encode20 (fullLedger T), hb⟩ : V) ∈ K →
              m ≤ |phiOf T| := by
  let d := Glennie.Compact.LocalOrbitQuotientR01.localData
  refine ⟨d.V, d.openV, ?_, ?_⟩
  · rw [flatBase_eq_sections, fullLedger_eq_source, encode20_eq_source]
    exact d.base
  · intro K hK
    obtain ⟨m, hm, hbound⟩ :=
      Glennie.Compact.NativeQ20AdapterR01.compact_response_margin d K hK
    refine ⟨m, hm, ?_⟩
    intro T hT hb hmem
    have hnative : Glennie.Compact.Affine20.encode20
        (Glennie.Compact.Affine20.ledger54 T) ∈ d.V := by
      rw [← encode20_eq_source, ← fullLedger_eq_source]
      exact hb
    let Td : Glennie.Compact.LocalOrbitQuotientR01.Admitted d :=
      ⟨T, hT, hnative⟩
    have hchart : Glennie.Compact.LocalOrbitQuotientR01.chart d Td =
        (⟨encode20 (fullLedger T), hb⟩ : d.V) := by
      apply Subtype.ext
      change Glennie.Compact.Affine20.encode20
        (Glennie.Compact.Affine20.ledger54 T) = encode20 (fullLedger T)
      rw [← encode20_eq_source, ← fullLedger_eq_source]
    have hk : Glennie.Compact.LocalOrbitQuotientR01.chart d Td ∈ K := by
      rw [hchart]
      exact hmem
    simpa only [phiOf_eq] using hbound Td hk

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
theorem signed_readout_margin (T : Triple) (noisy : Readouts) (ε : ℝ)
    (hε : 0 ≤ ε) (h : ErrorsAtMost noisy (exactReadouts T) ε)
    (hm : 12 * ε < |weightedScore noisy|) :
    (weightedScore noisy < 0 ∧ phiOf T < 0) ∨
    (0 < weightedScore noisy ∧ 0 < phiOf T) := by
  let toSource (r : Readouts) : Glennie.Compact.ReadoutRobustnessR01.Readouts :=
    ⟨r.hPlus, r.hMinus, r.xPlus, r.xMinus, r.onePlus, r.oneMinus⟩
  have hexact : toSource (exactReadouts T) =
      Glennie.Compact.ReadoutRobustnessR01.exactReadouts T := by
    rfl
  have herr : Glennie.Compact.ReadoutRobustnessR01.ErrorsAtMost
      (toSource noisy) (Glennie.Compact.ReadoutRobustnessR01.exactReadouts T) ε := by
    rw [← hexact]
    exact h
  have hscore (r : Readouts) : weightedScore r =
      Glennie.Compact.ReadoutRobustnessR01.weightedScore (toSource r) := rfl
  have hmargin : 12 * ε <
      |Glennie.Compact.ReadoutRobustnessR01.weightedScore (toSource noisy)| := by
    rwa [hscore] at hm
  have hs := Glennie.Compact.ReadoutRobustnessR01.sign_certificate
    T (toSource noisy) ε hε herr hmargin
  simpa only [← hscore, ← phiOf_eq] using hs


/-- The native raw trace norm, used to state perturbation radii independently. -/
def nA (x : Albert) : ℝ := Real.sqrt (inner x x)

/-- On a compact feasible chart region, nearby feasible coordinates recover
an actual frame triple up to one simultaneous automorphism, atom by atom.
Both the true and proposed coordinates must belong to the compact region. -/
theorem compact_feasible_element_recovery :
    ∃ V : Set (Fin 20 → ℝ), IsOpen V ∧ encode20 (fullLedger flatBase) ∈ V ∧
      ∃ secPos secNeg : (Fin 20 → ℝ) → Triple,
        ContinuousOn (fun b => fun a i => Albert.coordinateEquiv (secPos b a i)) V ∧
        ContinuousOn (fun b => fun a i => Albert.coordinateEquiv (secNeg b a i)) V ∧
        (∀ b ∈ V, ∀ a : Fin 3, Frame (secPos b a)) ∧
        (∀ b ∈ V, ∀ a : Fin 3, Frame (secNeg b a)) ∧
        (∀ b ∈ V, encode20 (fullLedger (secPos b)) = b) ∧
        (∀ b ∈ V, encode20 (fullLedger (secNeg b)) = b) ∧
        (∀ b ∈ V, 0 < phiOf (secPos b)) ∧
        (∀ b ∈ V, phiOf (secNeg b) < 0) ∧
        (∀ K : Set V, IsCompact K → ∀ ζ : ℝ, 0 < ζ →
          ∃ η > 0, ∀ T : Triple, (∀ a : Fin 3, Frame (T a)) →
            ∀ hb : encode20 (fullLedger T) ∈ V,
              (⟨encode20 (fullLedger T), hb⟩ : V) ∈ K →
              ∀ b : V, b ∈ K →
                dist (⟨encode20 (fullLedger T), hb⟩ : V) b < η →
                  ∃ g : CompactAutomorphism, ∀ a i : Fin 3,
                    nA (T a i - g.equiv
                      ((if 0 < phiOf T then secPos b.1 else secNeg b.1) a i)) < ζ) := by
  let d := Glennie.Compact.LocalOrbitQuotientR01.localData
  have hcoordinate : Continuous
      (Albert.coordinateEquiv : Albert → Albert.Coordinates) :=
    Albert.coordinateLinearEquiv.toLinearMap.continuous_of_finiteDimensional
  have hcoord : Continuous
      (fun T : Triple => fun a i => Albert.coordinateEquiv (T a i)) := by
    apply continuous_pi
    intro a
    apply continuous_pi
    intro i
    exact hcoordinate.comp ((continuous_apply i).comp (continuous_apply a))
  refine ⟨d.V, d.openV, ?_, d.pos, d.neg, ?_, ?_,
    d.framePos, d.frameNeg, ?_, ?_, ?_, ?_, ?_⟩
  · rw [flatBase_eq_sections, fullLedger_eq_source, encode20_eq_source]
    exact d.base
  · exact hcoord.comp_continuousOn d.contPos
  · exact hcoord.comp_continuousOn d.contNeg
  · intro b hb
    rw [fullLedger_eq_source, encode20_eq_source]
    exact d.chartPos b hb
  · intro b hb
    rw [fullLedger_eq_source, encode20_eq_source]
    exact d.chartNeg b hb
  · intro b hb
    rw [phiOf_eq]
    exact d.phiPos b hb
  · intro b hb
    rw [phiOf_eq]
    exact d.phiNeg b hb
  · intro K hK ζ hζ
    obtain ⟨η, hη, hrec⟩ :=
      Glennie.Compact.NativeQ20AdapterR01.compact_feasible_recovery d K hK ζ hζ
    refine ⟨η, hη, ?_⟩
    intro T hT hb hTK b hbK hdist
    have hnative : Glennie.Compact.Affine20.encode20
        (Glennie.Compact.Affine20.ledger54 T) ∈ d.V := by
      rw [← encode20_eq_source, ← fullLedger_eq_source]
      exact hb
    let Td : Glennie.Compact.LocalOrbitQuotientR01.Admitted d :=
      ⟨T, hT, hnative⟩
    have hchart : Glennie.Compact.LocalOrbitQuotientR01.chart d Td =
        (⟨encode20 (fullLedger T), hb⟩ : d.V) := by
      apply Subtype.ext
      change Glennie.Compact.Affine20.encode20
        (Glennie.Compact.Affine20.ledger54 T) = encode20 (fullLedger T)
      rw [← encode20_eq_source, ← fullLedger_eq_source]
    have hTK' : Glennie.Compact.LocalOrbitQuotientR01.chart d Td ∈ K := by
      rw [hchart]
      exact hTK
    have hdist' : dist (Glennie.Compact.LocalOrbitQuotientR01.chart d Td) b < η := by
      rwa [hchart]
    obtain ⟨g, hg⟩ := hrec Td hTK' b hbK hdist'
    refine ⟨g, ?_⟩
    have hsection :
        Glennie.Compact.NativeQ20AdapterR01.branchSection d b
          (Glennie.Compact.LocalOrbitQuotientR01.sheet d Td) =
          (if 0 < phiOf T then d.pos b.1 else d.neg b.1) := by
      by_cases hp : 0 < phiOf T
      · have hps : 0 < Glennie.Compact.Sections.phiOf T := by
          rwa [← phiOf_eq]
        simp [Glennie.Compact.NativeQ20AdapterR01.branchSection,
          Glennie.Compact.LocalOrbitQuotientR01.sheet, hp, hps, Td]
      · have hps : ¬ 0 < Glennie.Compact.Sections.phiOf T := by
          rwa [← phiOf_eq]
        simp [Glennie.Compact.NativeQ20AdapterR01.branchSection,
          Glennie.Compact.LocalOrbitQuotientR01.sheet, hp, hps, Td]
    rw [hsection] at hg
    intro a i
    have hbound :
        ‖(T - Glennie.Compact.Affine20.mapAtoms g
          (if 0 < phiOf T then d.pos b.1 else d.neg b.1)) a i‖ ≤
        ‖T - Glennie.Compact.Affine20.mapAtoms g
          (if 0 < phiOf T then d.pos b.1 else d.neg b.1)‖ :=
      (norm_le_pi_norm _ i).trans (norm_le_pi_norm _ a)
    have hlt := lt_of_le_of_lt hbound hg
    have hnorm (x : Albert) : nA x = ‖x‖ := by
      unfold nA
      rw [← Glennie.native_norm_sq]
      exact Real.sqrt_sq (norm_nonneg x)
    simpa only [hnorm, Pi.sub_apply, Glennie.Compact.Affine20.mapAtoms]
      using hlt

/-- A strict six-reading margin selects the correct continuous branch for
compact feasible-coordinate recovery. The proposed chart remains feasible. -/
theorem compact_noisy_feasible_element_recovery :
    ∃ V : Set (Fin 20 → ℝ), IsOpen V ∧ encode20 (fullLedger flatBase) ∈ V ∧
      ∃ secPos secNeg : (Fin 20 → ℝ) → Triple,
        ContinuousOn (fun b => fun a i => Albert.coordinateEquiv (secPos b a i)) V ∧
        ContinuousOn (fun b => fun a i => Albert.coordinateEquiv (secNeg b a i)) V ∧
        (∀ b ∈ V, ∀ a : Fin 3, Frame (secPos b a)) ∧
        (∀ b ∈ V, ∀ a : Fin 3, Frame (secNeg b a)) ∧
        (∀ b ∈ V, encode20 (fullLedger (secPos b)) = b) ∧
        (∀ b ∈ V, encode20 (fullLedger (secNeg b)) = b) ∧
        (∀ b ∈ V, 0 < phiOf (secPos b)) ∧
        (∀ b ∈ V, phiOf (secNeg b) < 0) ∧
        (∀ K : Set V, IsCompact K → ∀ ζ : ℝ, 0 < ζ →
          ∃ η > 0, ∀ T : Triple, (∀ a : Fin 3, Frame (T a)) →
            ∀ hb : encode20 (fullLedger T) ∈ V,
              (⟨encode20 (fullLedger T), hb⟩ : V) ∈ K →
              ∀ b : V, b ∈ K →
                dist (⟨encode20 (fullLedger T), hb⟩ : V) b < η →
                  ∀ noisy : Readouts, ∀ ε : ℝ, 0 ≤ ε →
                    ErrorsAtMost noisy (exactReadouts T) ε →
                    12 * ε < |weightedScore noisy| →
                    ∃ g : CompactAutomorphism, ∀ a i : Fin 3,
                      nA (T a i - g.equiv
                        ((if 0 < weightedScore noisy then secPos b.1
                          else secNeg b.1) a i)) < ζ) := by
  obtain ⟨V, ho, hb, p, n, hcp, hcn, hfp, hfn, hep, hen, hpp, hpn, hrec⟩ :=
    compact_feasible_element_recovery
  refine ⟨V, ho, hb, p, n, hcp, hcn, hfp, hfn, hep, hen, hpp, hpn, ?_⟩
  intro K hK ζ hζ
  obtain ⟨η, hη, hrecover⟩ := hrec K hK ζ hζ
  refine ⟨η, hη, ?_⟩
  intro T hT hbT hTK b hbK hdist noisy ε hε herr hm
  obtain ⟨g, hg⟩ := hrecover T hT hbT hTK b hbK hdist
  refine ⟨g, ?_⟩
  rcases signed_readout_margin T noisy ε hε herr hm with hn | hp
  · have hns : ¬ 0 < weightedScore noisy := not_lt_of_ge hn.1.le
    have hnp : ¬ 0 < phiOf T := not_lt_of_ge hn.2.le
    simpa only [if_neg hns, if_neg hnp] using hg
  · simpa only [if_pos hp.1, if_pos hp.2] using hg

def noisyPhi (r : Readouts) : ℝ := weightedScore r / (Nat.cast 2 : ℝ)

/-- Raw six-readout errors and three bounded input displacements certify the
sign, full unital generation, and pointwise stabilizer at the displaced inputs. -/
theorem six_readout_displaced_generation
    (T : Triple) (noisy : Readouts) (x' y' z' : Albert)
    (ε ξ R δ : ℝ) (hξ : 0 ≤ ξ) (hR : 0 ≤ R)
    (hreadout : ErrorsAtMost noisy (exactReadouts T) ε)
    (hallowance : 6 * ε ≤ ξ)
    (hx : nA (encoder (T f0)) ≤ R) (hy : nA (encoder (T f1)) ≤ R)
    (hz : nA (encoder (T f2)) ≤ R)
    (hx' : nA x' ≤ R) (hy' : nA y' ≤ R) (hz' : nA z' ≤ R)
    (hdx : nA (encoder (T f0) - x') ≤ δ)
    (hdy : nA (encoder (T f1) - y') ≤ δ)
    (hdz : nA (encoder (T f2) - z') ≤ δ)
    (hmargin : 18 * R^8 * δ < |noisyPhi noisy| - ξ) :
    ((noisyPhi noisy < 0 ∧ phi x' y' z' < 0) ∨
      (0 < noisyPhi noisy ∧ 0 < phi x' y' z')) ∧
    (∀ K : Submodule ℝ Albert, (1 : Albert) ∈ K →
      (∀ p ∈ K, ∀ q ∈ K, jordan p q ∈ K) →
      x' ∈ K → y' ∈ K → z' ∈ K → K = ⊤) ∧
    (∀ g : CompactAutomorphism,
      g.equiv x' = x' → g.equiv y' = y' → g.equiv z' = z' →
      g.equiv = LinearEquiv.refl ℝ Albert) := by
  let r : Glennie.Compact.ReadoutRobustnessR01.Readouts :=
    ⟨noisy.hPlus, noisy.hMinus, noisy.xPlus, noisy.xMinus,
      noisy.onePlus, noisy.oneMinus⟩
  have herr : Glennie.Compact.ReadoutRobustnessR01.ErrorsAtMost r
      (Glennie.Compact.ReadoutRobustnessR01.exactReadouts T) ε := by
    change ErrorsAtMost noisy (exactReadouts T) ε
    exact hreadout
  have hnoisy : Glennie.Compact.ReadoutRobustnessR01.noisyPhi r =
      noisyPhi noisy := by rfl
  have hnorm (x : Albert) : nA x = ‖x‖ := by
    unfold nA
    rw [← Glennie.native_norm_sq]
    exact Real.sqrt_sq (norm_nonneg x)
  have hsource := Glennie.Compact.MeasuredMarginR01.six_readout_same_radius_sign_and_generation
    T r x' y' z' ε ξ R δ hξ hR herr hallowance
    (by simpa only [hnorm, f0_eq] using hx)
    (by simpa only [hnorm, f1_eq] using hy)
    (by simpa only [hnorm, f2_eq] using hz)
    (by simpa only [hnorm] using hx')
    (by simpa only [hnorm] using hy')
    (by simpa only [hnorm] using hz')
    (by simpa only [hnorm, f0_eq] using hdx)
    (by simpa only [hnorm, f1_eq] using hdy)
    (by simpa only [hnorm, f2_eq] using hdz)
    (by rw [hnoisy]; exact hmargin)
  rcases hsource with ⟨hsign, hgen, hstab⟩
  refine ⟨?_, hgen, ?_⟩
  · rw [hnoisy] at hsign
    exact hsign
  · intro g hgx hgy hgz
    rw [hstab g hgx hgy hgz]
    rfl

/-- The coordinatewise special Jordan product in arbitrary Euclidean dimension. -/
def diagonalNProduct {n : ℕ} (a b : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) := WithLp.toLp (Nat.cast 2 : ENNReal) (fun i => a i * b i)

/-- A uniform all-input defect bounds the degree-nine scalar on any
radius-bounded triple for every finite coordinatewise Euclidean target. -/
theorem diagonalN_defect_response_radius {n : ℕ}
    (f : Albert →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (hf : ∀ x : Albert, ‖f x‖ = nA x)
    (μ R : ℝ) (hμ : 0 ≤ μ) (hR : 0 ≤ R)
    (hdef : ∀ a b : Albert,
      ‖f (jordan a b) - diagonalNProduct (f a) (f b)‖ ≤
        μ * nA a * nA b)
    (x y z : Albert) (hx : nA x ≤ R) (hy : nA y ≤ R)
    (hz : nA z ≤ R) :
    |phi x y z| ≤ 38 * μ * R^9 := by
  have hnorm (w : Albert) : nA w = ‖w‖ := by
    unfold nA
    rw [← Glennie.native_norm_sq]
    exact Real.sqrt_sq (norm_nonneg w)
  let fIso : Albert →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) :=
    ⟨f, fun w => (hf w).trans (hnorm w)⟩
  have hdef' : ∀ a b : Albert,
      ‖fIso (jordan a b) -
        Glennie.Compact.VariableDiagonalNullTargetR01.diagonalNProduct
          (fIso a) (fIso b)‖ ≤ μ * ‖a‖ * ‖b‖ := by
    intro a b
    change ‖f (jordan a b) - diagonalNProduct (f a) (f b)‖ ≤
      μ * ‖a‖ * ‖b‖
    simpa only [hnorm] using hdef a b
  exact Glennie.Compact.VariableDiagonalDefectReadoutR01.native_diagonalN_defect_response
    fIso μ R hμ hR hdef' x y z
    (by simpa only [hnorm] using hx)
    (by simpa only [hnorm] using hy)
    (by simpa only [hnorm] using hz)

/-- An actual-frame noisy score forces a uniform multiplication defect for
any norm-preserving linear map into a coordinatewise Euclidean target. -/
theorem frame_noisy_diagonalN_defect_lower {n : ℕ}
    (f : Albert →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (hf : ∀ x : Albert, ‖f x‖ = nA x)
    (T : Triple) (hT : ∀ a : Fin 3, Frame (T a))
    (noisy : Readouts) (ε μ : ℝ) (hμ : 0 ≤ μ)
    (hreadout : ErrorsAtMost noisy (exactReadouts T) ε)
    (hdef : ∀ a b : Albert,
      ‖f (jordan a b) - diagonalNProduct (f a) (f b)‖ ≤
        μ * nA a * nA b) :
    (|weightedScore noisy| - 12 * ε) / (1216 * Real.sqrt 2) ≤ μ := by
  let r : Glennie.Compact.ReadoutRobustnessR01.Readouts :=
    ⟨noisy.hPlus, noisy.hMinus, noisy.xPlus, noisy.xMinus,
      noisy.onePlus, noisy.oneMinus⟩
  have herr : Glennie.Compact.ReadoutRobustnessR01.ErrorsAtMost r
      (Glennie.Compact.ReadoutRobustnessR01.exactReadouts T) ε := by
    change ErrorsAtMost noisy (exactReadouts T) ε
    exact hreadout
  have hnorm (x : Albert) : nA x = ‖x‖ := by
    unfold nA
    rw [← Glennie.native_norm_sq]
    exact Real.sqrt_sq (norm_nonneg x)
  let fIso : Albert →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) :=
    ⟨f, fun x => (hf x).trans (hnorm x)⟩
  have hdef' : ∀ a b : Albert,
      ‖fIso (jordan a b) -
        Glennie.Compact.VariableDiagonalNullTargetR01.diagonalNProduct
          (fIso a) (fIso b)‖ ≤ μ * ‖a‖ * ‖b‖ := by
    intro a b
    change ‖f (jordan a b) - diagonalNProduct (f a) (f b)‖ ≤
      μ * ‖a‖ * ‖b‖
    simpa only [hnorm] using hdef a b
  have hs :=
    Glennie.Compact.VariableDiagonalDefectReadoutR01.frame_noisy_diagonalN_defect_lower
      fIso T hT r ε μ hμ herr hdef'
  have hscore : Glennie.Compact.ReadoutRobustnessR01.weightedScore r =
      weightedScore noisy := by rfl
  rw [hscore] at hs
  exact hs

/-- A noisy actual-frame score also forces a defect for an associative
cyclic-trace represented target with its exact product and metric adapters. -/
theorem frame_noisy_represented_defect_lower
    {E N : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedRing N] [NormedAlgebra ℝ N]
    (jE : E →ₗ[ℝ] E →ₗ[ℝ] E)
    (f : Albert →ₗ[ℝ] E) (hf : ∀ x : Albert, ‖f x‖ = nA x)
    (ρ : E →ₗᵢ[ℝ] N) (τ : N →ₗ[ℝ] ℝ)
    (hj : ∀ a b : E, ρ (jE a b) =
      (1 / 2 : ℝ) • (ρ a * ρ b + ρ b * ρ a))
    (hB : ∀ a b : E, Inner.inner ℝ a b = τ (ρ a * ρ b))
    (hcyclic : ∀ a b : N, τ (a * b) = τ (b * a))
    (T : Triple) (hT : ∀ a : Fin 3, Frame (T a))
    (noisy : Readouts) (ε μ : ℝ) (hμ : 0 ≤ μ)
    (hreadout : ErrorsAtMost noisy (exactReadouts T) ε)
    (hdef : ∀ a b : Albert,
      ‖f (jordan a b) - jE (f a) (f b)‖ ≤ μ * nA a * nA b) :
    (|weightedScore noisy| - 12 * ε) / (1216 * Real.sqrt 2) ≤ μ := by
  let r : Glennie.Compact.ReadoutRobustnessR01.Readouts :=
    ⟨noisy.hPlus, noisy.hMinus, noisy.xPlus, noisy.xMinus,
      noisy.onePlus, noisy.oneMinus⟩
  have herr : Glennie.Compact.ReadoutRobustnessR01.ErrorsAtMost r
      (Glennie.Compact.ReadoutRobustnessR01.exactReadouts T) ε := by
    change ErrorsAtMost noisy (exactReadouts T) ε
    exact hreadout
  have hnorm (x : Albert) : nA x = ‖x‖ := by
    unfold nA
    rw [← Glennie.native_norm_sq]
    exact Real.sqrt_sq (norm_nonneg x)
  let fIso : Albert →ₗᵢ[ℝ] E :=
    ⟨f, fun x => (hf x).trans (hnorm x)⟩
  have hj' : ∀ a b : E, ρ (jE a b) =
      Glennie.Compact.CyclicTraceNullR01.symmProd (ρ a) (ρ b) := by
    intro a b
    exact hj a b
  have hdef' : ∀ a b : Albert,
      ‖fIso (jordan a b) - jE (fIso a) (fIso b)‖ ≤
        μ * ‖a‖ * ‖b‖ := by
    intro a b
    change ‖f (jordan a b) - jE (f a) (f b)‖ ≤ μ * ‖a‖ * ‖b‖
    simpa only [hnorm] using hdef a b
  have hs :=
    Glennie.Compact.RepresentedDefectReadoutR01.frame_noisy_represented_defect_lower
      jE fIso ρ τ hj' hB hcyclic T hT r ε μ hμ herr hdef'
  have hscore : Glennie.Compact.ReadoutRobustnessR01.weightedScore r =
      weightedScore noisy := by rfl
  rw [hscore] at hs
  exact hs

/-- The same 27 fixed bracketed words evaluated in any marked product. -/
def witnessX : Albert := ⟨-1,0,1,0,0,0⟩
def witnessY : Albert := ⟨0,0,0,octScalar 1,octI,octScalar 1⟩
def nativeMarks : Fin 3 → Albert := ![witnessX,witnessY,witnessZ]
def wordValues {E : Type*} (e : E) (a : Fin 3 → E)
    (j : E → E → E) : Fin 27 → E :=
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
def candidateWordValues {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (e : E) (a : Fin 3 → E) (j : E →ₗ[ℝ] E →ₗ[ℝ] E) : Fin 27 → E :=
  wordValues e a (fun x y => j x y)
/-- The generated unital product-closed submodule is independent of the list. -/
def generated {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (e : E) (a : Fin 3 → E) (j : E →ₗ[ℝ] E →ₗ[ℝ] E) : Submodule ℝ E :=
  sInf {K : Submodule ℝ E | e ∈ K ∧ (∀ i, a i ∈ K) ∧
    (∀ x ∈ K, ∀ y ∈ K, j x y ∈ K)}
/-- Three fully determined families of scalar data from the fixed native words. -/
structure Match27 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (e : E) (a : Fin 3 → E) (j : E →ₗ[ℝ] E →ₗ[ℝ] E) : Prop where
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

private theorem wordValues_eq_source {E : Type*} (e : E) (a : Fin 3 → E)
    (j : E → E → E) (i : Fin 27) :
    wordValues e a j i =
      Glennie.Compact.NativeWordTableR01.eval e a j
        (Glennie.Compact.NativeWordTableR01.words i) := by
  fin_cases i <;> rfl

private theorem nativeWordValue_eq_source (i : Fin 27) :
    nativeWordValues i = Glennie.Compact.NativeWordTableR01.nativeWords i := by
  have hmarks : nativeMarks = Glennie.Compact.NativeWordTableR01.marks := by
    funext k
    fin_cases k <;> rfl
  change wordValues 1 nativeMarks jordan i =
    Glennie.Compact.NativeWordTableR01.eval 1
      Glennie.Compact.NativeWordTableR01.marks jordan
      (Glennie.Compact.NativeWordTableR01.words i)
  rw [hmarks]
  exact wordValues_eq_source 1 _ jordan i
private theorem candidateWordValues_eq_source
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (e : E) (a : Fin 3 → E) (j : E →ₗ[ℝ] E →ₗ[ℝ] E) :
    candidateWordValues e a j =
      Glennie.Compact.MarkedModelConsumerCandidate.candidateWords e a j := by
  funext i
  fin_cases i <;> rfl
private theorem generated_eq_source
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (e : E) (a : Fin 3 → E) (j : E →ₗ[ℝ] E →ₗ[ℝ] E) :
    generated e a j = Glennie.Compact.MarkedModelConsumerCandidate.generated e a j := by rfl

/-- The native word certificate supplies a unique unit-, mark-, product- and
metric-preserving embedding into the ambient carrier. -/
theorem finite_word_marked_recognition
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (e : E) (a : Fin 3 → E) (j : E →ₗ[ℝ] E →ₗ[ℝ] E)
    (h : Match27 e a j) :
    ∃! L : Albert →ₗ[ℝ] E,
      L 1 = e ∧
      (∀ i : Fin 3, L (nativeMarks i) = a i) ∧
      (∀ x y : Albert, L (jordan x y) = j (L x) (L y)) ∧
      (∀ x y : Albert, Inner.inner ℝ (L x) (L y) = inner x y) ∧
      Function.Injective L ∧ LinearMap.range L = generated e a j := by
  have hsrc : Glennie.Compact.MarkedModelConsumerCandidate.Match27 e a j := by
    refine ⟨?_, ?_, ?_⟩
    · intro i k
      simpa only [← candidateWordValues_eq_source,
        ← nativeWordValue_eq_source] using h.gram i k
    · intro i k l
      simpa only [← candidateWordValues_eq_source,
        ← nativeWordValue_eq_source] using h.mixed i k l
    · intro i k
      simpa only [← candidateWordValues_eq_source,
        ← nativeWordValue_eq_source] using h.product_sq i k
  obtain ⟨_, I, _⟩ :=
    Glennie.Compact.MarkedModelConsumerCandidate.unique_generated_marked_recognition
      e a j hsrc
  let L : Albert →ₗ[ℝ] E :=
    (Submodule.subtype _).comp I.A.symm.toLinearMap
  have hunit : L 1 = e := by
    have hI : I.A.symm (1 : Albert) =
        Glennie.Compact.MarkedModelConsumerCandidate.spanUnit e a j := by
      apply I.A.injective
      rw [I.A.apply_symm_apply]
      exact I.map_unit.symm
    change ((I.A.symm (1 : Albert) :
      Glennie.Compact.MarkedModelConsumerCandidate.wordSpan e a j) : E) = e
    rw [hI]
    rfl
  have hmarks : ∀ i : Fin 3, L (nativeMarks i) = a i := by
    intro i
    have hI : I.A.symm (nativeMarks i) =
        Glennie.Compact.MarkedModelConsumerCandidate.spanMarks e a j i := by
      apply I.A.injective
      rw [I.A.apply_symm_apply]
      exact (I.map_marks i).symm
    change ((I.A.symm (nativeMarks i) :
      Glennie.Compact.MarkedModelConsumerCandidate.wordSpan e a j) : E) = a i
    rw [hI]
    rfl
  have hprod : ∀ x y : Albert, L (jordan x y) = j (L x) (L y) := by
    intro x y
    have hz : I.A.symm (jordan x y) =
        Glennie.Compact.MarkedModelConsumerCandidate.spanProduct e a j hsrc
          (I.A.symm x) (I.A.symm y) := by
      apply I.A.injective
      rw [I.A.apply_symm_apply, I.map_product,
        I.A.apply_symm_apply, I.A.apply_symm_apply]
    change ((I.A.symm (jordan x y) :
      Glennie.Compact.MarkedModelConsumerCandidate.wordSpan e a j) : E) =
      j (I.A.symm x).1 (I.A.symm y).1
    rw [hz]
    rfl
  have hmetric : ∀ x y : Albert, Inner.inner ℝ (L x) (L y) = inner x y := by
    intro x y
    change Inner.inner ℝ (I.A.symm x : E) (I.A.symm y : E) = inner x y
    have hm := I.map_metric (I.A.symm x) (I.A.symm y)
    simpa only [Submodule.coe_inner, I.A.apply_symm_apply] using hm
  have hinj : Function.Injective L := by
    intro x y hxy
    have hsub : I.A.symm x = I.A.symm y := Subtype.ext hxy
    exact I.A.symm.injective hsub
  have hrange : LinearMap.range L = generated e a j := by
    rw [generated_eq_source]
    ext x
    constructor
    · rintro ⟨v, rfl⟩
      rw [← Glennie.Compact.MarkedModelConsumerCandidate.wordSpan_eq_generated e a j hsrc]
      exact (I.A.symm v).2
    · intro hx
      rw [← Glennie.Compact.MarkedModelConsumerCandidate.wordSpan_eq_generated e a j hsrc] at hx
      refine ⟨I.A ⟨x,hx⟩, ?_⟩
      change (I.A.symm (I.A ⟨x,hx⟩) : E) = x
      rw [I.A.symm_apply_apply]
  refine ⟨L, ⟨hunit, hmarks, hprod, hmetric, hinj, hrange⟩, ?_⟩
  intro J hJ
  rcases hJ with ⟨hJu, hJm, hJp, _, _, _⟩
  have heval (M : Albert →ₗ[ℝ] E)
      (hu : M 1 = e) (hm : ∀ i : Fin 3, M (nativeMarks i) = a i)
      (hp : ∀ x y, M (jordan x y) = j (M x) (M y))
      (w : Glennie.Compact.NativeWordTableR01.Word) :
      M (Glennie.Compact.NativeWordTableR01.nativeEval w) =
        Glennie.Compact.NativeWordTableR01.eval e a (fun x y => j x y) w := by
    induction w with
    | unit => exact hu
    | mark i => exact hm i
    | mul u v ihu ihv =>
        change M (jordan (Glennie.Compact.NativeWordTableR01.nativeEval u)
          (Glennie.Compact.NativeWordTableR01.nativeEval v)) = _
        rw [hp, ihu, ihv]
        rfl
  have hwords (i : Fin 27) :
      J (Glennie.Compact.NativeWordTableR01.nativeWords i) =
        L (Glennie.Compact.NativeWordTableR01.nativeWords i) := by
    exact (heval J hJu hJm hJp _).trans
      (heval L hunit hmarks hprod _).symm
  apply LinearMap.ext
  intro x
  have hx : x ∈ Submodule.span ℝ
      (Set.range Glennie.Compact.NativeWordTableR01.nativeWords) := by
    rw [Glennie.Compact.NativeWordTableR01.nativeWords_span]
    trivial
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact hwords i
  | zero => simp
  | add x y _ _ hx hy => simp [map_add, hx, hy]
  | smul r x _ hx => simp [map_smul, hx]

end
end Glennie.SubmissionR03

@[expose] public section
namespace Glennie.SubmissionR04Quotient
noncomputable section
open Glennie Glennie.Compact.Affine20 Glennie.SubmissionR03
set_option autoImplicit false
set_option maxHeartbeats 1000000

abbrev ChartPoint := Fin 20 → ℝ
abbrev TripleCoordinates := Fin 3 → Fin 3 → Albert.Coordinates

def tripleCoordinates (T : Triple) : TripleCoordinates :=
  fun a i => Albert.coordinateEquiv (T a i)

/-- The honest topology from all nine native coordinate vectors. -/
def tripleCoordinateTopology : TopologicalSpace Triple :=
  TopologicalSpace.induced tripleCoordinates inferInstance

private def tripleCoordinateHomeomorph : Triple ≃ₜ TripleCoordinates :=
  Homeomorph.piCongrRight (fun _ : Fin 3 =>
    Homeomorph.piCongrRight (fun _ : Fin 3 =>
      Albert.coordinateLinearEquiv.toContinuousLinearEquiv.toHomeomorph))

private theorem tripleCoordinateTopology_eq_native :
    tripleCoordinateTopology = (inferInstance : TopologicalSpace Triple) := by
  change TopologicalSpace.induced
    (tripleCoordinateHomeomorph : Triple → TripleCoordinates) inferInstance = _
  exact tripleCoordinateHomeomorph.isInducing.eq_induced.symm

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

private theorem flatBase_eq_source :
    flatBase = Glennie.Compact.Sections.flatBase := rfl
private theorem fullLedger_eq_source (T : Triple) :
    fullLedger T = Glennie.Compact.Affine20.ledger54 T := rfl
private theorem encode20_eq_source (L : Ledger54) :
    Glennie.SubmissionR03.encode20 L = Glennie.Compact.Affine20.encode20 L := rfl
private theorem phiOf_eq_source (T : Triple) :
    phiOf T = Glennie.Compact.Sections.phiOf T := by
  simp only [phiOf, Glennie.Compact.Sections.phiOf]
  rfl

private theorem admitted_eq_source
    (d : Glennie.Compact.LocalOrbitQuotientR01.LocalData) :
    Admitted d.V = Glennie.Compact.LocalOrbitQuotientR01.Admitted d := by
  rfl

private theorem orbitSetoid_eq_source
    (d : Glennie.Compact.LocalOrbitQuotientR01.LocalData) :
    orbitSetoid d.V = Glennie.Compact.LocalOrbitQuotientR01.orbitSetoid d := by
  rfl

private def quotientCoordinateTopology
    (d : Glennie.Compact.LocalOrbitQuotientR01.LocalData) :
    TopologicalSpace (OrbitQuotient d.V) :=
  @instTopologicalSpaceQuotient (Admitted d.V) (orbitSetoid d.V)
    (@instTopologicalSpaceSubtype Triple _ tripleCoordinateTopology)

private def quotientNativeTopology
    (d : Glennie.Compact.LocalOrbitQuotientR01.LocalData) :
    TopologicalSpace (Glennie.Compact.LocalOrbitQuotientR01.OrbitQuotient d) :=
  @instTopologicalSpaceQuotient
    (Glennie.Compact.LocalOrbitQuotientR01.Admitted d)
    (Glennie.Compact.LocalOrbitQuotientR01.orbitSetoid d)
    (@instTopologicalSpaceSubtype Triple _ Pi.topologicalSpace)

private theorem quotientTopology_eq_source
    (d : Glennie.Compact.LocalOrbitQuotientR01.LocalData) :
    quotientCoordinateTopology d = quotientNativeTopology d := by
  unfold quotientCoordinateTopology quotientNativeTopology
  rw [tripleCoordinateTopology_eq_native]
  rfl

private theorem orbitQuotient_eq_source
    (d : Glennie.Compact.LocalOrbitQuotientR01.LocalData) :
    OrbitQuotient d.V =
      Glennie.Compact.LocalOrbitQuotientR01.OrbitQuotient d := by
  rfl

private theorem continuous_forward_induced
    (d : Glennie.Compact.LocalOrbitQuotientR01.LocalData) :
    Continuous (Glennie.Compact.LocalOrbitQuotientR01.forward d :
      OrbitQuotient d.V → d.V × Bool) := by
  let Q := Glennie.Compact.LocalOrbitQuotientR01.OrbitQuotient d
  let τn : TopologicalSpace Q := quotientNativeTopology d
  let τc : TopologicalSpace Q :=
    quotientCoordinateTopology d
  let P : TopologicalSpace Q → Prop := fun τ =>
    @Continuous Q (d.V × Bool) τ inferInstance
      (Glennie.Compact.LocalOrbitQuotientR01.forward d)
  have hs : P τn := by
    with_unfolding_all exact Glennie.Compact.LocalOrbitQuotientR01.continuous_forward d
  have heq : τn = τc := (quotientTopology_eq_source d).symm
  with_unfolding_all change P τc
  exact heq ▸ hs

private theorem continuous_inverse_induced
    (d : Glennie.Compact.LocalOrbitQuotientR01.LocalData) :
    Continuous (Glennie.Compact.LocalOrbitQuotientR01.inverse d :
      d.V × Bool → OrbitQuotient d.V) := by
  let Q := Glennie.Compact.LocalOrbitQuotientR01.OrbitQuotient d
  let τn : TopologicalSpace Q := quotientNativeTopology d
  let τc : TopologicalSpace Q :=
    quotientCoordinateTopology d
  let P : TopologicalSpace Q → Prop := fun τ =>
    @Continuous (d.V × Bool) Q inferInstance τ
      (Glennie.Compact.LocalOrbitQuotientR01.inverse d)
  have hs : P τn := by
    with_unfolding_all exact Glennie.Compact.LocalOrbitQuotientR01.continuous_inverse d
  have heq : τn = τc := (quotientTopology_eq_source d).symm
  with_unfolding_all change P τc
  exact heq ▸ hs

/-- The actual automorphism quotient of all admitted ordered frames is
homeomorphic to the centered feasible chart and its two algebraic sign sheets. -/
theorem admitted_orbit_quotient_homeomorph :
    ∃ V : Set ChartPoint, IsOpen V ∧
      Glennie.SubmissionR03.encode20 (fullLedger flatBase) ∈ V ∧
      ∃ H : OrbitQuotient V ≃ₜ V × Bool,
        (∀ T : Admitted V, H (Quotient.mk' T) = invariant V T) ∧
        (∀ T S : Admitted V,
          (orbitSetoid V).r T S ↔ invariant V T = invariant V S) := by
  let d := Glennie.Compact.LocalOrbitQuotientR01.localData
  refine ⟨d.V, d.openV, ?_, ?_⟩
  · simpa only [flatBase_eq_source, fullLedger_eq_source,
      encode20_eq_source] using d.base
  · let H : OrbitQuotient d.V ≃ₜ d.V × Bool := {
      toFun := Glennie.Compact.LocalOrbitQuotientR01.forward d
      invFun := Glennie.Compact.LocalOrbitQuotientR01.inverse d
      left_inv := Glennie.Compact.LocalOrbitQuotientR01.inverse_forward d
      right_inv := Glennie.Compact.LocalOrbitQuotientR01.forward_inverse d
      continuous_toFun := continuous_forward_induced d
      continuous_invFun := continuous_inverse_induced d }
    refine ⟨H, ?_, ?_⟩
    · intro T
      rfl
    · intro T S
      change (Glennie.Compact.LocalOrbitQuotientR01.orbitSetoid d).r T S ↔
        Glennie.Compact.LocalOrbitQuotientR01.invariant d T =
          Glennie.Compact.LocalOrbitQuotientR01.invariant d S
      simpa only [Glennie.Compact.LocalOrbitQuotientR01.invariant,
        Prod.mk.injEq] using
        (Glennie.Compact.LocalOrbitQuotientR01.rel_iff_chart_sheet_eq d T S)

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
def ambientMetricD1 (P : BasedCubic E) (x : E) :
    E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ := fderiv ℝ (metric P) x
/-- Three-term affine Koszul covector, before any Hessian-symmetry shortcut. -/
def ambientKoszulTensor (P : BasedCubic E) (x : E) :
    E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ :=
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
def ambientCovariantDerivative (P : BasedCubic E) (u : E)
    (Y : E → E) (x : E) : E :=
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
structure Frame (e : E) (t : E → ℝ) (j : E → E → E)
    (p : Fin 3 → E) : Prop where
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
def qSingle (t : E → ℝ) (j : E → E → E)
    (T : Triple E) (v : Fin 3) (s : Fin 2) : ℝ :=
  pairing t j (power j (T v) 0) (power j (T v) s)
def qPair (t : E → ℝ) (j : E → E → E)
    (T : Triple E) (v w : Fin 3) (s r : Fin 2) : ℝ :=
  pairing t j (power j (T v) s) (power j (T w) r)
def qTriple (t : E → ℝ) (j : E → E → E)
    (T : Triple E) (s r u : Fin 2) : ℝ :=
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
def mapAtoms {t : E → ℝ} {j : E → E → E}
    (g : Automorphism t j) (T : Triple E) : Triple E := fun a i => g.equiv (T a i)
def orbit (t : E → ℝ) (j : E → E → E) (S : Triple E) : Set (Triple E) :=
  {T | ∃ g : Automorphism t j, mapAtoms g S = T}
def fibre54 (e : E) (t : E → ℝ) (j : E → E → E) (b : Chart) : Set (Triple E) :=
  {T | (∀ a, Frame e t j (T a)) ∧ ledger t j T = Glennie.SubmissionR03.decode20 b}
def fibre20 (e : E) (t : E → ℝ) (j : E → E → E) (b : Chart) : Set (Triple E) :=
  {T | (∀ a, Frame e t j (T a)) ∧ Glennie.SubmissionR03.encode20 (ledger t j T) = b}
def SameSign (e : E) (t : E → ℝ) (j : E → E → E) (T S : Triple E) : Prop :=
  (score e t j T < 0 ∧ score e t j S < 0) ∨
    (0 < score e t j T ∧ 0 < score e t j S)
def Admitted (e : E) (t : E → ℝ) (j : E → E → E)
    (V : Set Chart) (T : Triple E) : Prop :=
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
structure Result (e : E) (N : E → ℝ) (t : E → ℝ)
    (a B : E → E → ℝ) (j Gamma : E → E → E) (R : E → E → E → E)
    (nativeN : Glennie.Albert → ℝ) where
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
abbrev ReconstructionResult {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : BasedCubic E) (e : E) :=
  Local.Result e (cubic P) (fun x => traceAt P e x)
    (fun x y => metric P e x y) (fun x y => rawPair P e x y) (product P e)
    (fun x y => ambientConnection P e x y) (ambientCurvature P e) nativeCubic
end
end Glennie.SubmissionR04Intrinsic

@[expose] public section
namespace Glennie.SubmissionR04Intrinsic
noncomputable section
set_option autoImplicit false
open AlbertGeometry.Cubic
open AlbertGeometry.BasedNormDerivativeTransport.BasedNormIso
open AlbertGeometry.BasedNormAdjointTransport
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
def toSource (P : BasedCubic E) : SymmetricTrilinearForm E where
  form := P.form
  swap12 := P.swap12
  swap23 := P.swap23

theorem cubic_eq_source (P : BasedCubic E) (x : E) :
    cubic P x = diagonalCubic (toSource P).form x := rfl

theorem metric_eq_source (P : BasedCubic E) (x : E) :
    metric P x = logHessianForm (toSource P) x := rfl

/- The function and both derivatives are literal, not desired formulas. -/
theorem traceAt_eq_source (P : BasedCubic E) (e : E) :
    traceAt P e = normTrace (toSource P) e := rfl

theorem secondDerivative_eq_source (P : BasedCubic E) (e : E) :
    fderiv ℝ (fun z : E => fderiv ℝ (cubic P) z) e =
      cubicHessian (toSource P) e := rfl

theorem rawPair_eq_source (P : BasedCubic E) (e : E) :
    rawPair P e = rawTraceForm (toSource P) e := rfl

theorem rawPair_apply (P : BasedCubic E) (e x y : E) :
    rawPair P e x y = traceAt P e x * traceAt P e y -
      fderiv ℝ (fun z : E => fderiv ℝ (cubic P) z) e x y := by
  exact rawTraceForm_apply (toSource P) e x y

theorem hasFDerivAt_cubic (P : BasedCubic E) (x : E) :
    HasFDerivAt (cubic P) (fderiv ℝ (cubic P) x) x := by
  exact (differentiable_diagonalCubic (toSource P).form x).hasFDerivAt

theorem hasFDerivAt_traceAt (P : BasedCubic E) (x : E) :
    HasFDerivAt (fun z : E => traceAt P z)
      (fderiv ℝ (fun z : E => traceAt P z) x) x := by
  exact hasFDerivAt_fderiv_diagonalCubic_actual (toSource P) x

/- The factor 3 is a theorem requiring N(e)=1; it is not definitional. -/
theorem rawPair_eq_three_metric (P : BasedCubic E) (e : E)
    (he : cubic P e = 1) (x y : E) :
    rawPair P e x y = 3 * metric P e x y := by
  exact rawTraceForm_eq_three_logMetric (toSource P) e he x y

theorem traceAt_eq_three_metric_unit (P : BasedCubic E) (e : E)
    (he : cubic P e = 1) (x : E) :
    traceAt P e x = 3 * metric P e x e := by
  have hepos : 0 < diagonalCubic (toSource P).form e := by
    change 0 < cubic P e
    rw [he]
    norm_num
  change fderiv ℝ (diagonalCubic (toSource P).form) e x =
    3 * logHessianForm (toSource P) e x e
  rw [logHessianForm_symm (toSource P) hepos x e,
    logHessianForm_radial_at_one (toSource P) e x he]
  ring

variable [FiniteDimensional ℝ E]

/- Build the continuous raw-pairing equivalence from the EXISTING algebraic
nondegeneracy producer. This does not build the tangent metric dual or K. -/
theorem rawPair_isInvertible (P : BasedCubic E) (e : E)
    (he : cubic P e = 1)
    (hp : ∀ x : E, x ≠ 0 → 0 < metric P e x x) :
    (rawPair P e).IsInvertible := by
  let B := rawBilinearForm (toSource P) e
  have hB : B.Nondegenerate := rawBilinearForm_nondegenerate (toSource P) e he hp
  let d : Module.Dual ℝ E ≃ₗ[ℝ] (E →L[ℝ] ℝ) := LinearMap.toContinuousLinearMap
  let A : E ≃L[ℝ] (E →L[ℝ] ℝ) := ((B.toDual hB).trans d).toContinuousLinearEquiv
  refine ⟨A, ?_⟩
  ext x y
  rfl

/- Under the unchanged entrance hypotheses, inverse's zero fallback is excluded. -/
theorem adjoint_pairing (P : BasedCubic E) (e : E)
    (he : cubic P e = 1)
    (hp : ∀ x : E, x ≠ 0 → 0 < metric P e x x) (x y : E) :
    rawPair P e (adjoint P e x) y = fderiv ℝ (cubic P) x y := by
  exact congrArg (fun L : E →L[ℝ] ℝ => L y)
    ((rawPair_isInvertible P e he hp).self_apply_inverse (fderiv ℝ (cubic P) x))

theorem adjoint_unique (P : BasedCubic E) (e : E)
    (he : cubic P e = 1)
    (hp : ∀ x : E, x ≠ 0 → 0 < metric P e x x) (x z : E)
    (hz : ∀ y : E, rawPair P e z y = fderiv ℝ (cubic P) x y) :
    z = adjoint P e x := by
  apply (rawPair_isInvertible P e he hp).bijective.1
  ext y
  rw [hz, adjoint_pairing P e he hp]

/- hB is any proof for the source representation: proof identity is immaterial. -/
theorem adjoint_eq_source (P : BasedCubic E) (e : E)
    (he : cubic P e = 1)
    (hp : ∀ x : E, x ≠ 0 → 0 < metric P e x x)
    (hB : (rawBilinearForm (toSource P) e).Nondegenerate) (x : E) :
    adjoint P e x = intrinsicAdjoint (toSource P) e hB x := by
  apply intrinsicAdjoint_unique (toSource P) e hB x
  intro y
  exact adjoint_pairing P e he hp x y

theorem product_eq_source (P : BasedCubic E) (e : E)
    (he : cubic P e = 1)
    (hp : ∀ x : E, x ≠ 0 → 0 < metric P e x x)
    (hB : (rawBilinearForm (toSource P) e).Nondegenerate) (x y : E) :
    product P e x y = intrinsicProduct (toSource P) e hB x y := by
  simp only [product, intrinsicProduct, intrinsicCross, intrinsicS,
    adjoint_eq_source P e he hp hB, traceAt_eq_source, rawPair_eq_source]


theorem product_eq_sourceProduct (P : BasedCubic E) (e : E)
    (he : cubic P e = 1)
    (hp : ∀ x : E, x ≠ 0 → 0 < metric P e x x) (x y : E) :
    product P e x y = AlbertGeometry.IntrinsicLocalTransport.sourceProduct
      (toSource P) e he hp x y := by
  exact product_eq_source P e he hp
    (rawBilinearForm_nondegenerate (toSource P) e he hp) x y

end
end Glennie.SubmissionR04Intrinsic

@[expose] public section
namespace Glennie.SubmissionR04Intrinsic
noncomputable section
set_option autoImplicit false
open Glennie
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
theorem tangent_eq_source (P : BasedCubic E) (e : E) :
    tangent P e = AlbertGeometry.Cubic.tangentSpace (toSource P) e := rfl

theorem nativeCubic_eq_source (x : Albert) :
    nativeCubic x = AlbertGeometry.NativeNormAlgebra.nativeNewtonNorm x := rfl

theorem nativeTraceLinear_eq_source :
    nativeTraceLinear = AlbertRecognition.traceLinear := by
  ext x
  rfl

theorem nativeTangent_eq_source : NativeTangent = AlbertRecognition.V := by
  change nativeTraceLinear.ker = AlbertRecognition.traceLinear.ker
  rw [nativeTraceLinear_eq_source]

def nativeToSource : NativeTangent ≃ₗ[ℝ] AlbertRecognition.V :=
  LinearEquiv.ofEq _ _ nativeTangent_eq_source

theorem nativeToSource_K (u v : NativeTangent) :
    nativeToSource (nativeK u v) =
      AlbertRecognition.KA (nativeToSource u) (nativeToSource v) := by
  apply Subtype.ext
  simp only [nativeToSource, LinearEquiv.coe_ofEq_apply]
  rfl

theorem nativeToSource_metric (u v : NativeTangent) :
    nativeMetric u v = AlbertRecognition.gA (nativeToSource u) (nativeToSource v) := by
  simp only [nativeToSource, nativeMetric, AlbertRecognition.gA,
    LinearEquiv.coe_ofEq_apply]

private theorem gA_neg_left_local (x y : AlbertRecognition.V) :
    AlbertRecognition.gA (-x) y = -AlbertRecognition.gA x y := by
  change Glennie.inner (-(x : Albert)) (y : Albert) / 3 =
    -(Glennie.inner (x : Albert) (y : Albert) / 3)
  rw [Glennie.inner_neg_left, neg_div]

private theorem gA_sub_left_local (x y z : AlbertRecognition.V) :
    AlbertRecognition.gA (x - y) z =
      AlbertRecognition.gA x z - AlbertRecognition.gA y z := by
  rw [sub_eq_add_neg, AlbertRecognition.gA_add_left, gA_neg_left_local]
  ring

theorem nativeProject_eq_source (x : Albert) :
    (nativeProject x : Albert) = (AlbertRecognition.project x : Albert) := rfl

theorem nativeMetric_eq_source (u v : NativeTangent) :
    nativeMetric u v = AlbertRecognition.gA
      (nativeTangent_eq_source ▸ u)
      (nativeTangent_eq_source ▸ v) := by
  rfl

theorem nativeK_eq_source (u v : NativeTangent) :
    nativeK u v = AlbertRecognition.KA u v := rfl

theorem nativeCurvature_reference (u v w : NativeTangent) :
    nativeToSource (nativeCurvature u v w) =
      -(AlbertRecognition.D (nativeToSource u) (nativeToSource v)
        (nativeToSource w)) := by
  simp only [nativeCurvature, map_add, map_sub, map_smul,
    nativeToSource_K, nativeToSource_metric]
  simp only [AlbertRecognition.D, AlbertRecognition.wedge,
    AlbertRecognition.q, AlbertRecognition.operatorComm,
    AlbertRecognition.KB_referenceCubic,
    LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply]
  change _ =
    -(AlbertRecognition.gA (nativeToSource v) (nativeToSource w) • nativeToSource u -
      AlbertRecognition.gA (nativeToSource u) (nativeToSource w) • nativeToSource v +
      (AlbertRecognition.KA (nativeToSource u)
        (AlbertRecognition.KA (nativeToSource v) (nativeToSource w)) -
       AlbertRecognition.KA (nativeToSource v)
        (AlbertRecognition.KA (nativeToSource u) (nativeToSource w))))
  module

theorem referenceCurvature_eq_native_actual
    (u v w : AlbertRecognition.V) :
    -(AlbertRecognition.D u v w) =
      AlbertGeometry.NativeCurvatureDictionary.nativeCurvatureValue u v w := by
  apply AlbertRecognition.metricDual.injective
  apply LinearMap.ext
  intro t
  change AlbertRecognition.gA (-(AlbertRecognition.D u v w)) t =
    AlbertRecognition.gA
      (AlbertGeometry.NativeCurvatureDictionary.nativeCurvatureValue u v w) t
  rw [AlbertGeometry.NativeCurvatureDictionary.nativeCurvatureValue_pairing,
    AlbertGeometry.NativeCurvatureDictionary.nativeScalarCurvature_eq_native_q]
  simp only [AlbertRecognition.D, AlbertRecognition.wedge,
    AlbertRecognition.q, AlbertRecognition.operatorComm,
    AlbertRecognition.KB_referenceCubic,
    LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply]
  change AlbertRecognition.gA
    (-(AlbertRecognition.gA v w • u - AlbertRecognition.gA u w • v +
      (AlbertRecognition.KA u (AlbertRecognition.KA v w) -
        AlbertRecognition.KA v (AlbertRecognition.KA u w)))) t = _
  simp only [gA_neg_left_local, AlbertRecognition.gA_add_left,
    gA_sub_left_local, AlbertRecognition.gA_smul_left]
  ring

def nativeCurvatureOnV (u v w : AlbertRecognition.V) : AlbertRecognition.V :=
  nativeToSource (nativeCurvature
    (nativeToSource.symm u) (nativeToSource.symm v) (nativeToSource.symm w))

theorem nativeCurvatureOnV_eq_actual (u v w : AlbertRecognition.V) :
    nativeCurvatureOnV u v w =
      AlbertGeometry.NativeCurvatureDictionary.nativeCurvatureValue u v w := by
  rw [nativeCurvatureOnV, nativeCurvature_reference]
  simp only [LinearEquiv.apply_symm_apply]
  exact referenceCurvature_eq_native_actual u v w


theorem ambientConnection_eq_source (P : BasedCubic E) (x : E) :
    ambientConnection P x =
      AlbertGeometry.AmbientLeviCivitaProduct.ambientGamma (toSource P) x := rfl
variable [CompleteSpace E] [FiniteDimensional ℝ E]
theorem ambientCurvature_eq_source (P : BasedCubic E) (x u v w : E) :
    ambientCurvature P x u v w =
      AlbertGeometry.AmbientCurvatureProduct.ambientCurvature (toSource P) x u v w := rfl
end
end Glennie.SubmissionR04Intrinsic

@[expose] public section
namespace Glennie.SubmissionR04Intrinsic
noncomputable section
set_option autoImplicit false
open Glennie
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
def sourceCurvature (P : BasedCubic E) (e : E)
    (K : tangent P e → tangent P e → tangent P e)
    (u v w : tangent P e) : tangent P e :=
  -(metric P e (v : E) (w : E)) • u +
    (metric P e (u : E) (w : E)) • v - K u (K v w) + K v (K u w)


variable [CompleteSpace E]
variable [FiniteDimensional ℝ E]

attribute [local instance] tangentDualNormedAddCommGroup tangentDualNormedSpace
  tangentBilinearNormedAddCommGroup tangentBilinearNormedSpace
  tangentTrilinearNormedAddCommGroup tangentTrilinearNormedSpace
  tangentEndNormedAddCommGroup tangentEndNormedSpace
  tangentVectorBilinearNormedAddCommGroup tangentVectorBilinearNormedSpace
  tangentInverseNormedAddCommGroup tangentInverseNormedSpace

theorem tangentMetricDual_apply (P : BasedCubic E) (e : E)
    (u v : tangent P e) :
    tangentMetricDual P e u v = metric P e (u : E) (v : E) := rfl

theorem independentRaisedCubic_apply (P : BasedCubic E) (e : E)
    (u v : tangent P e) :
    independentRaisedCubic P e u v =
      tangentMetricRaise P e (tangentCubicCurried P e u v) := by
  simp only [independentRaisedCubic, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.compL_apply]


theorem tangentMetricDual_eq_baseChartMetric (P : BasedCubic E) (e : E)
    (he : cubic P e = 1) :
    tangentMetricDual P e = AlbertGeometry.Cubic.baseChartMetric (toSource P) e he := by
  ext u v
  rw [tangentMetricDual_apply, metric_eq_source]
  exact (AlbertGeometry.Cubic.baseChartMetric_apply (toSource P) e he u v).symm

theorem tangentCubicForm_eq_source (P : BasedCubic E) (e : E) :
    tangentCubicForm P e =
      (AlbertGeometry.Cubic.tangentSymmetricCubic (toSource P) e).form := rfl

theorem tangentCubicCurried_eq_source (P : BasedCubic E) (e : E) :
    tangentCubicCurried P e = AlbertGeometry.Cubic.fullyCurried
      (AlbertGeometry.Cubic.tangentSymmetricCubic (toSource P) e) := rfl

theorem tangentMetricRaise_eq_source (P : BasedCubic E) (e : E)
    (he : cubic P e = 1) :
    tangentMetricRaise P e =
      (AlbertGeometry.Cubic.baseChartMetric (toSource P) e he).inverse := by
  unfold tangentMetricRaise
  rw [tangentMetricDual_eq_baseChartMetric P e he]
  rfl

theorem independentRaisedCubic_eq_source (P : BasedCubic E) (e : E)
    (he : cubic P e = 1) :
    independentRaisedCubic P e =
      AlbertGeometry.Cubic.raisedTangentCubic (toSource P) e he := by
  unfold independentRaisedCubic AlbertGeometry.Cubic.raisedTangentCubic
  rw [tangentMetricRaise_eq_source P e he, tangentCubicCurried_eq_source P e]
  rfl


theorem tangent_metric_eq_source (P : BasedCubic E) (e : E)
    (he : cubic P e = 1) (u v : tangent P e) :
    metric P e (u : E) (v : E) =
      AlbertGeometry.Cubic.baseChartMetric (toSource P) e he u v := by
  rw [metric_eq_source]
  exact (AlbertGeometry.Cubic.baseChartMetric_apply (toSource P) e he u v).symm

def sourceK (P : BasedCubic E) (e : E) (he : cubic P e = 1)
    (u v : tangent P e) : tangent P e :=
  AlbertGeometry.Cubic.raisedTangentCubic (toSource P) e he u v

def sourceCurvatureOnSource (P : BasedCubic E) (e : E)
    (he : AlbertGeometry.Cubic.diagonalCubic (toSource P).form e = 1)
    (u v w : AlbertGeometry.Cubic.tangentSpace (toSource P) e) :
    AlbertGeometry.Cubic.tangentSpace (toSource P) e :=
  -(AlbertGeometry.Cubic.baseChartMetric (toSource P) e he v w) • u +
    (AlbertGeometry.Cubic.baseChartMetric (toSource P) e he u w) • v -
    AlbertGeometry.Cubic.raisedTangentCubic (toSource P) e he u
      (AlbertGeometry.Cubic.raisedTangentCubic (toSource P) e he v w) +
    AlbertGeometry.Cubic.raisedTangentCubic (toSource P) e he v
      (AlbertGeometry.Cubic.raisedTangentCubic (toSource P) e he u w)

theorem sourceCurvatureOnSource_eq_actual (P : BasedCubic E) (e : E)
    (he : AlbertGeometry.Cubic.diagonalCubic (toSource P).form e = 1)
    (hp : ∀ u : E, u ≠ 0 → 0 < metric P e u u)
    (u v w : AlbertGeometry.Cubic.tangentSpace (toSource P) e) :
    sourceCurvatureOnSource P e he u v w =
      AlbertGeometry.Cubic.chartCurvature (toSource P) e he 0 u v w := by
  have hpos : ∀ z : E, z ≠ 0 →
      0 < AlbertGeometry.Cubic.logHessianForm (toSource P) e z z := hp
  rw [AlbertGeometry.Cubic.chartCurvature_zero (toSource P) e he hpos]
  simp only [sourceCurvatureOnSource,
    AlbertGeometry.Cubic.baseMetricWedge,
    AlbertGeometry.Cubic.raisedCubicCommutator]
  rw [neg_smul]
  abel

theorem curvaturePremise_iff_actual (P : BasedCubic E) (e : E)
    (he : AlbertGeometry.Cubic.diagonalCubic (toSource P).form e = 1)
    (hp : ∀ z : E, z ≠ 0 → 0 < metric P e z z)
    (F : AlbertRecognition.V ≃ₗ[ℝ]
      AlbertGeometry.Cubic.tangentSpace (toSource P) e) :
    (∀ u v w : AlbertRecognition.V,
      sourceCurvatureOnSource P e he (F u) (F v) (F w) =
        F (nativeCurvatureOnV u v w)) ↔
    (∀ u v w : AlbertRecognition.V,
      AlbertGeometry.Cubic.chartCurvature (toSource P) e he 0
        (F u) (F v) (F w) =
        F (AlbertGeometry.NativeCurvatureDictionary.nativeCurvatureValue u v w)) := by
  simp only [sourceCurvatureOnSource_eq_actual P e he hp,
    nativeCurvatureOnV_eq_actual]

open AlbertGeometry.Cubic AlbertGeometry.NativeCurvatureDictionary
  AlbertGeometry.NativeEuclideanNormBinding

set_option maxHeartbeats 800000 in

def frameToActualIso (P : BasedCubic E) (e : E)
    (he : diagonalCubic (toSource P).form e = 1)
    (hp : ∀ z : E, z ≠ 0 → 0 < metric P e z z)
    (F : AlbertRecognition.V ≃ₗ[ℝ] tangentSpace (toSource P) e)
    (hmetric : ∀ x y : AlbertRecognition.V,
      baseChartMetric (toSource P) e he (F x) (F y) = AlbertRecognition.gA x y)
    (hcurv : ∀ x y z : AlbertRecognition.V,
      sourceCurvatureOnSource P e he (F x) (F y) (F z) =
        F (nativeCurvatureOnV x y z)) :
    AlbertGeometry.RecognitionFromCurvature.TangentCurvatureIso
      (toSource P) e he where
  equiv := F.symm.trans nativeMetricFrame
  map_metric := by
    intro u v
    change baseChartMetric _ _ _ (nativeMetricFrame (F.symm u))
      (nativeMetricFrame (F.symm v)) = baseChartMetric (toSource P) e he u v
    rw [nativeMetricFrame_metric,
      ← hmetric (F.symm u) (F.symm v),
      F.apply_symm_apply, F.apply_symm_apply]
  map_curvature := by
    intro u v w
    have hactual := (curvaturePremise_iff_actual P e he hp F).mp hcurv
      (F.symm u) (F.symm v) (F.symm w)
    simp only [F.apply_symm_apply] at hactual
    change nativeMetricFrame (F.symm (chartCurvature (toSource P) e he 0 u v w)) =
      chartCurvature nativeEuclideanRepresentation nativeCoordinateUnit
        nativeNormalization 0 (nativeMetricFrame (F.symm u))
        (nativeMetricFrame (F.symm v)) (nativeMetricFrame (F.symm w))
    rw [hactual, F.symm_apply_apply]
    exact nativeMetricFrame.apply_symm_apply _

set_option maxHeartbeats 800000 in
theorem actualIso_iff_independentFrame (P : BasedCubic E) (e : E)
    (he : diagonalCubic (toSource P).form e = 1)
    (hp : ∀ z : E, z ≠ 0 → 0 < metric P e z z) :
    Nonempty (AlbertGeometry.RecognitionFromCurvature.TangentCurvatureIso
      (toSource P) e he) ↔
    ∃ F : AlbertRecognition.V ≃ₗ[ℝ] tangentSpace (toSource P) e,
      (∀ x y : AlbertRecognition.V,
        metric P e (F x : E) (F y : E) = AlbertRecognition.gA x y) ∧
      (∀ x y z : AlbertRecognition.V,
        sourceCurvatureOnSource P e he (F x) (F y) (F z) =
          F (nativeCurvatureOnV x y z)) := by
  constructor
  · rintro ⟨I⟩
    let F := AlbertGeometry.RecognitionFromCurvature.matchingMetricFrame
      (toSource P) e he I
    refine ⟨F, ?_, ?_⟩
    · intro x y
      calc
        metric P e (F x : E) (F y : E) =
            baseChartMetric (toSource P) e he (F x) (F y) :=
          tangent_metric_eq_source P e he (F x) (F y)
        _ = AlbertRecognition.gA x y :=
          AlbertGeometry.RecognitionFromCurvature.matchingMetricFrame_metric
            (toSource P) e he I x y
    · apply (curvaturePremise_iff_actual P e he hp F).mpr
      intro x y z
      exact AlbertGeometry.RecognitionFromCurvature.matchingMetricFrame_curvature
        (toSource P) e he I x y z
  · rintro ⟨F, hmetric, hcurv⟩
    refine ⟨frameToActualIso P e he hp F ?_ hcurv⟩
    intro x y
    calc
      baseChartMetric (toSource P) e he (F x) (F y) =
          metric P e (F x : E) (F y : E) :=
        (tangent_metric_eq_source P e he (F x) (F y)).symm
      _ = AlbertRecognition.gA x y := hmetric x y

theorem independentCurvature_eq_sourceFormula (P : BasedCubic E) (e : E)
    (he : cubic P e = 1) (u v w : tangent P e) :
    independentCurvature P e u v w = sourceCurvatureOnSource P e he u v w := by
  simp only [independentCurvature, sourceCurvatureOnSource,
    ← tangentMetricDual_eq_baseChartMetric P e he,
    ← independentRaisedCubic_eq_source P e he]
  rfl


theorem independentCurvature_eq_actual (P : BasedCubic E) (e : E)
    (he : cubic P e = 1)
    (hp : ∀ x : E, x ≠ 0 → 0 < metric P e x x) (u v w : tangent P e) :
    independentCurvature P e u v w =
      AlbertGeometry.Cubic.chartCurvature (toSource P) e he 0 u v w := by
  rw [independentCurvature_eq_sourceFormula P e he]
  exact sourceCurvatureOnSource_eq_actual P e he hp u v w

/-- The source formula now uses only the independently defined raised cubic. -/
theorem actualIso_iff_independentRaisedFrame (P : BasedCubic E) (e : E)
    (he : cubic P e = 1)
    (hp : ∀ x : E, x ≠ 0 → 0 < metric P e x x) :
    Nonempty (AlbertGeometry.RecognitionFromCurvature.TangentCurvatureIso
      (toSource P) e he) ↔
    ∃ F : AlbertRecognition.V ≃ₗ[ℝ] tangent P e,
      (∀ x y : AlbertRecognition.V,
        metric P e (F x : E) (F y : E) = AlbertRecognition.gA x y) ∧
      (∀ x y z : AlbertRecognition.V,
        independentCurvature P e (F x) (F y) (F z) =
          F (nativeCurvatureOnV x y z)) := by
  constructor
  · intro h
    obtain ⟨F, hm, hc⟩ := (actualIso_iff_independentFrame P e he hp).mp h
    refine ⟨F, hm, ?_⟩
    intro x y z
    rw [independentCurvature_eq_sourceFormula P e he]
    exact hc x y z
  · rintro ⟨F, hm, hc⟩
    apply (actualIso_iff_independentFrame P e he hp).mpr
    refine ⟨F, hm, ?_⟩
    intro x y z
    exact (independentCurvature_eq_sourceFormula P e he (F x) (F y) (F z)).symm.trans
      (hc x y z)

end
end Glennie.SubmissionR04Intrinsic

@[expose] public section
namespace Glennie.SubmissionR04Intrinsic.LocalBridge
noncomputable section
set_option autoImplicit false
open AlbertGeometry.Cubic AlbertGeometry.IntrinsicLocalTransport
open AlbertGeometry.RecognitionFromCurvature
open AlbertGeometry.IntrinsicLocalGenerationCapstoneR01

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

/- Native vocabulary equalities by definitional reduction. -/
theorem encode20_binding (L : Local.Ledger54) :
    Glennie.SubmissionR03.encode20 L = Glennie.Compact.Affine20.encode20 L := rfl
theorem decode20_binding (b : Local.Chart) :
    Glennie.SubmissionR03.decode20 b = Glennie.Compact.Affine20.decode20 b := rfl
theorem flatBase_binding :
    Glennie.SubmissionR03.flatBase = Glennie.Compact.Sections.flatBase := rfl

section LocalBindings
variable (P : SymmetricTrilinearForm E) (e : E)
  (he : diagonalCubic P.form e = 1)
  (hp : ∀ x : E, x ≠ 0 → 0 < logHessianForm P e x x)
  (t : E → ℝ) (j : E → E → E)
  (ht : t = sourceTrace P e) (hj : j = sourceProduct P e he hp)
include ht hj

theorem frame_binding (p : Fin 3 → E) :
    Local.Frame e t j p ↔ SourceFrame P e he hp p := by
  subst t
  subst j
  constructor
  · intro h
    exact ⟨h.trace_one, h.idempotent, h.orthogonal, h.sum_unit⟩
  · intro h
    exact ⟨h.trace_one, h.idempotent, h.orthogonal, h.sum_unit⟩

theorem ledger_binding (T : Local.Triple E) :
    Local.ledger t j T = sourceLedger54 P e he hp T := by
  subst t
  subst j
  rfl
theorem q26_binding (T : Local.Triple E) :
    Local.q26 t j T = sourceQ26 P e he hp T := by
  subst t
  subst j
  rfl
theorem score_binding (T : Local.Triple E) :
    Local.score e t j T = sourceScore P e he hp T := by
  subst t
  subst j
  rfl
theorem phi_binding (x y z : E) :
    Local.phi t j x y z = sourcePhi P e he hp x y z := by
  subst t
  subst j
  rfl
theorem sameSign_binding (T S : Local.Triple E) :
    Local.SameSign e t j T S ↔ SameSourceScoreSign P e he hp T S := by
  subst t
  subst j
  rfl

def autToSource (g : Local.Automorphism t j) : SourceAutomorphism P e he hp where
  equiv := g.equiv
  map_product := by
    intro x y
    simpa only [← hj] using g.map_product x y
  map_trace := by
    intro x
    simpa only [← ht] using g.map_trace x
def autFromSource (g : SourceAutomorphism P e he hp) : Local.Automorphism t j where
  equiv := g.equiv
  map_product := by
    intro x y
    simpa only [hj] using g.map_product x y
  map_trace := by
    intro x
    simpa only [ht] using g.map_trace x

/-- Both directions range over ALL product-and-trace linear automorphisms. -/
theorem orbit_binding (T : Local.Triple E) :
    Local.orbit t j T = sourceAutOrbit P e he hp T := by
  ext S
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨autToSource P e he hp t j ht hj g, hg⟩
  · rintro ⟨g, hg⟩
    exact ⟨autFromSource P e he hp t j ht hj g, hg⟩

theorem fibre54_binding (b : Local.Chart) :
    Local.fibre54 e t j b = sourceFibre54 P e he hp b := by
  ext T
  simp only [Local.fibre54, sourceFibre54, Set.mem_setOf_eq,
    frame_binding P e he hp t j ht hj,
    ledger_binding P e he hp t j ht hj, decode20_binding]
theorem fibre20_binding (b : Local.Chart) :
    Local.fibre20 e t j b = sourceFibre20 P e he hp b := by
  ext T
  simp only [Local.fibre20, sourceFibre20, Set.mem_setOf_eq,
    frame_binding P e he hp t j ht hj,
    ledger_binding P e he hp t j ht hj, encode20_binding]

theorem twoOrbitSections_binding (V : Set Local.Chart) :
    Local.TwoOrbitSections e t j V ↔ TwoOrbitSections P e he hp V := by
  simp only [Local.TwoOrbitSections, TwoOrbitSections,
    frame_binding P e he hp t j ht hj,
    ledger_binding P e he hp t j ht hj, decode20_binding,
    score_binding P e he hp t j ht hj,
    fibre54_binding P e he hp t j ht hj,
    fibre20_binding P e he hp t j ht hj,
    orbit_binding P e he hp t j ht hj]

theorem scoreComplete_binding (V : Set Local.Chart) :
    Local.ScoreComplete e t j V ↔ ScoreComplete P e he hp V := by
  simp only [Local.ScoreComplete, ScoreComplete,
    frame_binding P e he hp t j ht hj,
    ledger_binding P e he hp t j ht hj, encode20_binding,
    score_binding P e he hp t j ht hj, q26_binding P e he hp t j ht hj,
    sameSign_binding P e he hp t j ht hj,
    orbit_binding P e he hp t j ht hj]

/-- Internal composition: every equality argument must be discharged by an
upstream identification theorem. The public theorem exposes only the based
cubic, normalization/positivity, and independent full-curvature matching. -/
theorem exists_result_from_actual_entrance
    (N : E → ℝ) (a B : E → E → ℝ)
    (Gamma : E → E → E) (R : E → E → E → E) (nativeN : Glennie.Albert → ℝ)
    (hN : N = diagonalCubic P.form)
    (ha : ∀ x y : E, a x y = logHessianForm P e x y)
    (hB : ∀ x y : E, B x y = 3 * a x y)
    (hGamma : ∀ x y : E, Gamma x y = AlbertGeometry.AmbientLeviCivitaProduct.ambientGamma P e x y)
    (hRdef : R = AlbertGeometry.AmbientCurvatureProduct.ambientCurvature P e)
    (hnativeN : nativeN = AlbertGeometry.NativeCoordinateDictionary.nativeDeterminant)
    (hEntrance : Nonempty (TangentCurvatureIso P e he)) :
    Nonempty (Local.Result e N t a B j Gamma R nativeN) := by
  obtain ⟨d, hgen, hstab, hder⟩ :=
    exists_intrinsic_local_reconstruction_with_generation P e he hp hEntrance
  refine ⟨{
    A := d.A
    map_unit := d.map_unit
    map_norm := ?_
    map_metric := ?_
    map_raw_pairing := ?_
    map_trace := ?_
    map_product := ?_
    map_connection := ?_
    map_curvature := ?_
    V := d.V
    V_open := d.V_open
    flat_mem := ?_
    two_orbits := (twoOrbitSections_binding P e he hp t j ht hj d.V).mpr d.two_orbits
    score_complete := (scoreComplete_binding P e he hp t j ht hj d.V).mpr
      d.finite_observation_test
    q26_iff_ledger := ?_
    score_eq_two_phi := ?_
    atoms_generate := ?_
    atom_stabilizer := ?_
    atom_derivation := ?_ }⟩
  · intro x
    rw [hnativeN, hN]
    exact d.map_norm x
  · intro x y
    rw [ha x y]
    exact d.map_metric x y
  · intro x y
    rw [hB x y, ha x y, d.map_metric x y]
    change 3 * (Glennie.inner (d.A x) (d.A y) / 3) =
      Glennie.inner (d.A x) (d.A y)
    ring
  · intro x
    rw [ht]
    exact sourceTrace_eq P e d.A d.map_unit d.map_metric x
  · intro x y
    rw [hj]
    exact d.map_product x y
  · intro x y
    rw [hGamma x y]
    exact d.map_connection x y
  · intro u v w
    rw [hRdef]
    exact d.map_curvature u v w
  · rw [ledger_binding P e he hp t j ht hj, encode20_binding, flatBase_binding]
    exact d.flat_mem
  · intro T S hT hS
    rw [q26_binding P e he hp t j ht hj T,
      q26_binding P e he hp t j ht hj S,
      ledger_binding P e he hp t j ht hj T,
      ledger_binding P e he hp t j ht hj S]
    exact sourceQ26_eq_iff_ledger54_eq P e he hp d.A
      d.map_unit d.map_metric d.map_product T S
      (fun f => (frame_binding P e he hp t j ht hj (T f)).mp (hT f))
      (fun f => (frame_binding P e he hp t j ht hj (S f)).mp (hS f))
  · intro T
    rw [score_binding P e he hp t j ht hj T,
      phi_binding P e he hp t j ht hj]
    exact sourceScore_eq_twoPhi P e he hp d.A
      d.map_unit d.map_metric d.map_product T
  · intro T hT K hK hAtoms
    have hframes : ∀ f, SourceFrame P e he hp (T f) :=
      fun f => (frame_binding P e he hp t j ht hj (T f)).mp (hT.1 f)
    have hb : Glennie.Compact.Affine20.encode20 (sourceLedger54 P e he hp T) ∈ d.V := by
      simpa only [ledger_binding P e he hp t j ht hj, encode20_binding] using hT.2
    have hK' : ∀ p ∈ K, ∀ q ∈ K, sourceProduct P e he hp p q ∈ K := by
      simpa only [hj] using hK
    exact hgen T hframes hb K hK' hAtoms
  · intro T hT g hfix
    have hframes : ∀ f, SourceFrame P e he hp (T f) :=
      fun f => (frame_binding P e he hp t j ht hj (T f)).mp (hT.1 f)
    have hb : Glennie.Compact.Affine20.encode20 (sourceLedger54 P e he hp T) ∈ d.V := by
      simpa only [ledger_binding P e he hp t j ht hj, encode20_binding] using hT.2
    exact hstab T hframes hb (autToSource P e he hp t j ht hj g) hfix
  · intro T hT D hD hkill
    have hframes : ∀ f, SourceFrame P e he hp (T f) :=
      fun f => (frame_binding P e he hp t j ht hj (T f)).mp (hT.1 f)
    have hb : Glennie.Compact.Affine20.encode20 (sourceLedger54 P e he hp T) ∈ d.V := by
      simpa only [ledger_binding P e he hp t j ht hj, encode20_binding] using hT.2
    have hD' : ∀ p q, D (sourceProduct P e he hp p q) =
        sourceProduct P e he hp (D p) q + sourceProduct P e he hp p (D q) := by
      simpa only [hj] using hD
    exact hder T hframes hb D hD' hkill
end LocalBindings

end
end Glennie.SubmissionR04Intrinsic.LocalBridge

@[expose] public section
namespace Glennie.SubmissionR04Intrinsic
noncomputable section
set_option autoImplicit false
theorem intrinsic_local_reconstruction
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E]
    (P : BasedCubic E) (e : E) (he : cubic P e = 1)
    (hp : ∀ x : E, x ≠ 0 → 0 < metric P e x x)
    (hMatch : ∃ F : NativeTangent ≃ₗ[ℝ] tangent P e,
      (∀ x y : NativeTangent,
        metric P e (F x : E) (F y : E) = nativeMetric x y) ∧
      (∀ x y z : NativeTangent,
        independentCurvature P e (F x) (F y) (F z) =
          F (nativeCurvature x y z))) :
    Nonempty (ReconstructionResult P e) := by
  obtain ⟨F, hmetric, hcurvature⟩ := hMatch
  let FSource : AlbertRecognition.V ≃ₗ[ℝ] tangent P e :=
    nativeToSource.symm.trans F
  have hmetricSource : ∀ x y : AlbertRecognition.V,
      metric P e (FSource x : E) (FSource y : E) = AlbertRecognition.gA x y := by
    intro x y
    change metric P e (F (nativeToSource.symm x) : E)
      (F (nativeToSource.symm y) : E) = AlbertRecognition.gA x y
    rw [hmetric, nativeToSource_metric]
    simp only [LinearEquiv.apply_symm_apply]
  have hcurvatureSource : ∀ x y z : AlbertRecognition.V,
      independentCurvature P e (FSource x) (FSource y) (FSource z) =
        FSource (nativeCurvatureOnV x y z) := by
    intro x y z
    change independentCurvature P e (F (nativeToSource.symm x))
      (F (nativeToSource.symm y)) (F (nativeToSource.symm z)) =
        F (nativeToSource.symm (nativeCurvatureOnV x y z))
    rw [hcurvature]
    simp only [nativeCurvatureOnV, LinearEquiv.symm_apply_apply]
  have hActual : Nonempty
      (AlbertGeometry.RecognitionFromCurvature.TangentCurvatureIso (toSource P) e he) :=
    (actualIso_iff_independentRaisedFrame P e he hp).mpr
      ⟨FSource, hmetricSource, hcurvatureSource⟩
  have ht : (fun x : E => traceAt P e x) =
      AlbertGeometry.IntrinsicLocalTransport.sourceTrace (toSource P) e :=
    by
      funext x
      exact traceAt_eq_three_metric_unit P e he x
  have hj : product P e =
      AlbertGeometry.IntrinsicLocalTransport.sourceProduct (toSource P) e he hp := by
    funext x y
    exact product_eq_sourceProduct P e he hp x y
  have hN : cubic P = AlbertGeometry.Cubic.diagonalCubic (toSource P).form :=
    funext (cubic_eq_source P)
  have ha : ∀ x y : E, metric P e x y =
      AlbertGeometry.Cubic.logHessianForm (toSource P) e x y := by
    intro x y
    exact congrArg (fun B => B x y) (metric_eq_source P e)
  have hGamma : ∀ x y : E, ambientConnection P e x y =
      AlbertGeometry.AmbientLeviCivitaProduct.ambientGamma (toSource P) e x y := by
    intro x y
    exact congrArg (fun G => G x y) (ambientConnection_eq_source P e)
  have hRdef : ambientCurvature P e =
      AlbertGeometry.AmbientCurvatureProduct.ambientCurvature (toSource P) e := by
    funext u v w
    exact ambientCurvature_eq_source P e u v w
  have hn : nativeCubic = AlbertGeometry.NativeCoordinateDictionary.nativeDeterminant := by
    funext x
    exact (nativeCubic_eq_source x).trans
      (AlbertGeometry.NativeCoordinateDictionary.nativeNewtonNorm_eq_nativeDeterminant x)
  exact LocalBridge.exists_result_from_actual_entrance
    (toSource P) e he hp (fun x => traceAt P e x) (product P e) ht hj
    (cubic P) (fun x y => metric P e x y) (fun x y => rawPair P e x y)
    (fun x y => ambientConnection P e x y) (ambientCurvature P e) nativeCubic
    hN ha (rawPair_eq_three_metric P e he) hGamma hRdef hn hActual

end
end Glennie.SubmissionR04Intrinsic
