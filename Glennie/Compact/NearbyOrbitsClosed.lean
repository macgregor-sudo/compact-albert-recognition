module

public import Glennie.Compact.PairNormNearby

/- Nearby fibre classification with local orbit-completeness premises discharged.

`NearbyOrbits.nearby_sign_rigidity` and `NearbyOrbits.nearby_fibres_two_orbits` take
`LocalOrbitCompleteness flatBaseTriple` and `LocalOrbitCompleteness flatBaseRev3`.
`PairNormNearby.localOrbitCompleteness_flatBaseTriple` and
`PairNormNearby.localOrbitCompleteness_flatBaseRev3` discharge these premises.
`PairNormNearby.both_localOrbitCompleteness` packages their conjunction; the consumers
here use the separate theorems. `PairNormNearby` imports `NearbyOrbits`, so the single
import supplies all declarations needed by this module.

WHAT THE RESULT SAYS, in words, so that it is not overstated. Two statements, both local and
both about ORDERED triples under the DIAGONAL action.

 (1) Sign rigidity. There is an open set of ledger values containing the flat one such that
     any two genuine frame triples with the SAME 54-entry ledger in that set whose Phi values
     have the SAME SIGN are carried onto one another by a single automorphism acting on all
     nine atoms. Near the flat ledger, the ledger plus the sign of Phi determines the triple
     up to one automorphism.

 (2) The fibre classification. There is an open neighbourhood of the flat chart point in the
     twenty-coordinate chart space, and two continuous sections over it, one with Phi > 0 and
     one with Phi < 0, such that over EVERY chart point of that neighbourhood the full
     54-entry fibre is EXACTLY the union of the two automorphism orbits of the two section
     values, those two orbits are DISJOINT, and the twenty-coordinate fibre is the same set.

WHAT IS STILL NOT CLAIMED. The neighbourhood is existential: there is no radius, no size and
no construction. The two sections are existential too -- they come from
`NativeFlatSections.native_flat_two_sections_full54`, whose only regularity clause is
`ContinuousOn` -- so the classification names the orbits of two functions that are known to
exist and are not computable from this statement. NO SECTION IS DIFFERENTIATED ANYWHERE in
the chain. And "exactly two" is a count of ORBITS OF ORDERED TRIPLES under the diagonal
action: modulo the 1296 outcome relabellings the flat fibre is ONE class
(`FlatOrbit.flat_fibre_eq_single_relabel_class`), a different statement about a different
object, and quotienting would delete the result rather than weaken it.

NO RESIDUAL SIDE CONDITION. The fibre classification is FALSE without Phi-nonvanishing, because a member
with Phi = 0 would lie in neither orbit. That is discharged unconditionally by
`NearbyOrbits.phi_bounded_away_near_flat` (:295), which shrinks the neighbourhood until every
frame triple over it has |Phi| > 1/27. PairNormNearby's Phi-SIGN conditions sit INSIDE the
existential open set of `LocalOrbitCompleteness` -- `PBox` intersected with {Phi < 0} at the
original triple and with {Phi > 0} at the reversal -- and so are not premises either. The Phi
signs that survive into the conclusion of (2) are CONCLUSIONS about the two sections, not
assumptions about anything. Neither theorem below has a hypothesis of any kind.

CONVENTIONS. flatXN = diag(1,0,-1)
(FlatBase.lean); `encoder p = p 2 - p 0` (Native.lean); Phi = -4/27 at the ORIGINAL
flat ordered triple (`FlatOrbit.phi_flatBase`) and +4/27 at `flatBaseRev3`, the THIRD-frame
reversal, over the one shared ledger, which is why the two base points carry OPPOSITE Phi-sign
conditions. `flatFramePRev := projectorFrame witnessX` -- the FIRST-frame convention, built on
a different element from `flatFrameP := projectorFrame flatXN` -- is named in this header only
and occurs in no statement below, so it cannot leak in. Octonion conjugation is an
ANTI-automorphism and is not used here; no sign is corrected anywhere. `mapAtoms` is the
DIAGONAL action, one automorphism on all nine atoms (Relabel.lean), and
`CompactAutomorphism.comp g h` means "first h, then g" (Automorphism.lean).

NO NOVELTY IS CLAIMED. The level-set and orbit description of a frame-triple fibre may well be
classical for H3(K); this module only closes a premise.
-/

@[expose] public section

namespace Glennie.Compact.NearbyOrbitsClosed

open Glennie Glennie.Compact.FlatBase Glennie.Compact.Affine20
open Glennie.Compact.FrameTopology Glennie.Compact.FlatOrbit
open Glennie.Compact.Sections Glennie.Compact.NearbyOrbits

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-! ## 1. Sign rigidity over a neighbourhood of the flat ledger, with no premise -/

/-- **UNCONDITIONAL SIGN RIGIDITY.** `NearbyOrbits.nearby_sign_rigidity` (:415) with both of
its premises discharged by `PairNormNearby`. Over an open set of ledger values containing the
flat one, two genuine frame triples with equal ledgers and Phi of the same sign are related by
one automorphism acting diagonally on all nine atoms. -/
theorem nearby_sign_rigidity_unconditional :
    ∃ V : Set Ledger54, IsOpen V ∧ ledger54 flatBaseTriple ∈ V ∧
      ∀ T S : Triple, (∀ a : Fin 3, Glennie.Frame (T a)) →
        (∀ a : Fin 3, Glennie.Frame (S a)) → ledger54 T ∈ V →
        ledger54 T = ledger54 S →
        ((phiOf T < 0 ∧ phiOf S < 0) ∨ (0 < phiOf T ∧ 0 < phiOf S)) →
        ∃ k : Glennie.CompactAutomorphism, mapAtoms k S = T :=
  NearbyOrbits.nearby_sign_rigidity
    PairNormNearby.localOrbitCompleteness_flatBaseTriple
    PairNormNearby.localOrbitCompleteness_flatBaseRev3

/-! ## 2. The nearby fibre classification, with no premise -/

/-- **THE UNCONDITIONAL NEARBY FIBRE CLASSIFICATION.**
`NearbyOrbits.nearby_fibres_two_orbits` (:510) with both of its premises discharged by
`PairNormNearby`. Over an open chart neighbourhood of the flat chart point, every full
54-entry fibre is exactly the disjoint union of the two section orbits under the diagonal
automorphism action, and the twenty-coordinate fibre is the same set.

ORDERED TRIPLES, DIAGONAL ACTION. "Exactly two" counts orbits of ordered triples under one
automorphism applied to all nine atoms. No relabelling is quotiented anywhere. -/
theorem nearby_fibres_two_orbits_unconditional :
    ∃ V : Set (Fin 20 → ℝ), IsOpen V ∧
      encode20 (ledger54 Glennie.Compact.Sections.flatBase) ∈ V ∧
      ∃ secPos secNeg : (Fin 20 → ℝ) → Triple,
        ContinuousOn secPos V ∧ ContinuousOn secNeg V ∧
        (∀ b ∈ V, ∀ a : Fin 3, Glennie.Frame (secPos b a)) ∧
        (∀ b ∈ V, ∀ a : Fin 3, Glennie.Frame (secNeg b a)) ∧
        (∀ b ∈ V, encode20 (ledger54 (secPos b)) = b) ∧
        (∀ b ∈ V, encode20 (ledger54 (secNeg b)) = b) ∧
        (∀ b ∈ V, ledger54 (secPos b) = decode20 b) ∧
        (∀ b ∈ V, ledger54 (secNeg b) = decode20 b) ∧
        (∀ b ∈ V, 0 < phiOf (secPos b)) ∧
        (∀ b ∈ V, phiOf (secNeg b) < 0) ∧
        (∀ b ∈ V, fibre54 b = autOrbit (secNeg b) ∪ autOrbit (secPos b)) ∧
        (∀ b ∈ V, Disjoint (autOrbit (secNeg b)) (autOrbit (secPos b))) ∧
        (∀ b ∈ V, fibre20 b = fibre54 b) :=
  NearbyOrbits.nearby_fibres_two_orbits
    PairNormNearby.localOrbitCompleteness_flatBaseTriple
    PairNormNearby.localOrbitCompleteness_flatBaseRev3

/-! ## 3. The discharged premise holds at every point of both orbits

`NearbyOrbits.localOrbitCompleteness_mapAtoms` (:359) is the statement that the premise is a
property of the ORBIT rather than of the point, and it is unconditional. Composed with the two
endpoints it says the premise now holds, with no hypothesis, at every triple either orbit
reaches. These two are corollaries for downstream use; the headline results are sections 1 and
2 above. -/

/-- The discharged premise at every point of the orbit of the original flat ordered triple. -/
theorem localOrbitCompleteness_mapAtoms_flatBaseTriple (g : Glennie.CompactAutomorphism) :
    LocalOrbitCompleteness (mapAtoms g flatBaseTriple) :=
  NearbyOrbits.localOrbitCompleteness_mapAtoms g
    PairNormNearby.localOrbitCompleteness_flatBaseTriple

/-- The discharged premise at every point of the orbit of the third-frame reversal. -/
theorem localOrbitCompleteness_mapAtoms_flatBaseRev3 (g : Glennie.CompactAutomorphism) :
    LocalOrbitCompleteness (mapAtoms g flatBaseRev3) :=
  NearbyOrbits.localOrbitCompleteness_mapAtoms g
    PairNormNearby.localOrbitCompleteness_flatBaseRev3

end
end Glennie.Compact.NearbyOrbitsClosed
