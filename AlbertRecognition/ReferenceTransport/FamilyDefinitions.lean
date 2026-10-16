/- Explicit finite native reference transporters. No orbit theorem is used. -/
module

public import AlbertRecognition.Transporter
public import AlbertRecognition.FixedFrame.CyclicPullback
public import AlbertRecognition.FixedFrame.OctonionCommutants

@[expose] public section
namespace AlbertRecognition.ReferenceTransport
noncomputable section
open Glennie AlbertRecognition.FixedFrame
open scoped Quaternion

/-- Three diagonal cases and 3 slots × 8 units × 2 signs. -/
abbrev FamilyIndex := Fin 3 ⊕ (Fin 3 × Fin 8 × Bool)

theorem family_card : Fintype.card FamilyIndex = 51 := by
  simp [FamilyIndex]

def signedBasis (t : Fin 8) (plus : Bool) : Octonion :=
  if plus then octBasis t else -octBasis t

theorem octBasis_norm (t : Fin 8) : octNormSq (octBasis t) = 1 := by
  fin_cases t <;>
    norm_num [octBasis, octNormSq, Quaternion.normSq_def', octScalar, qi, qj, qk]

theorem signedBasis_norm (t : Fin 8) (plus : Bool) :
    octNormSq (signedBasis t plus) = 1 := by
  cases plus
  · change octNormSq (-octBasis t) = 1
    have hn : octNormSq (-octBasis t) = octNormSq (octBasis t) := by
      simp [octNormSq, Quaternion.normSq_def']
    rw [hn, octBasis_norm]
  · exact octBasis_norm t

/-- Slots are ordered 01,02,12 and always store native upper entries. -/
def slotVector : Fin 3 → (Octonion →ₗ[ℝ] V) := ![X01, X02, X12]

def slotIdempotent (slot : Fin 3) (a : Octonion) : Albert :=
  ![⟨1/2,1/2,0,(1/2 : ℝ) • a,0,0⟩,
    ⟨1/2,0,1/2,0,(1/2 : ℝ) • a,0⟩,
    ⟨0,1/2,1/2,0,0,(1/2 : ℝ) • a⟩] slot

/-- Same real half rotation for both signs; the middle triple carries ±a. -/
def transport12 (a : Octonion) (ha : octNormSq a = 1) : CompactAutomorphism :=
  (octMiddleTriple a ha).compactAutomorphism.comp
    (Transporter.realHalfRotation.comp realSwap01Automorphism)

def slotTransporter (slot : Fin 3) (a : Octonion)
    (ha : octNormSq a = 1) : CompactAutomorphism :=
  ![realSwap01Automorphism.comp (realSwap02Automorphism.comp (transport12 a ha)),
    realSwap01Automorphism.comp (transport12 a ha), transport12 a ha] slot

def transporter : FamilyIndex → CompactAutomorphism
  | Sum.inl i => ![CompactAutomorphism.refl, realSwap01Automorphism,
      realSwap02Automorphism] i
  | Sum.inr (slot,t,plus) =>
      slotTransporter slot (signedBasis t plus) (signedBasis_norm t plus)

def familyIdempotent : FamilyIndex → Albert
  | Sum.inl i => e i
  | Sum.inr (slot,t,plus) => slotIdempotent slot (signedBasis t plus)

/-- Actual trace-kernel restriction of the constructed reference automorphism. -/
def direction (i : FamilyIndex) : V := automorphismV (transporter i) (h 0)

end
end AlbertRecognition.ReferenceTransport
