/- One positive section produces the negative section through an explicit
involutive ledger reversal. Generic conditional statement; no native gate
or section/rank producer is asserted. -/
module
public import Mathlib.Topology.ContinuousOn
public import Mathlib.Topology.Continuous
public import Mathlib.Basic.Real.Basic

@[expose] public section
namespace Glennie.RobustBranchCore

variable {X L : Type*}

def reversalDomain (tau : L → L) (U : Set L) : Set L := U ∩ tau ⁻¹' U

def reversalSection (reverse : X → X) (tau : L → L) (positiveSection : L → X) :
    L → X := fun b => reverse (positiveSection (tau b))

/-- Under involution, the preimage description is exactly U intersect tau(U). -/
theorem reversalDomain_eq_inter_image (tau : L → L)
    (hinv : Function.Involutive tau) (U : Set L) :
    reversalDomain tau U = U ∩ tau '' U := by
  ext b
  constructor
  · rintro ⟨hb, htaub⟩
    exact ⟨hb, tau b, htaub, hinv b⟩
  · rintro ⟨hb, ⟨c, hc, hcb⟩⟩
    refine ⟨hb, ?_⟩
    change tau b ∈ U
    rw [← hcb, hinv c]
    exact hc

/-- The reversal fixed base point belongs to the common section domain. -/
theorem flat_mem_reversalDomain (tau : L → L) (U : Set L)
    (flat : L) (hflat : flat ∈ U) (hfixed : tau flat = flat) :
    flat ∈ reversalDomain tau U := by
  exact ⟨hflat, by change tau flat ∈ U; rw [hfixed]; exact hflat⟩

/-- Literal ledger naturality and involution give a right inverse at SAME b. -/
theorem reversalSection_ledger (ledger : X → L) (reverse : X → X) (tau : L → L)
    (hinv : Function.Involutive tau)
    (hledgerReverse : ∀ x, ledger (reverse x) = tau (ledger x))
    (U : Set L) (positiveSection : L → X)
    (hsection : ∀ b ∈ U, ledger (positiveSection b) = b) :
    ∀ b ∈ reversalDomain tau U,
      ledger (reversalSection reverse tau positiveSection b) = b := by
  intro b hb
  change ledger (reverse (positiveSection (tau b))) = b
  rw [hledgerReverse, hsection (tau b) hb.2, hinv b]

/-- Literal Phi reversal converts the positive section value at tau(b) to negative. -/
theorem reversalSection_negative (phi : X → ℝ) (reverse : X → X) (tau : L → L)
    (hphiReverse : ∀ x, phi (reverse x) = -phi x)
    (U : Set L) (positiveSection : L → X)
    (hpositive : ∀ b ∈ U, 0 < phi (positiveSection b)) :
    ∀ b ∈ reversalDomain tau U,
      phi (reversalSection reverse tau positiveSection b) < 0 := by
  intro b hb
  change phi (reverse (positiveSection (tau b))) < 0
  rw [hphiReverse]
  exact neg_lt_zero.mpr (hpositive (tau b) hb.2)

/-- Native valid-frame/positivity/primitivity transport must supply hvalidReverse;
this abstract lemma does not manufacture those conclusions. -/
theorem reversalSection_valid (Valid : X → Prop) (reverse : X → X) (tau : L → L)
    (hvalidReverse : ∀ x, Valid x → Valid (reverse x))
    (U : Set L) (positiveSection : L → X)
    (hvalid : ∀ b ∈ U, Valid (positiveSection b)) :
    ∀ b ∈ reversalDomain tau U,
      Valid (reversalSection reverse tau positiveSection b) := by
  intro b hb
  exact hvalidReverse _ (hvalid (tau b) hb.2)

section Topology
variable [TopologicalSpace X] [TopologicalSpace L]

theorem reversalDomain_isOpen (tau : L → L) (htau : Continuous tau)
    (U : Set L) (hU : IsOpen U) : IsOpen (reversalDomain tau U) := by
  exact hU.inter (IsOpen.preimage htau hU)

theorem reversalSection_continuousOn (reverse : X → X) (tau : L → L)
    (hreverse : Continuous reverse) (htau : Continuous tau)
    (U : Set L) (positiveSection : L → X)
    (hsection : ContinuousOn positiveSection U) :
    ContinuousOn (reversalSection reverse tau positiveSection) (reversalDomain tau U) := by
  have hcomp : ContinuousOn (fun b => positiveSection (tau b)) (reversalDomain tau U) :=
    hsection.comp' htau.continuousOn (fun b hb => hb.2)
  exact hreverse.comp_continuousOn' hcomp

/-- One positive continuous section is sufficient for the two-section interface
on the common nonempty open domain. No second derivative/rank claim is needed here. -/
theorem two_sections_of_reversal (ledger : X → L) (phi : X → ℝ)
    (reverse : X → X) (tau : L → L)
    (hinv : Function.Involutive tau)
    (hledgerReverse : ∀ x, ledger (reverse x) = tau (ledger x))
    (hphiReverse : ∀ x, phi (reverse x) = -phi x)
    (hreverse : Continuous reverse) (htau : Continuous tau)
    (U : Set L) (hU : IsOpen U) (flat : L)
    (hflat : flat ∈ U) (hfixed : tau flat = flat)
    (positiveSection : L → X) (hc : ContinuousOn positiveSection U)
    (hsection : ∀ b ∈ U, ledger (positiveSection b) = b)
    (hpositive : ∀ b ∈ U, 0 < phi (positiveSection b)) :
    IsOpen (reversalDomain tau U) ∧
      flat ∈ reversalDomain tau U ∧
      ContinuousOn positiveSection (reversalDomain tau U) ∧
      ContinuousOn (reversalSection reverse tau positiveSection) (reversalDomain tau U) ∧
      (∀ b ∈ reversalDomain tau U,
        ledger (positiveSection b) = b ∧
        ledger (reversalSection reverse tau positiveSection b) = b ∧
        0 < phi (positiveSection b) ∧
        phi (reversalSection reverse tau positiveSection b) < 0) := by
  refine ⟨reversalDomain_isOpen tau htau U hU,
    flat_mem_reversalDomain tau U flat hflat hfixed,
    hc.mono (fun b hb => hb.1),
    reversalSection_continuousOn reverse tau hreverse htau U positiveSection hc, ?_⟩
  intro b hb
  exact ⟨hsection b hb.1,
    reversalSection_ledger ledger reverse tau hinv hledgerReverse U positiveSection hsection b hb,
    hpositive b hb.1,
    reversalSection_negative phi reverse tau hphiReverse U positiveSection hpositive b hb⟩

end Topology
end Glennie.RobustBranchCore
