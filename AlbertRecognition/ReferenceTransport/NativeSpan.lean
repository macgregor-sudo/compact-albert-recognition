/- The 51 constructed native reference directions span the actual trace kernel.
no numerical-rank or spanning premise. -/
module

public import AlbertRecognition.ReferenceTransport.FiniteFamily
public import AlbertRecognition.FixedFrame.FrameCoordinates
public import Mathlib.LinearAlgebra.Span.Basic

@[expose] public section
namespace AlbertRecognition.ReferenceTransport
noncomputable section
open Glennie AlbertRecognition.FixedFrame

def familySpan : Submodule ℝ V := Submodule.span ℝ (Set.range direction)

theorem direction_mem_familySpan (i : FamilyIndex) : direction i ∈ familySpan :=
  Submodule.subset_span ⟨i,rfl⟩

theorem slot_basis_mem_familySpan (slot : Fin 3) (t : Fin 8) :
    slotVector slot (octBasis t) ∈ familySpan := by
  have hd := familySpan.sub_mem
    (direction_mem_familySpan (Sum.inr (slot,t,true)))
    (direction_mem_familySpan (Sum.inr (slot,t,false)))
  have hs := familySpan.smul_mem (-1/3 : ℝ) hd
  have hc : (-1/3 : ℝ) * (-3) = 1 := by norm_num
  simpa only [direction_difference, smul_smul, hc, one_smul] using hs

theorem slot_mem_familySpan (slot : Fin 3) (a : Octonion) :
    slotVector slot a ∈ familySpan := by
  rw [oct_decompose a]
  simp only [map_add, map_smul]
  repeat' apply familySpan.add_mem
  all_goals apply familySpan.smul_mem
  all_goals exact slot_basis_mem_familySpan slot _

theorem frameD_eq_directions :
    frameD = (1/3 : ℝ) • (h 2 - h 1) := by
  apply Subtype.ext
  apply Albert.ext <;> norm_num [frameD, h, e, unit, smul_eq_mul]

theorem h_mem_familySpan (i : Fin 3) : h i ∈ familySpan := by
  rw [← direction_diagonal]
  exact direction_mem_familySpan (Sum.inl i)

theorem frameD_mem_familySpan : frameD ∈ familySpan := by
  rw [frameD_eq_directions]
  exact familySpan.smul_mem _
    (familySpan.sub_mem (h_mem_familySpan 2) (h_mem_familySpan 1))

theorem frameSpin_mem_familySpan (s : Spin) : frameSpin s ∈ familySpan := by
  rcases s with ⟨u,v⟩
  rw [frameSpin_apply]
  exact familySpan.add_mem (slot_mem_familySpan 0 u) (slot_mem_familySpan 1 v)

theorem mem_familySpan (x : V) : x ∈ familySpan := by
  rw [frame_decompose x]
  exact familySpan.add_mem
    (familySpan.add_mem
      (familySpan.add_mem
        (familySpan.smul_mem _ (h_mem_familySpan 0))
        (familySpan.smul_mem _ frameD_mem_familySpan))
      (slot_mem_familySpan 2 _))
    (frameSpin_mem_familySpan _)

theorem familySpan_eq_top : familySpan = ⊤ := by
  apply top_unique
  intro x hx
  exact mem_familySpan x

theorem span_directions : Submodule.span ℝ (Set.range direction) = ⊤ :=
  familySpan_eq_top

/-- Equality on the actual finite orbit directions determines every linear map. -/
theorem linear_ext_on_directions {W : Type*} [AddCommGroup W] [Module ℝ W]
    (f g : V →ₗ[ℝ] W) (hfg : ∀ i : FamilyIndex, f (direction i) = g (direction i)) :
    f = g := by
  apply (Submodule.linearMap_eq_iff_of_span_eq_top f g span_directions).mpr
  rintro ⟨x,hx⟩
  obtain ⟨i,rfl⟩ := hx
  exact hfg i

end
end AlbertRecognition.ReferenceTransport
