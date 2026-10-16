/- Full native Albert Jacobi-kernel line from actual finite reference transport.
no unknown invariance or spanning premise is introduced. -/
module

public import AlbertRecognition.FixedFrame.FrameTransport
public import AlbertRecognition.ReferenceTransport.NativeSpan
public import AlbertRecognition.CubicAlgebra

@[expose] public section
namespace AlbertRecognition.FixedFrame
noncomputable section

/-- The actual 51-direction spanning theorem extends the single transported
scalar to every first argument of the native multiplication operator. -/
theorem KB_eq_scalar_reference_of_A_q_zero (B : SymmetricCubic)
    (hB : A (q referenceCubic) B = 0) : ∃ b : ℝ, KB B = b • KA := by
  obtain ⟨b,hb⟩ := common_scalar_on_reference_frames B hB
  refine ⟨b, ?_⟩
  apply ReferenceTransport.linear_ext_on_directions (KB B) (b • KA)
  intro i
  change KB B (automorphismV (ReferenceTransport.transporter i) (h 0)) =
    b • KA (automorphismV (ReferenceTransport.transporter i) (h 0))
  exact hb (ReferenceTransport.transporter i) 0

/-- Faithfulness of the actual trace/3 index raising recovers the whole form. -/
theorem cubic_eq_scalar_reference_of_A_q_zero (B : SymmetricCubic)
    (hB : A (q referenceCubic) B = 0) :
    ∃ b : ℝ, B = scalarCubic b referenceCubic := by
  obtain ⟨b,hb⟩ := KB_eq_scalar_reference_of_A_q_zero B hB
  refine ⟨b, ?_⟩
  apply KB_injective
  rw [KB_scalarCubic, KB_referenceCubic]
  exact hb

/-- Literal equality of the native Jacobi kernel with the reference cubic line.
The forward direction uses only the original arbitrary-B Jacobi equation. -/
theorem reference_nativeKernelLine : NativeKernelLine referenceCubic := by
  intro B
  constructor
  · exact cubic_eq_scalar_reference_of_A_q_zero B
  · rintro ⟨b,rfl⟩
    rw [A_scalarCubic, A_q_self]
    exact smul_zero _

end
end AlbertRecognition.FixedFrame
