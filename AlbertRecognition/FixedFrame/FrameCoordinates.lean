/- Rational 1+9+16 fixed-frame coordinates on the actual compact trace kernel.
The scaled metric is explicit; no inner-product instance is installed. -/
module

public import AlbertRecognition.Reference
public import AlbertRecognition.FixedFrame.SpinCommutant

@[expose] public section
namespace AlbertRecognition.FixedFrame
noncomputable section
open Glennie

abbrev FrameCoordinates := ℝ × ℝ × Octonion × Spin

/-- Complementary diagonal direction d=e1-e2 for the zero-based frame. -/
def frameD : V := ⟨⟨0, 1, -1, 0, 0, 0⟩, by
  change (0 : ℝ) + 1 + (-1) = 0
  norm_num⟩

theorem frameD_coe : (frameD : Albert) = e 1 - e 2 := by
  apply Albert.ext <;> norm_num [frameD, e]

/-- The ordered spin pair is the actual upper-slot pair (01,02). -/
def frameSpin : Spin →ₗ[ℝ] V :=
  X01.comp (LinearMap.fst ℝ Octonion Octonion) +
    X02.comp (LinearMap.snd ℝ Octonion Octonion)

@[simp] theorem frameSpin_apply (u v : Octonion) :
    frameSpin (u, v) = X01 u + X02 v := rfl

/-- Exact rational coordinates (alpha,beta,slot12,(slot01,slot02)). -/
def frameCoordinates : V ≃ₗ[ℝ] FrameCoordinates where
  toFun x :=
    (-(x : Albert).d0 / 2, ((x : Albert).d1 - (x : Albert).d2) / 2,
      (x : Albert).o12, ((x : Albert).o01, (x : Albert).o02))
  invFun c :=
    ⟨⟨-2*c.1, c.1+c.2.1, c.1-c.2.1,
      c.2.2.2.1, c.2.2.2.2, c.2.2.1⟩, by
      change -2*c.1 + (c.1+c.2.1) + (c.1-c.2.1) = 0
      ring⟩
  left_inv x := by
    have ht := trace_V x
    change (x : Albert).d0 + (x : Albert).d1 + (x : Albert).d2 = 0 at ht
    apply Subtype.ext
    apply Albert.ext
    · change -2 * (-(x : Albert).d0 / 2) = (x : Albert).d0
      ring
    · change -(x : Albert).d0 / 2 +
        ((x : Albert).d1 - (x : Albert).d2) / 2 = (x : Albert).d1
      linarith
    · change -(x : Albert).d0 / 2 -
        ((x : Albert).d1 - (x : Albert).d2) / 2 = (x : Albert).d2
      linarith
    · rfl
    · rfl
    · rfl
  right_inv c := by
    rcases c with ⟨a, b, z, u, v⟩
    change (-(-2*a)/2, ((a+b)-(a-b))/2, z, (u,v)) = (a,b,z,(u,v))
    have ha : -(-2*a)/2 = a := by ring
    have hb : ((a+b)-(a-b))/2 = b := by ring
    rw [ha, hb]
  map_add' x y := by
    change (-((x : Albert).d0+(y : Albert).d0)/2,
      ((x : Albert).d1+(y : Albert).d1-((x : Albert).d2+(y : Albert).d2))/2,
      (x : Albert).o12+(y : Albert).o12,
      ((x : Albert).o01+(y : Albert).o01,(x : Albert).o02+(y : Albert).o02)) =
      (-(x : Albert).d0/2 + -(y : Albert).d0/2,
      ((x : Albert).d1-(x : Albert).d2)/2 + ((y : Albert).d1-(y : Albert).d2)/2,
      (x : Albert).o12+(y : Albert).o12,
      ((x : Albert).o01+(y : Albert).o01,(x : Albert).o02+(y : Albert).o02))
    have ha : -((x : Albert).d0+(y : Albert).d0)/2 =
        -(x : Albert).d0/2 + -(y : Albert).d0/2 := by ring
    have hb : ((x : Albert).d1+(y : Albert).d1-
        ((x : Albert).d2+(y : Albert).d2))/2 =
        ((x : Albert).d1-(x : Albert).d2)/2 +
          ((y : Albert).d1-(y : Albert).d2)/2 := by ring
    rw [ha, hb]
  map_smul' r x := by
    simp only [RingHom.id_apply]
    change (-(r*(x : Albert).d0)/2,
      (r*(x : Albert).d1-r*(x : Albert).d2)/2,
      r • (x : Albert).o12,(r • (x : Albert).o01,r • (x : Albert).o02)) =
      (r*(-(x : Albert).d0/2),r*(((x : Albert).d1-(x : Albert).d2)/2),
      r • (x : Albert).o12,(r • (x : Albert).o01,r • (x : Albert).o02))
    have ha : -(r*(x : Albert).d0)/2 = r*(-(x : Albert).d0/2) := by ring
    have hb : (r*(x : Albert).d1-r*(x : Albert).d2)/2 =
        r*(((x : Albert).d1-(x : Albert).d2)/2) := by ring
    rw [ha, hb]

def frameEmbed : FrameCoordinates →ₗ[ℝ] V := frameCoordinates.symm.toLinearMap

/-- Actual 1+1+8+16 block decomposition, rather than a spanning assumption. -/
theorem frameEmbed_eq (a b : ℝ) (z : Octonion) (s : Spin) :
    frameEmbed (a,b,z,s) = a • h 0 + b • frameD + X12 z + frameSpin s := by
  rcases s with ⟨u,v⟩
  apply Subtype.ext
  apply Albert.ext <;>
    simp [frameEmbed, frameCoordinates, h, e, unit, frameD, frameSpin,
      X01, X02, X12] <;> ring

theorem frame_decompose (x : V) :
    x = (frameCoordinates x).1 • h 0 + (frameCoordinates x).2.1 • frameD +
      X12 (frameCoordinates x).2.2.1 + frameSpin (frameCoordinates x).2.2.2 := by
  calc
    x = frameEmbed (frameCoordinates x) := (frameCoordinates.symm_apply_apply x).symm
    _ = _ := frameEmbed_eq (frameCoordinates x).1 (frameCoordinates x).2.1
      (frameCoordinates x).2.2.1 (frameCoordinates x).2.2.2

/-- Metric weights are 2 on h0, and 2/3 on d and every raw octonion slot. -/
theorem gA_frameEmbed (a b c d : ℝ) (z w : Octonion) (s t : Spin) :
    gA (frameEmbed (a,b,z,s)) (frameEmbed (c,d,w,t)) =
      2*a*c + (2/3 : ℝ) *
        (b*d + octDot z w + octDot s.1 t.1 + octDot s.2 t.2) := by
  change inner ⟨-2*a,a+b,a-b,s.1,s.2,z⟩
    ⟨-2*c,c+d,c-d,t.1,t.2,w⟩ / 3 = _
  rw [inner_coordinates]
  dsimp
  ring

end
end AlbertRecognition.FixedFrame
