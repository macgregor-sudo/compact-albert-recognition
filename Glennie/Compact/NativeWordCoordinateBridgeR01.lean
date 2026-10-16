/- Explicit ordered full-coordinate dictionary for the native word table. -/
module
public import AlbertGeometry.NativeOperatorTrace
public import Glennie.Native.Statements
public import Mathlib.Tactic.FinCases

@[expose] public section
namespace Glennie.Compact.NativeWordTableR01
noncomputable section
open Glennie AlbertGeometry.NativeOperatorTrace
open scoped BigOperators Matrix
set_option autoImplicit false

inductive Word where
  | unit : Word
  | mark : Fin 3 → Word
  | mul : Word → Word → Word

def eval {E : Type*} (e : E) (a : Fin 3 → E) (j : E → E → E) : Word → E
  | .unit => e
  | .mark i => a i
  | .mul u v => j (eval e a j u) (eval e a j v)

def marks : Fin 3 → Albert := ![witnessX,witnessY,witnessZ]
def nativeEval : Word → Albert := eval 1 marks jordan

def fullSlot : Fin 27 → FullIndex := ![Sum.inl 0, Sum.inl 1, Sum.inl 2, Sum.inr (0,0), Sum.inr (0,1), Sum.inr (0,2), Sum.inr (0,3), Sum.inr (0,4), Sum.inr (0,5), Sum.inr (0,6), Sum.inr (0,7), Sum.inr (1,0), Sum.inr (1,1), Sum.inr (1,2), Sum.inr (1,3), Sum.inr (1,4), Sum.inr (1,5), Sum.inr (1,6), Sum.inr (1,7), Sum.inr (2,0), Sum.inr (2,1), Sum.inr (2,2), Sum.inr (2,3), Sum.inr (2,4), Sum.inr (2,5), Sum.inr (2,6), Sum.inr (2,7)]

def unflatten (c : Fin 27 → ℝ) : FullIndex → ℝ
  | .inl j => ![c 0,c 1,c 2] j
  | .inr (s,t) =>
    (![![c 3, c 4, c 5, c 6, c 7, c 8, c 9, c 10],
       ![c 11, c 12, c 13, c 14, c 15, c 16, c 17, c 18],
       ![c 19, c 20, c 21, c 22, c 23, c 24, c 25, c 26]] : Fin 3 → Fin 8 → ℝ) s t

def encode (x : Albert) : Fin 27 → ℝ := fun i => fullCoordinates x (fullSlot i)
def decode (c : Fin 27 → ℝ) : Albert := fullCoordinates.symm (unflatten c)

theorem encode_decode (c : Fin 27 → ℝ) : encode (decode c) = c := by
  funext i
  change fullCoordinates (fullCoordinates.symm (unflatten c)) (fullSlot i) = c i
  rw [LinearEquiv.apply_symm_apply]
  fin_cases i <;> rfl

theorem decode_encode (x : Albert) : decode (encode x) = x := by
  apply fullCoordinates.injective
  change fullCoordinates (fullCoordinates.symm (unflatten (encode x))) = fullCoordinates x
  rw [LinearEquiv.apply_symm_apply]
  funext i
  rcases i with j | ⟨s,t⟩
  · fin_cases j <;> rfl
  · fin_cases s <;> fin_cases t <;> rfl

def flatCoordinates : Albert ≃ₗ[ℝ] (Fin 27 → ℝ) where
  toFun := encode
  invFun := decode
  left_inv := decode_encode
  right_inv := encode_decode
  map_add' x y := by
    funext i
    change fullCoordinates (x+y) (fullSlot i) =
      fullCoordinates x (fullSlot i) + fullCoordinates y (fullSlot i)
    rw [map_add]
    rfl
  map_smul' r x := by
    funext i
    change fullCoordinates (r • x) (fullSlot i) =
      (RingHom.id ℝ) r • fullCoordinates x (fullSlot i)
    rw [map_smul]
    rfl

end
end Glennie.Compact.NativeWordTableR01
