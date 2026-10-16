/- Native literal endpoint propositions. No endpoint theorem is assumed. -/
module

public import Glennie.Native

@[expose] public section

namespace Glennie
noncomputable section

def SharpGramBound : Prop :=
  ∀ x y z : Albert, 23328 * phi x y z ^ 2 ≤ (gram x y z).det ^ 3

def UniversalConstant (c : ℝ) : Prop :=
  ∀ x y z : Albert, c * phi x y z ^ 2 ≤ (gram x y z).det ^ 3

def OptimalConstant : Prop := UniversalConstant 23328 ∧
  ∀ c : ℝ, UniversalConstant c → c ≤ 23328

def FrameBound : Prop := ∀ (p q r : Fin 3 → Albert),
  Frame p → Frame q → Frame r → |phi (encoder p) (encoder q) (encoder r)| ≤ 4/27

def FrameEquality : Prop := ∀ (p q r : Fin 3 → Albert),
  Frame p → Frame q → Frame r →
  (|phi (encoder p) (encoder q) (encoder r)| = 4/27 ↔ UniformLedger p q r)

def quatI : Quaternion ℝ := ⟨0,1,0,0⟩
def quatJ : Quaternion ℝ := ⟨0,0,1,0⟩
def quatK : Quaternion ℝ := ⟨0,0,0,1⟩
def octI : Octonion := (quatI,0)
def octJ : Octonion := (quatJ,0)
def octK : Octonion := (quatK,0)
def octL : Octonion := (0,1)
def octJL : Octonion := (0,quatJ)

def witnessX : Albert := ⟨-1,0,1,0,0,0⟩
def witnessY : Albert := ⟨0,0,0,octScalar 1,octI,octScalar 1⟩
def witnessZ : Albert := ⟨0,0,0,octJL,-octL,-octK⟩

end
end Glennie
