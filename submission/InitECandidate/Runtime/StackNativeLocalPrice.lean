import InitECandidate.Runtime.StackExecutionRiscV
import Flapjack.Compiler.Backend.LabToTarget.PositionOrder
namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Encoders.Asm

def positionPrefixMax (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => max (positionPrefixMax f n) (f n)

theorem positionPrefixMax_bound (f : Nat → Nat) (n i : Nat) (inside : i < n) :
    f i ≤ positionPrefixMax f n := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [positionPrefixMax]
    by_cases eq : i = n
    · subst i; exact Nat.le_max_right _ _
    · exact (ih (by omega)).trans (Nat.le_max_left _ _)

/-- Maximum local encoded position gap, in instruction words. This is a
maximum over line gaps, never a sum over the program's ROM bytes. -/
def encodedLineWords (code : LabProgHOL 64) : Nat :=
  positionPrefixMax (fun pc => (posVal (pc + 1) 0 code - posVal pc 0 code) / 4) (numPcs code)

theorem encodedLineWords_bound (code : LabProgHOL 64) (pc : Nat) :
    (posVal (pc + 1) 0 code - posVal pc 0 code) / 4 ≤ encodedLineWords code := by
  by_cases inside : pc < numPcs code
  · exact positionPrefixMax_bound (fun j => (posVal (j + 1) 0 code - posVal j 0 code) / 4) _ _ inside
  · have h0 := posVal_geNumPcs pc 0 code (by omega)
    have h1 := posVal_geNumPcs (pc + 1) 0 code (by omega)
    rw [← h0, ← h1, Nat.sub_self, Nat.zero_div]
    exact Nat.zero_le _

noncomputable def nativeLocalPrice {F : Type} : ExecutionLocalPrice F := fun p _ code =>
  match p with
  | .inst instruction => instLocalCost instruction + encodedLineWords code
  | .tick => instLocalCost .skip + encodedLineWords code
  | .locValue _ _ _ => 2 + encodedLineWords code
  | .break _ => 2
  | .ret _ | .raise _ | .shMemOp _ _ _ => 1
  | .ffi _ _ _ _ _ _ => 19 + encodedLineWords code
  | .ite _ _ _ _ _ => 5 + encodedLineWords code
  | .loop _ => 2
  | .call none dest _ => callJumpWork dest
  | .call (some _) dest _ => 4 + encodedLineWords code + callJumpWork dest
  | .rawCall _ => 2
  | .jumpLower _ _ _ => 3 + encodedLineWords code
  | _ => 0

theorem nativeLocalPrice_caps {F : Type} : LocalNativeCaps (nativeLocalPrice (F := F)) := by
  constructor
  · intro source instruction encoded pc
    have h := encodedLineWords_bound encoded pc
    have sub : (posVal (pc + 1) 0 encoded - posVal pc 0 encoded -
        (Flapjack.Compiler.Encoders.RiscV.Target.riscvTarget.config.encode (.inst instruction)).length) / 4 ≤
        (posVal (pc + 1) 0 encoded - posVal pc 0 encoded) / 4 := Nat.div_le_div_right (Nat.sub_le _ _)
    simp only [LabToTarget.LocalCost.instructionWork, nativeLocalPrice]
    omega
  · intro source reg sid lid encoded pc
    have h := encodedLineWords_bound encoded pc
    simpa only [nativeLocalPrice, LabToTarget.controlWork] using Nat.add_le_add_left h 2
  · intro source encoded pc
    have h := encodedLineWords_bound encoded pc
    have sub : (posVal (pc + 1) 0 encoded - posVal pc 0 encoded -
        (Flapjack.Compiler.Encoders.RiscV.Target.riscvTarget.config.encode (.inst .skip)).length) / 4 ≤
        (posVal (pc + 1) 0 encoded - posVal pc 0 encoded) / 4 := Nat.div_le_div_right (Nat.sub_le _ _)
    simp only [LabToTarget.LocalCost.instructionWork, nativeLocalPrice]
    omega
  · intros; exact Nat.le_refl _
  · intros; exact Nat.le_refl _
  · intros; exact Nat.le_refl _
  · intro source name ptr len ptr2 len2 ret encoded pc
    have h := encodedLineWords_bound encoded pc
    simp only [nativeLocalPrice, LabToTarget.controlWork]
    omega
  · intros; exact Nat.le_refl _
  · intro source cmp reg operand yes no encoded pc
    have h := encodedLineWords_bound encoded pc
    simp only [nativeLocalPrice, LabToTarget.controlWork]
    omega
  · intros; exact Nat.le_refl _
  · intros; exact Nat.le_refl _
  · intros; exact Nat.le_refl _
  · intro source rp link l1 l2 dest handler encoded pc
    have h := encodedLineWords_bound encoded pc
    simp only [nativeLocalPrice, LabToTarget.controlWork]
    omega
  · intro source regX regY dest encoded pc
    have h := encodedLineWords_bound encoded pc
    simpa only [nativeLocalPrice, LabToTarget.controlWork] using Nat.add_le_add_left h 3

#print axioms encodedLineWords_bound
#print axioms nativeLocalPrice_caps
end InitECandidate.Runtime.StackToLab
