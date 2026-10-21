import InitECandidate.Runtime.StackWeightedControl
import InitECandidate.Runtime.StackWeightedBlock
import Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenCorrect.If
namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.StackToLab.Proofs.CodeInstalled
open Flapjack.Compiler.Backend.StackToLab.Proofs.StateRel
open Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenHelpers
open Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenCorrect
open Flapjack.Compiler.Backend.StackToLab.Proofs

/-- The actually taken conditional transfer costs at most three native steps. -/
theorem branch_taken_update_weighted {F : Type}
    (start : LabSem.State 64 Flapjack.Compiler.Backend.LabToTarget.Config F)
    (encoded : LabProgHOL 64) (cmp : HolCmp) (reg : Nat) (operand : HolRegImm 64)
    (label : Lab) (pc : Nat)
    (fetch : asmFetchAux start.pc start.code = some (.labAsm (.jumpCmp cmp reg operand label) 0 [] 0))
    (chosen : wordSemWordCmp cmp (start.regs reg) (regImm operand start) = some true)
    (destination : getPcValue label start = some pc) :
    LabToTarget.WeightedInstructionTrace encoded { start with clock := start.clock + 1 }
      (updPc pc start) 3 := by
  have successor : updPc pc (decClock { start with clock := start.clock + 1 }) = updPc pc start := by
    simp only [decClock, updPc, Nat.add_sub_cancel]
  have step := LabToTarget.WeightedInstructionTrace.branchTaken (code := encoded)
    { start with clock := start.clock + 1 } (updPc pc start) cmp reg operand label pc 0 [] 0 0
    (by simp) (by simpa only [asmFetch] using fetch)
    (by simpa only [LabProps.regImmWithClock] using chosen) destination
    (by rw [successor]; exact .nil _)
  simpa only [Nat.zero_add] using step

/-- Fall-through pays the actual visited branch expansion and padding. -/
theorem branch_fallthrough_update_weighted {F : Type}
    (start : LabSem.State 64 Flapjack.Compiler.Backend.LabToTarget.Config F)
    (encoded : LabProgHOL 64) (cmp : HolCmp) (reg : Nat) (operand : HolRegImm 64)
    (label : Lab)
    (fetch : asmFetchAux start.pc start.code = some (.labAsm (.jumpCmp cmp reg operand label) 0 [] 0))
    (chosen : wordSemWordCmp cmp (start.regs reg) (regImm operand start) = some false) :
    LabToTarget.WeightedInstructionTrace encoded { start with clock := start.clock + 1 }
      (incPc start) (LabToTarget.controlWork 3 encoded start.pc) := by
  have successor : incPc (decClock { start with clock := start.clock + 1 }) = incPc start := by
    simp only [decClock, incPc, Nat.add_sub_cancel]
  have step := LabToTarget.WeightedInstructionTrace.branchFallthrough (code := encoded)
    { start with clock := start.clock + 1 } (incPc start) cmp reg operand label 0 [] 0 0
    (by simp) (by simpa only [asmFetch] using fetch)
    (by simpa only [LabProps.regImmWithClock] using chosen)
    (by rw [successor]; exact .nil _)
  simpa only [Nat.zero_add] using step

private theorem branch_appAppend {α : Type} (a b : AppList α) :
    appListAppend (.append a b) = appListAppend a ++ appListAppend b := (appListAppend_thm a b []).1
private theorem branch_appList {α : Type} (lines : List α) :
    appListAppend (.list lines) = lines := (appListAppend_thm .nil .nil lines).2.1

/-- A normal instruction arm has no internal labels, does not return, and
leaves the compiler label counter untouched. -/
theorem flatten_instructionBlock_metadata (instructions : List (HolInst 64))
    (sectionId labelId : Nat) (continues breaks : List Nat) :
    let compiled := Flapjack.Compiler.Backend.StackToLab.flattenHOL false
      (instructionBlock instructions) sectionId labelId continues breaks
    compiled.2.1 = false ∧ compiled.2.2 = labelId ∧
      appListAppend compiled.1 = instructions.map (fun i => (.asm (.asmi (.inst i)) [] 0 : LabLineHOL 64)) := by
  induction instructions with
  | nil => simp only [instructionBlock, List.foldr_nil,
      Flapjack.Compiler.Backend.StackToLab.flattenHOL, branch_appList, List.map_nil, and_self]
  | cons instruction rest ih =>
    change let compiled := (Flapjack.Compiler.Backend.StackToLab.flattenHOL false
        ((Prog.inst instruction).seq (instructionBlock rest)) sectionId labelId continues breaks)
      compiled.2.1 = false ∧ compiled.2.2 = labelId ∧ appListAppend compiled.1 =
        (instruction :: rest).map (fun i => (.asm (.asmi (.inst i)) [] 0 : LabLineHOL 64))
    simp only [Flapjack.Compiler.Backend.StackToLab.flattenHOL,
      Bool.false_eq_true, ↓reduceIte, Bool.false_or, branch_appAppend, branch_appList,
      ih.1, ih.2.1, ih.2.2, List.map_cons, List.singleton_append, and_self]

/-- The actual conditional compiler layout for two nonempty ordinary arms.
Only the chosen arm will execute; the other arm contributes no dynamic work. -/
theorem flatten_instructionBlock_if_lines (yes no : List (HolInst 64))
    (yesNonempty : yes ≠ []) (noNonempty : no ≠ [])
    (cmp : HolCmp) (reg : Nat) (operand : HolRegImm 64) (flag : Bool)
    (sectionId labelId : Nat) (continues breaks : List Nat) :
    appListAppend (Flapjack.Compiler.Backend.StackToLab.flattenHOL flag
      (.ite cmp reg operand (instructionBlock yes) (instructionBlock no))
      sectionId labelId continues breaks).1 =
      .labAsm (.jumpCmp cmp reg operand (.lab sectionId labelId)) 0 [] 0 ::
        (no.map (fun i => (.asm (.asmi (.inst i)) [] 0 : LabLineHOL 64)) ++
          (.labAsm (.jump (.lab sectionId (labelId + 1))) 0 [] 0 :: .label sectionId labelId 0 ::
            (yes.map (fun i => (.asm (.asmi (.inst i)) [] 0 : LabLineHOL 64)) ++
              [.label sectionId (labelId + 1) 0]))) := by
  have yesSkip : Flapjack.Compiler.Backend.StackToLab.stackIsSkip (instructionBlock yes) = false := by
    cases yes with
    | nil => exact False.elim (yesNonempty rfl)
    | cons instruction rest => rfl
  have noSkip : Flapjack.Compiler.Backend.StackToLab.stackIsSkip (instructionBlock no) = false := by
    cases no with
    | nil => exact False.elim (noNonempty rfl)
    | cons instruction rest => rfl
  have yesMeta := flatten_instructionBlock_metadata yes sectionId labelId continues breaks
  have noMeta := flatten_instructionBlock_metadata no sectionId labelId continues breaks
  rw [Flapjack.Compiler.Backend.StackToLab.flattenHOL]
  simp only [yesSkip, noSkip, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
    yesMeta.1, yesMeta.2.1, noMeta.1, noMeta.2.1,
    branch_appAppend, branch_appList, yesMeta.2.2, noMeta.2.2,
    List.singleton_append, List.cons_append, List.append_nil, List.append_assoc, List.nil_append]

#print axioms flatten_instructionBlock_if_lines
#print axioms branch_taken_update_weighted
#print axioms branch_fallthrough_update_weighted
#print axioms flatten_instructionBlock_metadata
end InitECandidate.Runtime.StackToLab
