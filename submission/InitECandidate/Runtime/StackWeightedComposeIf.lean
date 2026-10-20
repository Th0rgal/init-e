import InitECandidate.Runtime.StackWeightedCompose
import InitECandidate.Runtime.StackWeightedIf
namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem

/-- Actual reached condition operands ground the compositional motive for the
compiler's two-arm layout. The unselected arm contributes layout length only,
not runtime work. -/
theorem normalWeightedFlatten_instructionBlockIf {F : Type}
    (yes no : List (HolInst 64)) (yesNonempty : yes ≠ []) (noNonempty : no ≠ [])
    (cmp : HolCmp) (reg : Nat) (operand : HolRegImm 64)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (x y : WordLocW 64) (chosen : Bool)
    (lhs : StackSemStateOps.getVar reg source = some x)
    (rhs : StackSemStateOps.getVarImm (HolRegImm.toWordRegImm operand) source = some y)
    (condition : wordSemWordCmp cmp x y = some chosen) :
    NormalWeightedFlatten (.ite cmp reg operand (instructionBlock yes) (instructionBlock no)) source
      (fun encoded pc => instructionBlockIfWork encoded pc yes no chosen) := by
  intro flag post sectionId labelId continues breaks start encoded hyps
  obtain ⟨final, related, pc, code, trace⟩ := flatten_instructionBlock_if_weighted
    yes no yesNonempty noNonempty cmp reg operand source post flag sectionId labelId continues breaks
    start encoded hyps x y chosen lhs rhs condition
  have filteredOrdinary (instructions : List (HolInst 64)) :
      ((instructions.map (fun i => (.asm (.asmi (.inst i)) [] 0 : LabLineHOL 64))).filter
        (fun line => !isLabelHOL line)).length = instructions.length := by
    induction instructions with
    | nil => rfl
    | cons instruction rest ih => simpa [isLabelHOL] using ih
  refine ⟨final, instructionBlockIfClock yes no chosen,
    instructionBlockIfWork encoded start.pc yes no chosen, related, ?_, code, Nat.le_refl _, trace.toMixed⟩
  rw [flatten_instructionBlock_if_lines yes no yesNonempty noNonempty]
  simp only [List.filter_cons, isLabelHOL, Bool.not_false, Bool.not_true,
    ↓reduceIte, List.filter_append, List.length_cons, List.length_append,
    List.filter_nil, List.length_nil, Nat.add_zero, Bool.false_eq_true, filteredOrdinary]
  have yesLength := filteredOrdinary yes
  have noLength := filteredOrdinary no
  simp only [isLabelHOL] at yesLength noLength
  omega

#print axioms normalWeightedFlatten_instructionBlockIf
end InitECandidate.Runtime.StackToLab
