import InitECandidate.Runtime.FrameHalt
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Opcode comparisons only select a branch; they cannot mutate the state. -/
theorem evaluate_opcode_ite {F : Type} (state : PanSemStateFiniteExact 64 F)
    (opcode : BitVec 64) (value : state.locals.lookup (ofString "op") = some (.val (.word opcode)))
    (operator : Cmp) (bound : BitVec 64) (yes no : ProgHOL 64) :
    evaluateHOLFiniteState state (.ite (.cmp operator (.var .local (ofString "op")) (.const bound)) yes no) =
      if Compiler.Encoders.Asm.wordCmpHOL operator opcode bound then
        evaluateHOLFiniteState state yes else evaluateHOLFiniteState state no := by
  classical
  cases flag : Compiler.Encoders.Asm.wordCmpHOL operator opcode bound <;>
    simp [evaluateHOLFiniteState_ite,evalHOLExact,toExact,value,flag]

#print axioms evaluate_opcode_ite
end InitECandidate.Runtime
