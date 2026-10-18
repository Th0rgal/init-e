import InitECandidate.Runtime.PanSequenceTerminal
import InitECandidate.Runtime.PanDecCallTerminal
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- Syntax whose final continuation returns instead of falling through. -/
def terminalTail : ProgHOL 64 → Bool
  | .dec _ _ _ body | .decCall _ _ _ _ body => terminalTail body
  | .seq _ tail => terminalTail tail
  | .return _ => true
  | _ => false

theorem evaluate_terminalTail {F : Type} (program : ProgHOL 64)
    (supported : terminalTail program = true) (state : PanSemStateFiniteExact 64 F) :
    (evaluateHOLFiniteState state program).1 ≠ none := by
  cases shape : program with
  | dec name kind initializer body =>
    have child : terminalTail body = true := by simpa only [shape,terminalTail] using supported
    rw [evaluateHOLFiniteState_dec_total]
    dsimp only
    split
    · simp
    · rename_i value initialized
      split
      · have terminal := evaluate_terminalTail body child (setVarHOLFinite name value state)
        cases run : evaluateHOLFiniteState (setVarHOLFinite name value state) body with
        | mk result post =>
          rw [run] at terminal
          exact terminal
      · simp
  | decCall name kind function arguments body =>
    have child : terminalTail body = true := by simpa only [shape,terminalTail] using supported
    exact evaluate_decCall_terminal state name function kind arguments body (fun current => evaluate_terminalTail body child current)
  | seq first tail =>
    have child : terminalTail tail = true := by simpa only [shape,terminalTail] using supported
    exact evaluate_seq_terminal state first tail (fun current => evaluate_terminalTail tail child current)
  | «return» expression => exact evaluate_return_terminal state expression
  | _ => simp [shape,terminalTail] at supported
termination_by sizeOf program

#print axioms evaluate_terminalTail
end InitECandidate.Runtime
