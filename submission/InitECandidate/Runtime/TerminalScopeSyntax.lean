import InitECandidate.Runtime.PanSequenceTerminal
import InitECandidate.Runtime.PanDecCallTerminal
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- Syntactic certificate that every path reaching the end has a terminal tail. -/
def terminalScopeSyntax : ProgHOL 64 → Bool
  | .return _ => true
  | .seq _ tail => terminalScopeSyntax tail
  | .dec _ _ _ body => terminalScopeSyntax body
  | .decCall _ _ _ _ tail => terminalScopeSyntax tail
  | .ite _ yes no => terminalScopeSyntax yes && terminalScopeSyntax no
  | _ => false

theorem evaluate_terminalScopeSyntax {F : Type} (program : ProgHOL 64)
    (supported : terminalScopeSyntax program = true) (state : PanSemStateFiniteExact 64 F) :
    (evaluateHOLFiniteState state program).1 ≠ none := by
  cases program with
  | «return» expression => exact evaluate_return_terminal state expression
  | seq first tail =>
    exact evaluate_seq_terminal state first tail (fun current => evaluate_terminalScopeSyntax tail supported current)
  | dec name shape initializer body =>
    rw [evaluateHOLFiniteState_dec_total]
    dsimp only
    split
    · simp
    · split
      · exact evaluate_terminalScopeSyntax body supported _
      · simp
  | decCall name shape function arguments tail =>
    exact evaluate_decCall_terminal state name function shape arguments tail
      (fun current => evaluate_terminalScopeSyntax tail supported current)
  | ite condition yes no =>
    have children : terminalScopeSyntax yes = true ∧ terminalScopeSyntax no = true := by
      simpa only [terminalScopeSyntax,Bool.and_eq_true] using supported
    rw [evaluateHOLFiniteState_ite]
    split
    · split
      · exact evaluate_terminalScopeSyntax no children.2 state
      · exact evaluate_terminalScopeSyntax yes children.1 state
    · simp
  | _ => simp [terminalScopeSyntax] at supported
termination_by sizeOf program

#print axioms evaluate_terminalScopeSyntax
end InitECandidate.Runtime
