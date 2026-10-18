import InitECandidate.Runtime.MainSszHandlerSource
import InitECandidate.Runtime.PanSequenceTerminal
import InitECandidate.Runtime.PanDecCallTerminal
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- The rejection handler cannot resume main normally: even an oracle that
returns from halt reaches the handler's explicit return. -/
theorem evaluate_mainSszHandler_terminal {F : Type} (state : PanSemStateFiniteExact 64 F) :
    (evaluateHOLFiniteState state mainSszHandler).1 ≠ none := by
  unfold mainSszHandler
  apply evaluate_decCall_terminal
  intro current
  unfold mainSszOutput
  apply evaluate_seq_terminal
  intro afterStore
  apply evaluate_seq_terminal
  intro afterOutput
  unfold mainSszHalt
  apply evaluate_seq_terminal
  intro afterHalt
  exact evaluate_return_terminal afterHalt _

#print axioms evaluate_mainSszHandler_terminal
end InitECandidate.Runtime
