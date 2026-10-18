import InitECandidate.Runtime.TerminalScopeSyntax
import InitECandidate.Runtime.OriginalRuntimeCode
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

theorem transactionRlp_terminal_syntax : terminalScopeSyntax (sourceFunctionBody Guest.guestFn_decode_transaction_rlp) = true := by
  simp only [sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- Original transaction RLP decoding always ends in a return or terminal failure. -/
theorem evaluate_transactionRlp_terminal {F : Type} (state : PanSemStateFiniteExact 64 F) :
    (evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_decode_transaction_rlp)).1 ≠ none :=
  evaluate_terminalScopeSyntax _ transactionRlp_terminal_syntax state

#print axioms evaluate_transactionRlp_terminal
end InitECandidate.Runtime
