import InitECandidate.Runtime.U256FromBeBodyFrame
import InitECandidate.Runtime.OriginalU256FromBeCode
import InitECandidate.Runtime.PanTailCallBodyFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Any actual call arguments are covered: malformed arguments reject, and
successful binding invokes the memory/global-preserving original converter. -/
theorem u256FromBe_tailCall_frame (arguments : List (ExpHOL 64)) :
    RuntimeFrame (.call none (ofString "u256_from_be") arguments) := by
  intro F state code
  cases args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments with
  | none => rw [evaluateHOLFiniteState_call,args]; exact ⟨rfl,rfl⟩
  | some values =>
    cases lookup : lookupCodeHOLFinite state.code.lookup (ofString "u256_from_be") values with
    | none =>
      rw [evaluateHOLFiniteState_call,args]
      dsimp only
      rw [lookup]
      exact ⟨rfl,rfl⟩
    | some installed =>
      obtain ⟨body,callee,returnShape⟩ := installed
      have installed := originalRuntimeCode_u256FromBe_lookup
      rw [← code] at installed
      have same := lookupCodeHOLFinite_installed_body state.code.lookup (ofString "u256_from_be")
        [(ofString "p",.one),(ofString "n",.one)] (sourceFunctionBody Guest.guestFn_u256_from_be)
        body (.comb [.one,.one,.one,.one]) returnShape values callee installed lookup
      have frame := u256FromBe_body_frame (callEntryStateHOLFinite state callee) code
      rw [← same] at frame
      exact evaluate_tailCall_body_frame state (ofString "u256_from_be") arguments values body callee returnShape args lookup frame

#print axioms u256FromBe_tailCall_frame
end InitECandidate.Runtime
