import InitECandidate.Runtime.HeaderU256SuffixBound
import InitECandidate.Runtime.HeaderWordSuffixBound
import InitECandidate.Runtime.U256FromBeBodyFrame
import InitECandidate.Runtime.PanDecCallBodyFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual installed converter declaration preserves memory/globals for
any arguments and every outcome when its continuation only reads memory. -/
theorem runtimeFrame_u256_declaration (name : MlS) (shape : ShapeHOL) (arguments : List (ExpHOL 64))
    (continuation : ProgHOL 64) (tailRead : readOnlyMemory continuation = true) :
    RuntimeFrame (.decCall name shape (ofString "u256_from_be") arguments continuation) := by
  intro F state code
  cases args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments with
  | none => rw [evaluateHOLFiniteState_decCall_total,args]; exact ⟨rfl,rfl⟩
  | some values =>
    cases lookup : lookupCodeHOLFinite state.code.lookup (ofString "u256_from_be") values with
    | none =>
      rw [evaluateHOLFiniteState_decCall_total,args]
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
      exact evaluate_decCall_body_frame state name (ofString "u256_from_be") shape returnShape arguments values body
        continuation callee args lookup frame tailRead

/-- The size guard, initialization, byte loop and return preserve memory and globals at every fuel. -/
theorem header_word_suffix_frame : RuntimeFrame (headerWordAt 1) :=
  runtimeFrame_readOnly _ rfl

/-- The original size guard and conversion suffix preserve memory and globals at every fuel. -/
theorem header_u256_suffix_frame : RuntimeFrame (headerU256At 1) := by
  rw [source_header_u256_guard]
  apply runtimeFrame_seq
  · exact runtimeFrame_readOnly _ rfl
  · rw [source_header_u256_conversion]
    exact runtimeFrame_u256_declaration _ _ _ _ rfl

#print axioms runtimeFrame_u256_declaration
#print axioms header_word_suffix_frame
#print axioms header_u256_suffix_frame
end InitECandidate.Runtime
