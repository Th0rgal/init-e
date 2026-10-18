import InitECandidate.Runtime.StoreBEBounds
import InitECandidate.Runtime.OriginalAddressFromWordsCode
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def addressFromWordsFirstArguments : List (ExpHOL 64) :=
  [.var .local (ofString "out"),.var .local (ofString "hi4")]
def addressFromWordsMiddleArguments : List (ExpHOL 64) :=
  [.op .add [.var .local (ofString "out"),.const 4],.var .local (ofString "mid8")]
def addressFromWordsLastArguments : List (ExpHOL 64) :=
  [.op .add [.var .local (ofString "out"),.const 12],.var .local (ofString "lo8")]

theorem source_addressFromWords_body : sourceFunctionBody Guest.guestFn_addr_from_words =
    .seq (.call (some (none,none)) (ofString "st_be32") addressFromWordsFirstArguments)
      (.seq (.call (some (none,none)) (ofString "st_be64") addressFromWordsMiddleArguments)
        (.seq (.call (some (none,none)) (ofString "st_be64") addressFromWordsLastArguments) (.return (.const 0)))) := by
  simp only [sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem evaluate_addressFromWords_body_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (code : state.code = originalRuntimeCode) (budget : 9 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_addr_from_words)
    state.clock ≤ evaluated.2.clock + 9 ∧ evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  rw [source_addressFromWords_body]
  apply evaluate_sequence_code_bounded state _ _ 1 8
    (evaluate_storeBE32_call_bounded state none addressFromWordsFirstArguments code (by omega)) ?_ budget
  intro next installed enough
  apply evaluate_sequence_code_bounded next _ _ 4 4
    (evaluate_storeBE64_call_bounded next none addressFromWordsMiddleArguments (installed.trans code) (by omega)) ?_ enough
  intro last lastCode lastBudget
  exact evaluate_sequence_straight_bounded last _ (.return (.const 0)) 4
    (evaluate_storeBE64_call_bounded last none addressFromWordsLastArguments (lastCode.trans (installed.trans code)) lastBudget) (by rfl)

theorem evaluate_addressFromWords_call_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (destination : Option (VarKind × MlS)) (arguments : List (ExpHOL 64))
    (code : state.code = originalRuntimeCode) (budget : 10 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (.call (some (destination,none)) (ofString "addr_from_words") arguments)
    state.clock ≤ evaluated.2.clock + 10 ∧ evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  apply evaluate_uniformCallee_call_bounded state (ofString "addr_from_words") destination arguments 9 budget
  intro values body locals returnShape found
  have same := lookupCodeHOLFinite_installed_body state.code.lookup (ofString "addr_from_words")
    [(ofString "out",.one),(ofString "hi4",.one),(ofString "mid8",.one),(ofString "lo8",.one)]
    (sourceFunctionBody Guest.guestFn_addr_from_words) body .one returnShape values locals
    (by rw [code]; exact originalRuntimeCode_addressFromWords_lookup) found
  rw [same]
  exact evaluate_addressFromWords_body_bounded (callEntryStateHOLFinite state locals) code (by change 9 ≤ state.clock - 1; omega)

#print axioms source_addressFromWords_body
#print axioms evaluate_addressFromWords_body_bounded
#print axioms evaluate_addressFromWords_call_bounded
end InitECandidate.Runtime
