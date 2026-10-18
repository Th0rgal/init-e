import InitECandidate.Runtime.TransactionToSource
import InitECandidate.Runtime.TxFixedBytesLocalCallValue
import InitECandidate.Runtime.TxToItemLocalCallValue
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem transaction_to_branch_word {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (array index : BitVec 64)
    (arrayLocal : state.locals.lookup (ofString "arr") = some (.val (.word array)))
    (indexLocal : state.locals.lookup (ofString "k") = some (.val (.word index)))
    (code : state.code = originalRuntimeCode)
    (run : evaluateHOLFiniteState state transactionToBranch = (none,post)) :
    ∃ word : BitVec 64, post.locals.lookup (ofString "w") = some (.val (.word word)) := by
  have fixedArgs : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [.var .local (ofString "arr"),.var .local (ofString "k"),.const 20] =
      some [.val (.word array),.val (.word index),.val (.word (20 : BitVec 64))] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,arrayLocal,indexLocal]
  have optionalArgs : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [.var .local (ofString "arr"),.var .local (ofString "k")] = some [.val (.word array),.val (.word index)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,arrayLocal,indexLocal]
  unfold transactionToBranch at run
  rw [evaluateHOLFiniteState_ite] at run
  split at run
  · split at run
    · exact txToItem_local_call_value state post (ofString "w") _ array index optionalArgs code run
    · exact txFixedBytes_local_call_value state post (ofString "w") _ array index 20 fixedArgs code run
  · cases run

#print axioms transaction_to_branch_word
end InitECandidate.Runtime
