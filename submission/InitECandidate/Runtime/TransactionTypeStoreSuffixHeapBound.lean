import InitECandidate.Runtime.TransactionTypeStoreSuffixBound
import InitECandidate.Runtime.TransactionTopGuardSuffixHeapBound
import InitECandidate.Runtime.StraightLocalFrame
import InitECandidate.Runtime.NamedGlobalFrame
import InitECandidate.Runtime.StraightLineNoTimeout
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem transaction_type_store_suffix_heap_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer length scratch frame array input inputLength tx kind expected tag total : BitVec 64) (ceiling inputLimit : Nat)
    (noWrap : pointer.toNat + length.toNat < 2^64) (lengthBound : length.toNat ≤ inputLimit)
    (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word array)))
    (arrayBound : array.toNat ≤ 33806089496) (countLimit : inputLimit * 120 < 2^64)
    (heapArena : ∀ address : BitVec 64, array.toNat ≤ address.toNat → address.toNat < 33806089496 → state.memaddrs address)
    (inputBeforeFrame : pointer.toNat + length.toNat ≤ frame.toNat)
    (inputBeforeArray : pointer.toNat + length.toNat ≤ array.toNat)
    (starts : input.toNat ≤ pointer.toNat)
    (ends : pointer.toNat + length.toNat ≤ input.toNat + inputLength.toNat)
    (txLocal : state.locals.lookup (ofString "tx") = some (.val (.word tx)))
    (typeLocal : state.locals.lookup (ofString "t") = some (.val (.word kind)))
    (wholeInputBeforeArray : input.toNat + inputLength.toNat ≤ array.toNat)
    (expectedLocal : state.locals.lookup (ofString "nfields") = some (.val (.word expected)))
    (fields : transactionRequiredFields kind ≤ expected.toNat)
    (inputBound : inputLength.toNat ≤ inputLimit)
    (headerBefore : tx.toNat + 344 < array.toNat)
    (arrayAbove : ceiling ≤ array.toNat)
    (wholeInputBeforeFrame : input.toNat + inputLength.toNat ≤ frame.toNat)
    (topLocal : state.locals.lookup (ofString "top") = some (.rStruct [.val (.word tag),.val (.word pointer),.val (.word length),.val (.word total)]))
    (budget : transactionListSuffixCost length.toNat inputLength.toNat ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (transactionAt 10)
    state.clock ≤ evaluated.2.clock + transactionListSuffixCost length.toNat inputLength.toNat ∧
      evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  have clock := clockPreserving_of_straightLine transactionTypeStore (by rfl) state
  have noTimeout := evaluate_straightLine_no_timeout transactionTypeStore (by rfl) state
  have locals : ∀ key, (evaluateHOLFiniteState state transactionTypeStore).2.locals.lookup key = state.locals.lookup key :=
    fun key => evaluate_straight_local_frame key transactionTypeStore (by rfl) state
  have globals : ∀ key, (evaluateHOLFiniteState state transactionTypeStore).2.globals.lookup key = state.globals.lookup key :=
    fun key => evaluate_avoidsGlobalAssignment key transactionTypeStore (by rfl) state
  have metadata := evaluateHOLFiniteState_metadata state transactionTypeStore
  rw [source_transaction_type_store,evaluateHOLFiniteState_seq_line780]
  cases stored : evaluateHOLFiniteState state transactionTypeStore with
  | mk result post =>
    rw [stored] at clock noTimeout locals globals metadata
    dsimp only at clock noTimeout locals globals metadata
    cases result with
    | some result =>
      dsimp only
      exact ⟨by omega,by omega,noTimeout⟩
    | none =>
      dsimp only
      have bounded := transaction_top_guard_suffix_heap_bounded post pointer length scratch frame array input inputLength tx kind expected tag total ceiling inputLimit
        noWrap lengthBound limitBound ((globals _).trans scratchGlobal) ((globals _).trans frameGlobal) (metadata.1.trans code)
        orderedFrame framePositive scratchBelow
        (by intro address low high; rw [metadata.2.1]; exact arena address low high)
        ((globals _).trans heap) arrayBound countLimit
        (by intro address low high; rw [metadata.2.1]; exact heapArena address low high)
        inputBeforeFrame inputBeforeArray starts ends ((locals _).trans txLocal) ((locals _).trans typeLocal) wholeInputBeforeArray
        ((locals _).trans expectedLocal) fields inputBound headerBefore arrayAbove wholeInputBeforeFrame ((locals _).trans topLocal) (by rw [clock]; exact budget)
      exact ⟨by have spent := bounded.1; omega,by have remaining := bounded.2.1; omega,bounded.2.2⟩

#print axioms source_transaction_type_store
#print axioms transaction_type_store_suffix_heap_bounded
end InitECandidate.Runtime
