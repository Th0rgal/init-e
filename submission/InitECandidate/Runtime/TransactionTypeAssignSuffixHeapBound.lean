import InitECandidate.Runtime.TransactionTypeAssignSuffixBound
import InitECandidate.Runtime.TransactionTypeFieldsSuffixHeapBound
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem transaction_type_assign_suffix_heap_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer length scratch frame array input inputLength tx kind oldKind tag total : BitVec 64) (ceiling inputLimit : Nat)
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
    (typeLocal : state.locals.lookup (ofString "t") = some (.val (.word oldKind)))
    (byteLocal : state.locals.lookup (ofString "b0") = some (.val (.word kind)))
    (wholeInputBeforeArray : input.toNat + inputLength.toNat ≤ array.toNat)
    (countLocal : state.locals.lookup (ofString "nfields") = some (.val (.word (9 : BitVec 64))))
    (supported : kind = 0 ∨ kind = 1 ∨ kind = 2 ∨ kind = 3 ∨ kind = 4)
    (inputBound : inputLength.toNat ≤ inputLimit)
    (headerBefore : tx.toNat + 344 < array.toNat)
    (arrayAbove : ceiling ≤ array.toNat)
    (wholeInputBeforeFrame : input.toNat + inputLength.toNat ≤ frame.toNat)
    (topLocal : state.locals.lookup (ofString "top") = some (.rStruct [.val (.word tag),.val (.word pointer),.val (.word length),.val (.word total)]))
    (budget : transactionListSuffixCost length.toNat inputLength.toNat ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (.seq transactionTypeAssign (.seq transactionTypeFields (transactionAt 10)))
    state.clock ≤ evaluated.2.clock + transactionListSuffixCost length.toNat inputLength.toNat ∧
      evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  have assigned := evaluate_local_word_assignment state (ofString "t") (.var .local (ofString "b0")) oldKind kind typeLocal
    (by simp [evalHOLExact,byteLocal])
  let middle := setVarHOLFinite (ofString "t") (.val (.word kind)) state
  have locals : ∀ key, key ≠ ofString "t" → middle.locals.lookup key = state.locals.lookup key := by
    intro key different
    simp [middle,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
  have typeReady : middle.locals.lookup (ofString "t") = some (.val (.word kind)) := by
    simp [middle,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have bounded := transaction_type_fields_suffix_heap_bounded middle pointer length scratch frame array input inputLength tx kind tag total ceiling inputLimit
    noWrap lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena heap arrayBound countLimit heapArena
    inputBeforeFrame inputBeforeArray starts ends ((locals _ (by decide)).trans txLocal) typeReady wholeInputBeforeArray
    ((locals _ (by decide)).trans countLocal) supported inputBound headerBefore arrayAbove wholeInputBeforeFrame ((locals _ (by decide)).trans topLocal) budget
  change evaluateHOLFiniteState state transactionTypeAssign = (none,middle) at assigned
  rw [evaluateHOLFiniteState_seq_line780,assigned]
  exact bounded

#print axioms source_transaction_type_assign
#print axioms transaction_type_assign_suffix_heap_bounded
end InitECandidate.Runtime
