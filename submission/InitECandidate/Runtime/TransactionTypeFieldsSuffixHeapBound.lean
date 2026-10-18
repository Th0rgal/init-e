import InitECandidate.Runtime.TransactionTypeStoreSuffixHeapBound
import InitECandidate.Runtime.TransactionTypeFieldsFrame
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem transaction_type_fields_suffix_heap_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer length scratch frame array input inputLength tx kind tag total : BitVec 64) (ceiling inputLimit : Nat)
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
    (inputBeforeFrame : pointer.toNat + length.toNat ≤ frame.toNat ∨ (ceiling % 8 = 0 ∧ ceiling ≤ pointer.toNat))
    (inputBeforeArray : pointer.toNat + length.toNat ≤ array.toNat)
    (starts : input.toNat ≤ pointer.toNat)
    (ends : pointer.toNat + length.toNat ≤ input.toNat + inputLength.toNat)
    (txLocal : state.locals.lookup (ofString "tx") = some (.val (.word tx)))
    (typeLocal : state.locals.lookup (ofString "t") = some (.val (.word kind)))
    (wholeInputBeforeArray : input.toNat + inputLength.toNat ≤ array.toNat)
    (countLocal : state.locals.lookup (ofString "nfields") = some (.val (.word (9 : BitVec 64))))
    (supported : kind = 0 ∨ kind = 1 ∨ kind = 2 ∨ kind = 3 ∨ kind = 4)
    (inputBound : inputLength.toNat ≤ inputLimit)
    (headerBefore : tx.toNat + 344 < array.toNat)
    (arrayAbove : ceiling ≤ array.toNat)
    (wholeInputBeforeFrame : input.toNat + inputLength.toNat ≤ frame.toNat ∨ (ceiling % 8 = 0 ∧ ceiling ≤ input.toNat))
    (topLocal : state.locals.lookup (ofString "top") = some (.rStruct [.val (.word tag),.val (.word pointer),.val (.word length),.val (.word total)]))
    (budget : transactionListSuffixCost length.toNat inputLength.toNat ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (.seq transactionTypeFields (transactionAt 10))
    state.clock ≤ evaluated.2.clock + transactionListSuffixCost length.toNat inputLength.toNat ∧
      evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  have result := transaction_type_fields_result state kind supported typeLocal countLocal
  have frameKept := transaction_type_fields_frame state
  have metadata := evaluateHOLFiniteState_metadata state transactionTypeFields
  rw [evaluateHOLFiniteState_seq_line780]
  cases ran : evaluateHOLFiniteState state transactionTypeFields with
  | mk outcome post =>
    rw [ran] at result frameKept metadata
    dsimp only at result frameKept metadata
    have normal : outcome = none := result.1
    subst outcome
    dsimp only
    have locals := frameKept.2.2
    have globals := frameKept.2.1
    have bounded := transaction_type_store_suffix_heap_bounded post pointer length scratch frame array input inputLength tx kind
      (BitVec.ofNat 64 (transactionRequiredFields kind)) tag total ceiling inputLimit
      noWrap lengthBound limitBound ((globals _).trans scratchGlobal) ((globals _).trans frameGlobal) (metadata.1.trans code)
      orderedFrame framePositive scratchBelow
      (by intro address low high; rw [metadata.2.1]; exact arena address low high)
      ((globals _).trans heap) arrayBound countLimit
      (by intro address low high; rw [metadata.2.1]; exact heapArena address low high)
      inputBeforeFrame inputBeforeArray starts ends ((locals _ (by decide)).trans txLocal) ((locals _ (by decide)).trans typeLocal)
      wholeInputBeforeArray result.2.2 (by rw [transaction_required_fields_word]) inputBound headerBefore arrayAbove wholeInputBeforeFrame
      ((locals _ (by decide)).trans topLocal) (by rw [result.2.1]; exact budget)
    exact ⟨by have spent := bounded.1; omega,by have remaining := bounded.2.1; omega,bounded.2.2⟩

#print axioms transaction_type_fields_suffix_heap_bounded
end InitECandidate.Runtime
