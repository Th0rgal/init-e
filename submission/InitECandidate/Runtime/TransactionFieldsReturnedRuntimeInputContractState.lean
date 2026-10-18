import InitECandidate.Runtime.TransactionListReturnedRuntimeInputContractState
import InitECandidate.Runtime.TransactionTypeHeaderReturnedPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem transaction_fields_returned_runtime_input_contract_state {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (tag pointer length total scratch frame array tx kind : BitVec 64) (ceiling inputLimit : Nat)
    (topLocal : state.locals.lookup (ofString "top") = some
      (.rStruct [.val (.word tag),.val (.word pointer),.val (.word length),.val (.word total)]))
    (noWrap : pointer.toNat + length.toNat < 2^64) (lengthBound : length.toNat ≤ inputLimit)
    (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word array)))
    (arrayBound : array.toNat ≤ 33806089496) (countLimit : inputLimit * 16 < 2^64)
    (heapArena : ∀ address : BitVec 64, array.toNat ≤ address.toNat → address.toNat < 33806089496 → state.memaddrs address)
    (budget : length.toNat * ((2 * length.toNat + 1) * 15 + 19) + length.toNat * 12 + 4 ≤ state.clock)
    (older olderCount input inputLength : BitVec 64)
    (valid : RlpSliceInputPrefix state older input inputLength olderCount.toNat)
    (before : older.toNat + olderCount.toNat * 16 ≤ array.toNat)
    (arrayBeforeFrame : array.toNat ≤ frame.toNat)
    (txLocal : state.locals.lookup (ofString "tx") = some (.val (.word tx)))
    (typeLocal : state.locals.lookup (ofString "t") = some (.val (.word kind)))
    (beforeTx : older.toNat + olderCount.toNat * 16 ≤ tx.toNat)
    (inputBeforeFrame : pointer.toNat + length.toNat ≤ frame.toNat)
    (inputBeforeArray : pointer.toNat + length.toNat ≤ array.toNat)
    (finalValue : ValueHOL 64)
    (run : evaluateHOLFiniteState state (transactionAt 10) = (some (.returned finalValue),post)) :
    ∃ (count : BitVec 64) (entry output : PanSemStateFiniteExact 64 F),
      count.toNat ≤ length.toNat ∧ RlpSliceInputPrefix entry array pointer length count.toNat ∧
      RlpSliceInputPrefix entry older input inputLength olderCount.toNat ∧
      entry.locals.lookup (ofString "lst") = some (.rStruct [.val (.word array),.val (.word count)]) ∧
      (∀ name, name ≠ ofString "lst" → entry.locals.lookup name = state.locals.lookup name) ∧
      entry.globals.lookup (ofString "heap_ptr") = some (.val (.word (allocationEnd array (count * 16)))) ∧
      entry.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)) ∧
      entry.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)) ∧
      entry.code = state.code ∧ entry.memaddrs = state.memaddrs ∧
      state.clock ≤ entry.clock + (length.toNat * ((2 * length.toNat + 1) * 15 + 19) + length.toNat * 12 + 4) ∧
      entry.clock ≤ state.clock ∧
      array.toNat + count.toNat * 16 ≤ (allocationEnd array (count * 16)).toNat ∧
      (allocationEnd array (count * 16)).toNat ≤ 33806089496 ∧
      (allocationEnd array (count * 16)).toNat % 8 = 0 ∧
      evaluateHOLFiniteState entry (transactionAt 13) = (some (.returned finalValue),output) ∧ (post.memory = output.memory ∧ post.globals = output.globals) := by
  obtain ⟨middle,tail,retained,locals,globals,postCode,domain,clock⟩ := transaction_type_header_returned_input_prefix state post
    tx kind older olderCount input inputLength finalValue txLocal typeLocal valid beforeTx run
  obtain ⟨count,entry,output,bounded,readable,preserved,atList,localFrame,heapPost,scratchPost,framePost,entryCode,entryDomain,consumed,remaining,covered,endpoint,aligned,bodyRun,finalMemory⟩ :=
    transaction_list_returned_runtime_input_contract_state middle post tag pointer length total scratch frame array ceiling inputLimit
      (by rw [locals]; exact topLocal) noWrap lengthBound limitBound
      (by rw [globals]; exact scratchGlobal) (by rw [globals]; exact frameGlobal)
      (postCode.trans code) orderedFrame framePositive scratchBelow
      (by intro address low high; rw [domain]; exact arena address low high)
      (by rw [globals]; exact heap) arrayBound countLimit
      (by intro address low high; rw [domain]; exact heapArena address low high)
      (by rw [clock]; exact budget) older olderCount input inputLength retained before arrayBeforeFrame inputBeforeFrame inputBeforeArray finalValue tail
  refine ⟨count,entry,output,bounded,readable,preserved,atList,?_,heapPost,scratchPost,framePost,entryCode.trans postCode,entryDomain.trans domain,?_,?_,covered,endpoint,aligned,bodyRun,finalMemory⟩
  · intro name different
    exact (localFrame name different).trans (congrArg (fun map => map.lookup name) locals)
  · rw [clock] at consumed
    exact consumed
  · rw [clock] at remaining
    exact remaining

#print axioms transaction_fields_returned_runtime_input_contract_state
end InitECandidate.Runtime
