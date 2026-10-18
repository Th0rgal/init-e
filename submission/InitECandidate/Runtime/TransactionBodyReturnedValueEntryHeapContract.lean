import InitECandidate.Runtime.TransactionBodyReturnedToHeapContract
import InitECandidate.Runtime.TransactionToAdvanceSuffixBound
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem transaction_body_returned_value_entry_heap_contract {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer length scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (lengthLocal : state.locals.lookup (ofString "len") = some (.val (.word length)))
    (inputRange : pointer.toNat + length.toNat < 2^64) (lengthBound : length.toNat ≤ inputLimit)
    (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (reserve : Nat)
    (budget : 402 + ((length.toNat * ((2 * length.toNat + 1) * 15 + 19) + 92635) + (length.toNat * ((2 * length.toNat + 1) * 15 + 19) + length.toNat * 12 + 4 + (length.toNat * ((2 * length.toNat + 1) * 15 + 19) + 92643 + (length.toNat * ((2 * length.toNat + 1) * 15 + 19) + 92668 + (2 * (length.toNat * ((2 * length.toNat + 1) * 15 + 19) + 92668) + (length.toNat * ((2 * length.toNat + 1) * 15 + 19) + 92643 + (length.toNat * ((2 * length.toNat + 1) * 15 + 19) + 92634 + reserve))))))) ≤ state.clock)
    (array count input inputLength : BitVec 64)
    (valid : RlpSliceInputPrefix state array input inputLength count.toNat)
    (above : ceiling ≤ array.toNat)
    (tx : BitVec 64)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word tx)))
    (within : tx.toNat ≤ 33806089496) (aligned : tx.toNat % 8 = 0)
    (txArena : ∀ address : BitVec 64, tx.toNat ≤ address.toNat → address.toNat < tx.toNat + 400 → state.memaddrs address)
    (countLimit : inputLimit * 16 < 2^64)
    (heapArena : ∀ address : BitVec 64, tx.toNat ≤ address.toNat → address.toNat < 33806089496 → state.memaddrs address)
    (inputBeforeFrame : pointer.toNat + length.toNat ≤ frame.toNat)
    (beforeTx : array.toNat + count.toNat * 16 ≤ tx.toNat)
    (inputBeforeTx : pointer.toNat + length.toNat ≤ tx.toNat)
    (value : ValueHOL 64)
    (run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_decode_transaction_rlp) = (some (.returned value),post)) :
    ∃ (fieldCount kind advance : BitVec 64) (entry output : PanSemStateFiniteExact 64 F),
      advance = (if 1#64 < kind then 2 else 1) ∧
      (advance = 1 ∨ advance = 2) ∧
      fieldCount.toNat = transactionRequiredFields kind ∧ fieldCount.toNat ≤ length.toNat ∧
      (allocationEnd tx 400).toNat + fieldCount.toNat * 16 ≤ 33806089496 ∧
      RlpSliceInputPrefix entry (allocationEnd tx 400) pointer length fieldCount.toNat ∧
      RlpSliceInputPrefix entry array input inputLength count.toNat ∧
      entry.locals.lookup (ofString "arr") = some (.val (.word (allocationEnd tx 400))) ∧
      entry.locals.lookup (ofString "tx") = some (.val (.word tx)) ∧
      (kind = 0 ∨ kind = 1 ∨ kind = 2 ∨ kind = 3 ∨ kind = 4) ∧
      entry.locals.lookup (ofString "t") = some (.val (.word kind)) ∧
      entry.globals.lookup (ofString "heap_ptr") = some (.val (.word (allocationEnd (allocationEnd tx 400) (fieldCount * 16)))) ∧
      entry.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)) ∧
      entry.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)) ∧
      entry.code = state.code ∧ entry.memaddrs = state.memaddrs ∧
      reserve ≤ entry.clock ∧ entry.clock ≤ state.clock ∧
      entry.locals.lookup (ofString "k") = some (.val (.word (((((if kind = 0 then 0 else 1) + 1) + advance) + 1) + 1))) ∧
      evaluateHOLFiniteState entry (transactionAt 29) = (some (.returned value),output) ∧
      post.memory = output.memory := by
  obtain ⟨fieldCount,kind,advance,ready,output,advanceEqual,advanceBound,naturalCount,bounded,fieldExtent,spans,preserved,atArray,atTx,supported,atType,
      heapPost,scratchPost,framePost,readyCode,domain,available,remaining,atIndex,tail,memory⟩ :=
    transaction_body_returned_to_heap_contract state post pointer length scratch frame ceiling inputLimit
      pointerLocal lengthLocal inputRange lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive
      scratchBelow arena reserve budget array count input inputLength valid above tx heap within aligned txArena countLimit heapArena
      inputBeforeFrame beforeTx inputBeforeTx value run
  rw [source_transaction_to_advance,evaluateHOLFiniteState_seq_line780,
    transaction_index_advance_run ready ((((if kind = 0 then 0 else 1) + 1) + advance) + 1) atIndex] at tail
  let entry := setVarHOLFinite (ofString "k") (.val (.word (((((if kind = 0 then 0 else 1) + 1) + advance) + 1) + 1))) ready
  have newSpans : RlpSliceInputPrefix entry (allocationEnd tx 400) pointer length fieldCount.toNat := by
    intro index inside
    obtain ⟨p,n,item⟩ := spans index inside
    exact ⟨p,n,RlpSliceInputEntry.after_frame ready entry _ _ _ _ _ _ item rfl rfl rfl⟩
  have oldSpans : RlpSliceInputPrefix entry array input inputLength count.toNat := by
    intro index inside
    obtain ⟨p,n,item⟩ := preserved index inside
    exact ⟨p,n,RlpSliceInputEntry.after_frame ready entry _ _ _ _ _ _ item rfl rfl rfl⟩
  refine ⟨fieldCount,kind,advance,entry,output,advanceEqual,advanceBound,naturalCount,bounded,fieldExtent,newSpans,oldSpans,?_,?_,supported,?_,
    heapPost,scratchPost,framePost,readyCode,domain,available,remaining,?_,tail,memory⟩
  · simpa [entry,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "k" ≠ ofString "arr" by decide] using atArray
  · simpa [entry,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "k" ≠ ofString "tx" by decide] using atTx
  · simpa [entry,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "k" ≠ ofString "t" by decide] using atType
  · simp [entry,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]

#print axioms transaction_body_returned_value_entry_heap_contract
end InitECandidate.Runtime
