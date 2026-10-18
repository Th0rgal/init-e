import InitECandidate.Runtime.TransactionBodyReturnedFieldSpansContract
import InitECandidate.Runtime.TransactionFieldCountReturned
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem transaction_body_returned_count_contract {F : Type} (state post : PanSemStateFiniteExact 64 F)
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
    (budget : 402 + ((length.toNat * ((2 * length.toNat + 1) * 15 + 19) + 92635) + (length.toNat * ((2 * length.toNat + 1) * 15 + 19) + length.toNat * 12 + 4)) ≤ state.clock)
    (array count input inputLength : BitVec 64)
    (valid : RlpSliceInputPrefix state array input inputLength count.toNat)
    (before : array.toNat + count.toNat * 16 ≤ frame.toNat)
    (tx : BitVec 64)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word tx)))
    (small : tx.toNat + 400 ≤ 33806089496) (aligned : tx.toNat % 8 = 0)
    (txArena : ∀ address : BitVec 64, tx.toNat ≤ address.toNat → address.toNat < tx.toNat + 400 → state.memaddrs address)
    (countLimit : inputLimit * 16 < 2^64)
    (heapArena : ∀ address : BitVec 64, tx.toNat ≤ address.toNat → address.toNat < 33806089496 → state.memaddrs address)
    (allocationBeforeFrame : tx.toNat + 400 ≤ frame.toNat)
    (beforeTx : array.toNat + count.toNat * 16 ≤ tx.toNat)
    (inputBeforeTx : pointer.toNat + length.toNat ≤ tx.toNat)
    (value : ValueHOL 64)
    (run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_decode_transaction_rlp) = (some (.returned value),post)) :
    ∃ (fieldCount kind : BitVec 64) (entry output : PanSemStateFiniteExact 64 F),
      fieldCount = BitVec.ofNat 64 (transactionRequiredFields kind) ∧
      fieldCount.toNat = transactionRequiredFields kind ∧
      fieldCount.toNat ≤ length.toNat ∧
      RlpSliceInputPrefix entry (allocationEnd tx 400) pointer length fieldCount.toNat ∧
      RlpSliceInputPrefix entry array input inputLength count.toNat ∧
      entry.locals.lookup (ofString "arr") = some (.val (.word (allocationEnd tx 400))) ∧
      entry.locals.lookup (ofString "tx") = some (.val (.word tx)) ∧
      (kind = 0 ∨ kind = 1 ∨ kind = 2 ∨ kind = 3 ∨ kind = 4) ∧
      entry.locals.lookup (ofString "t") = some (.val (.word kind)) ∧
      evaluateHOLFiniteState entry (transactionAt 15) = (some (.returned value),output) ∧
      post.memory = output.memory := by
  obtain ⟨fieldCount,kind,ready,tailOutput,bounded,spans,preserved,atList,atTx,supported,atType,atCount,tail,memory⟩ :=
    transaction_body_returned_field_spans_contract state post pointer length scratch frame ceiling inputLimit
      pointerLocal lengthLocal inputRange lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive
      scratchBelow arena budget array count input inputLength valid before tx heap small aligned txArena countLimit heapArena
      allocationBeforeFrame beforeTx inputBeforeTx value run
  obtain ⟨equal,output,bodyRun,bodyMemory⟩ := transaction_array_returned_field_count ready tailOutput
    (allocationEnd tx 400) fieldCount (BitVec.ofNat 64 (transactionRequiredFields kind)) value atList atCount tail
  let entry := setVarHOLFinite (ofString "arr") (.val (.word (allocationEnd tx 400))) ready
  have newSpans : RlpSliceInputPrefix entry (allocationEnd tx 400) pointer length fieldCount.toNat := by
    intro index inside
    obtain ⟨p,n,item⟩ := spans index inside
    exact ⟨p,n,RlpSliceInputEntry.after_frame ready entry _ _ _ _ _ _ item rfl rfl rfl⟩
  have oldSpans : RlpSliceInputPrefix entry array input inputLength count.toNat := by
    intro index inside
    obtain ⟨p,n,item⟩ := preserved index inside
    exact ⟨p,n,RlpSliceInputEntry.after_frame ready entry _ _ _ _ _ _ item rfl rfl rfl⟩
  have naturalCount : fieldCount.toNat = transactionRequiredFields kind := by
    rw [equal]
    rcases supported with rfl | rfl | rfl | rfl | rfl <;> decide
  refine ⟨fieldCount,kind,entry,output,equal,naturalCount,bounded,newSpans,oldSpans,?_,?_,supported,?_,bodyRun,memory.trans bodyMemory⟩
  · simp [entry,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  · simpa [entry,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "arr" ≠ ofString "tx" by decide] using atTx
  · simpa [entry,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "arr" ≠ ofString "t" by decide] using atType

#print axioms transaction_body_returned_count_contract
end InitECandidate.Runtime
