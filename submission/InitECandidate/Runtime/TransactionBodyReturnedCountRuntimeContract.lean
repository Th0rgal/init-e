import InitECandidate.Runtime.TransactionBodyReturnedFieldsRuntimeContract
import InitECandidate.Runtime.TransactionFieldCountReturned
import InitECandidate.Runtime.TransactionIndexWordReturnedScope
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem transaction_body_returned_count_runtime_contract {F : Type} (state post : PanSemStateFiniteExact 64 F)
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
    (budget : 402 + ((length.toNat * ((2 * length.toNat + 1) * 15 + 19) + 92635) + (length.toNat * ((2 * length.toNat + 1) * 15 + 19) + length.toNat * 12 + 4 + reserve)) ≤ state.clock)
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
      entry.locals.lookup (ofString "k") = some (.val (.word 0)) ∧
      entry.locals.lookup (ofString "w") = some (.val (.word 0)) ∧
      entry.globals.lookup (ofString "heap_ptr") = some (.val (.word (allocationEnd (allocationEnd tx 400) (fieldCount * 16)))) ∧
      entry.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)) ∧
      entry.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)) ∧
      entry.code = state.code ∧ entry.memaddrs = state.memaddrs ∧
      reserve ≤ entry.clock ∧ entry.clock ≤ state.clock ∧
      (allocationEnd tx 400).toNat + fieldCount.toNat * 16 ≤ (allocationEnd (allocationEnd tx 400) (fieldCount * 16)).toNat ∧
      (allocationEnd (allocationEnd tx 400) (fieldCount * 16)).toNat ≤ 33806089496 ∧
      (allocationEnd (allocationEnd tx 400) (fieldCount * 16)).toNat % 8 = 0 ∧
      evaluateHOLFiniteState entry (transactionAt 17) = (some (.returned value),output) ∧
      post.memory = output.memory := by
  obtain ⟨fieldCount,kind,ready,tailOutput,bounded,spans,preserved,atList,atTx,supported,atType,atCount,heapPost,scratchPost,framePost,entryCode,domain,available,remaining,covered,endpoint,alignedPost,tail,memory⟩ :=
    transaction_body_returned_fields_runtime_contract state post pointer length scratch frame ceiling inputLimit
      pointerLocal lengthLocal inputRange lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive
      scratchBelow arena reserve budget array count input inputLength valid before tx heap small aligned txArena countLimit heapArena
      allocationBeforeFrame beforeTx inputBeforeTx value run
  obtain ⟨equal,indexOutput,indexRun,bodyMemory⟩ := transaction_array_returned_field_count ready tailOutput
    (allocationEnd tx 400) fieldCount (BitVec.ofNat 64 (transactionRequiredFields kind)) value atList atCount tail
  obtain ⟨output,bodyRun,scopeMemory⟩ := transaction_index_word_returned_scope
    (setVarHOLFinite (ofString "arr") (.val (.word (allocationEnd tx 400))) ready) indexOutput value indexRun
  let entry := setVarHOLFinite (ofString "w") (.val (.word 0))
    (setVarHOLFinite (ofString "k") (.val (.word 0)) (setVarHOLFinite (ofString "arr") (.val (.word (allocationEnd tx 400))) ready))
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
  refine ⟨fieldCount,kind,entry,output,equal,naturalCount,bounded,newSpans,oldSpans,?_,?_,supported,?_,?_,?_,heapPost,scratchPost,framePost,entryCode,domain,available,remaining,covered,endpoint,alignedPost,bodyRun,memory.trans (bodyMemory.trans scopeMemory)⟩
  · simp [entry,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "w" ≠ ofString "arr" by decide, show ofString "k" ≠ ofString "arr" by decide]
  · simpa [entry,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "arr" ≠ ofString "tx" by decide,
      show ofString "w" ≠ ofString "tx" by decide, show ofString "k" ≠ ofString "tx" by decide] using atTx
  · simpa [entry,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "arr" ≠ ofString "t" by decide,
      show ofString "w" ≠ ofString "t" by decide, show ofString "k" ≠ ofString "t" by decide] using atType

  · simp [entry,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "w" ≠ ofString "k" by decide]
  · simp [entry,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]

#print axioms transaction_body_returned_count_runtime_contract
end InitECandidate.Runtime
