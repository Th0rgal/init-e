import InitECandidate.Runtime.TransactionBodyReturnedHeapSignatureWitness
import InitECandidate.Runtime.TransactionAccessReturnedGuardedHeapContract
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem transaction_body_returned_heap_access_fields {F : Type} (state post : PanSemStateFiniteExact 64 F)
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
    (futureTicks : Nat)
    (budget : 402 + ((length.toNat * ((2 * length.toNat + 1) * 15 + 19) + 92635) + (length.toNat * ((2 * length.toNat + 1) * 15 + 19) + length.toNat * 12 + 4 + (length.toNat * ((2 * length.toNat + 1) * 15 + 19) + 92643 + (length.toNat * ((2 * length.toNat + 1) * 15 + 19) + 92668 + (2 * (length.toNat * ((2 * length.toNat + 1) * 15 + 19) + 92668) + (length.toNat * ((2 * length.toNat + 1) * 15 + 19) + 92643 + (length.toNat * ((2 * length.toNat + 1) * 15 + 19) + 92634 + (length.toNat * ((2 * length.toNat + 1) * 15 + 19) + 92668 + (length.toNat * ((2 * length.toNat + 1) * 15 + 19) + 92634 + (txListItemAccessCost length.toNat + futureTicks)))))))))) ≤ state.clock)
    (array count input inputLength : BitVec 64)
    (valid : RlpSliceInputPrefix state array input inputLength count.toNat)
    (above : ceiling ≤ array.toNat)
    (tx : BitVec 64)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word tx)))
    (within : tx.toNat ≤ 33806089496) (aligned : tx.toNat % 8 = 0)
    (txArena : ∀ address : BitVec 64, tx.toNat ≤ address.toNat → address.toNat < tx.toNat + 400 → state.memaddrs address)
    (countLimit : inputLimit * 32 < 2^64)
    (heapArena : ∀ address : BitVec 64, tx.toNat ≤ address.toNat → address.toNat < 33806089496 → state.memaddrs address)
    (inputBeforeFrame : pointer.toNat + length.toNat ≤ frame.toNat)
    (beforeTx : array.toNat + count.toNat * 16 ≤ tx.toNat)
    (inputBeforeTx : pointer.toNat + length.toNat ≤ tx.toNat)
    (value : ValueHOL 64)
    (run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_decode_transaction_rlp) = (some (.returned value),post)) :
    ∃ (fieldCount kind : BitVec 64) (entry output : PanSemStateFiniteExact 64 F),
      RlpSliceInputPrefix entry array input inputLength count.toNat ∧
      futureTicks ≤ entry.clock ∧
      evaluateHOLFiniteState entry transactionBlobSignature = (some (.returned value),output) ∧
      post.memory = output.memory ∧
      (kind = 0 ∨ kind = 1 ∨ kind = 2 ∨ kind = 3 ∨ kind = 4) ∧
      fieldCount.toNat = transactionRequiredFields kind ∧ fieldCount.toNat ≤ length.toNat ∧
      ∃ next : TransactionDecodeWitness entry (allocationEnd tx 400) fieldCount tx kind pointer length scratch frame ceiling,
        next.index.toNat + (if kind = 3#64 then 2 else 0) + (if kind = 4#64 then 1 else 0) + 3 ≤ fieldCount.toNat ∧
        tx.toNat + 400 + fieldCount.toNat * 16 ≤ next.heap.toNat ∧
        next.heap.toNat ≤ tx.toNat + 400 + fieldCount.toNat * 16 + length.toNat * 40 + (length.toNat * 48 + 46) * length.toNat := by
  obtain ⟨fieldCount,kind,advance,start,output,_,_,supported,naturalCount,countBound,preserved,available,tail,memory,active,_,heapStart,fields⟩ :=
    transaction_body_returned_heap_signature_witness state post pointer length scratch frame ceiling inputLimit
      pointerLocal lengthLocal inputRange lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena
      (txListItemAccessCost length.toNat + futureTicks) budget array count input inputLength valid above tx heap within aligned txArena
      (by omega) heapArena inputBeforeFrame beforeTx inputBeforeTx value run
  have small := (transaction_body_returned_allocation_capacity state post pointer length tx value
    pointerLocal lengthLocal code heap within run).2
  have geometry : (allocationEnd tx 400).toNat = tx.toNat + 400 :=
    allocationEnd_aligned_toNat tx 400 small aligned (by decide)
  obtain ⟨entry,rest,retained,next,indexEqual,lower,ticks,upper⟩ := transaction_access_returned_guarded_heap_contract start output
    (allocationEnd tx 400) fieldCount tx kind pointer length scratch frame ceiling inputLimit active (by omega)
    lengthBound limitBound orderedFrame framePositive scratchBelow countLimit
    (by rw [geometry]; omega) inputBeforeFrame (by rw [geometry]; omega) futureTicks available
    array count input inputLength preserved above beforeTx value tail
  have nextFields : next.index.toNat + (if kind = 3#64 then 2 else 0) +
      (if kind = 4#64 then 1 else 0) + 3 ≤ fieldCount.toNat := by
    rw [indexEqual]
    by_cases legacy : kind = 0#64
    · simp only [legacy,ite_true] at fields ⊢
      omega
    · simp only [legacy,ite_false] at fields ⊢
      have noWrap : active.index.toNat + 1 < 2^64 := by have h := fieldCount.isLt; omega
      rw [BitVec.toNat_add_of_lt (by simpa using noWrap)]
      simpa using fields
  rw [heapStart] at lower upper
  exact ⟨fieldCount,kind,entry,output,retained,ticks,rest,memory,supported,naturalCount,countBound,next,nextFields,lower,upper⟩

#print axioms transaction_body_returned_heap_access_fields
end InitECandidate.Runtime
