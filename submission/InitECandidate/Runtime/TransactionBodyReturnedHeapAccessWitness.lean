import InitECandidate.Runtime.TransactionBodyReturnedHeapSignatureWitness
import InitECandidate.Runtime.TransactionAccessReturnedGuardedHeapContract
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem transaction_body_returned_heap_access_witness {F : Type} (state post : PanSemStateFiniteExact 64 F)
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
      Nonempty (TransactionDecodeWitness entry (allocationEnd tx 400) fieldCount tx kind pointer length scratch frame ceiling) := by
  obtain ⟨fieldCount,kind,advance,start,output,_,_,_,_,_,preserved,available,tail,memory,active,_,_,fields⟩ :=
    transaction_body_returned_heap_signature_witness state post pointer length scratch frame ceiling inputLimit
      pointerLocal lengthLocal inputRange lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena
      (txListItemAccessCost length.toNat + futureTicks) budget array count input inputLength valid above tx heap within aligned txArena
      (by omega) heapArena inputBeforeFrame beforeTx inputBeforeTx value run
  have small := (transaction_body_returned_allocation_capacity state post pointer length tx value
    pointerLocal lengthLocal code heap within run).2
  have geometry : (allocationEnd tx 400).toNat = tx.toNat + 400 :=
    allocationEnd_aligned_toNat tx 400 small aligned (by decide)
  obtain ⟨entry,rest,retained,next,_,_,ticks,_⟩ := transaction_access_returned_guarded_heap_contract start output
    (allocationEnd tx 400) fieldCount tx kind pointer length scratch frame ceiling inputLimit active (by omega)
    lengthBound limitBound orderedFrame framePositive scratchBelow countLimit
    (by rw [geometry]; omega) inputBeforeFrame (by rw [geometry]; omega) futureTicks available
    array count input inputLength preserved above beforeTx value tail
  exact ⟨fieldCount,kind,entry,output,retained,ticks,rest,memory,⟨next⟩⟩

#print axioms transaction_body_returned_heap_access_witness
end InitECandidate.Runtime
