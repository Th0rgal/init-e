import InitECandidate.Runtime.TransactionBodyReturnedHeapFinalSignatureState
import InitECandidate.Runtime.TransactionSignatureWitnessHeapGlobals
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem transaction_body_returned_guarded_heap_contract {F : Type} (state post : PanSemStateFiniteExact 64 F)
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
    (budget : 402 + ((length.toNat * ((2 * length.toNat + 1) * 15 + 19) + 92635) + (length.toNat * ((2 * length.toNat + 1) * 15 + 19) + length.toNat * 12 + 4 + (length.toNat * ((2 * length.toNat + 1) * 15 + 19) + 92643 + (length.toNat * ((2 * length.toNat + 1) * 15 + 19) + 92668 + (2 * (length.toNat * ((2 * length.toNat + 1) * 15 + 19) + 92668) + (length.toNat * ((2 * length.toNat + 1) * 15 + 19) + 92643 + (length.toNat * ((2 * length.toNat + 1) * 15 + 19) + 92634 + (length.toNat * ((2 * length.toNat + 1) * 15 + 19) + 92668 + (length.toNat * ((2 * length.toNat + 1) * 15 + 19) + 92634 + (txListItemAccessCost length.toNat + ((length.toNat * ((2 * length.toNat + 1) * 15 + 19) + 92668) + txListItemBlobCost length.toNat + (txListItemAuthorizationCost length.toNat + (3 * (length.toNat * ((2 * length.toNat + 1) * 15 + 19) + 92668)))))))))))))) ≤ state.clock)
    (array count input inputLength : BitVec 64)
    (valid : RlpSliceInputPrefix state array input inputLength count.toNat)
    (above : ceiling ≤ array.toNat)
    (tx : BitVec 64)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word tx)))
    (within : tx.toNat ≤ 33806089496) (aligned : tx.toNat % 8 = 0)
    (txArena : ∀ address : BitVec 64, tx.toNat ≤ address.toNat → address.toNat < tx.toNat + 400 → state.memaddrs address)
    (countLimit : inputLimit * 120 < 2^64)
    (heapArena : ∀ address : BitVec 64, tx.toNat ≤ address.toNat → address.toNat < 33806089496 → state.memaddrs address)
    (inputBeforeFrame : pointer.toNat + length.toNat ≤ frame.toNat)
    (beforeTx : array.toNat + count.toNat * 16 ≤ tx.toNat)
    (inputBeforeTx : pointer.toNat + length.toNat ≤ tx.toNat)
    (value : ValueHOL 64)
    (run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_decode_transaction_rlp) = (some (.returned value),post)) :
    ∃ fieldCount finalHeap : BitVec 64,
      fieldCount.toNat ≤ length.toNat ∧
      post.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)) ∧
      post.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)) ∧
      post.globals.lookup (ofString "heap_ptr") = some (.val (.word finalHeap)) ∧
      finalHeap.toNat ≤ 33806089496 ∧ finalHeap.toNat % 8 = 0 ∧
      tx.toNat + 400 + fieldCount.toNat * 16 ≤ finalHeap.toNat ∧
      finalHeap.toNat ≤ tx.toNat + 400 + fieldCount.toNat * 16 + length.toNat * 40 +
        (length.toNat * 48 + 46) * length.toNat + length.toNat * 280 := by
  obtain ⟨fieldCount,kind,entry,output,preserved,ticks,tail,memory,supported,naturalCount,countBound,active,fields,lower,upper⟩ :=
    transaction_body_returned_heap_final_signature_state state post pointer length scratch frame ceiling inputLimit
      pointerLocal lengthLocal inputRange lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena
      (3 * (length.toNat * ((2 * length.toNat + 1) * 15 + 19) + 92668)) budget array count input inputLength valid above tx heap within aligned txArena
      countLimit heapArena inputBeforeFrame beforeTx inputBeforeTx value run
  have small := (transaction_body_returned_allocation_capacity state post pointer length tx value
    pointerLocal lengthLocal code heap within run).2
  have geometry : (allocationEnd tx 400).toNat = tx.toNat + 400 :=
    allocationEnd_aligned_toNat tx 400 small aligned (by decide)
  have arrayAbove : ceiling ≤ (allocationEnd tx 400).toNat := by rw [geometry]; omega
  have arrayFits : (allocationEnd tx 400).toNat + fieldCount.toNat * 16 ≤ 2^64 := by
    have h := active.arrayBeforeHeap; have bound := active.heapBound; omega
  have watchedFits : array.toNat + count.toNat * 16 ≤ 2^64 := by omega
  have globals := transaction_signature_witness_returned_heap_globals entry output (allocationEnd tx 400) fieldCount tx kind pointer length scratch frame ceiling inputLimit
    active fields (by rw [geometry]; omega) arrayFits arrayAbove lengthBound limitBound orderedFrame framePositive scratchBelow ticks
    array count input inputLength preserved watchedFits above beforeTx (by omega) value tail
  have scratchFinal : post.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)) := by
    rw [memory.2]; exact (globals _).trans active.scratchGlobal
  have frameFinal : post.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)) := by
    rw [memory.2]; exact (globals _).trans active.frameGlobal
  have heapFinal : post.globals.lookup (ofString "heap_ptr") = some (.val (.word active.heap)) := by
    rw [memory.2]; exact (globals _).trans active.heapGlobal
  refine ⟨fieldCount,active.heap,countBound,scratchFinal,frameFinal,heapFinal,active.heapBound,active.heapAligned,lower,?_⟩
  omega

#print axioms transaction_body_returned_guarded_heap_contract
end InitECandidate.Runtime
