import InitECandidate.Runtime.TransactionBodyReturnedDataContract
import InitECandidate.Runtime.TransactionFieldArrayWitness
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem transaction_body_returned_signature_witness {F : Type} (state post : PanSemStateFiniteExact 64 F)
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
    (budget : 402 + ((length.toNat * ((2 * length.toNat + 1) * 15 + 19) + 92635) + (length.toNat * ((2 * length.toNat + 1) * 15 + 19) + length.toNat * 12 + 4 + (length.toNat * ((2 * length.toNat + 1) * 15 + 19) + 92643 + (length.toNat * ((2 * length.toNat + 1) * 15 + 19) + 92668 + (2 * (length.toNat * ((2 * length.toNat + 1) * 15 + 19) + 92668) + (length.toNat * ((2 * length.toNat + 1) * 15 + 19) + 92643 + (length.toNat * ((2 * length.toNat + 1) * 15 + 19) + 92634 + (length.toNat * ((2 * length.toNat + 1) * 15 + 19) + 92668 + (length.toNat * ((2 * length.toNat + 1) * 15 + 19) + 92634 + reserve))))))))) ≤ state.clock)
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
    (fieldsBeforeFrame : tx.toNat + 400 + length.toNat * 16 ≤ frame.toNat)
    (inputBeforeTx : pointer.toNat + length.toNat ≤ tx.toNat)
    (heapSpace : tx.toNat + 400 + length.toNat * 16 ≤ 33806089496)
    (value : ValueHOL 64)
    (run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_decode_transaction_rlp) = (some (.returned value),post)) :
    ∃ (fieldCount kind advance : BitVec 64) (entry output : PanSemStateFiniteExact 64 F),
      (advance = 1 ∨ advance = 2) ∧
      (kind = 0 ∨ kind = 1 ∨ kind = 2 ∨ kind = 3 ∨ kind = 4) ∧
      fieldCount.toNat = transactionRequiredFields kind ∧ fieldCount.toNat ≤ length.toNat ∧
      RlpSliceInputPrefix entry array input inputLength count.toNat ∧
      reserve ≤ entry.clock ∧
      evaluateHOLFiniteState entry transactionTypedSignature = (some (.returned value),output) ∧ post.memory = output.memory ∧
      ∃ active : TransactionDecodeWitness entry (allocationEnd tx 400) fieldCount tx kind pointer length scratch frame ceiling,
        active.index = (((((((if kind = 0 then (0 : BitVec 64) else 1) + 1) + advance) + 1) + 1) + 1) + 1) ∧
        active.heap.toNat = tx.toNat + 400 + fieldCount.toNat * 16 := by
  obtain ⟨fieldCount,kind,advance,entry,output,advanceBound,naturalCount,bounded,spans,preserved,atArray,atTx,supported,atType,
      heapPost,scratchPost,framePost,entryCode,domain,available,remaining,atIndex,tail,memory⟩ :=
    transaction_body_returned_data_contract state post pointer length scratch frame ceiling inputLimit
      pointerLocal lengthLocal inputRange lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive
      scratchBelow arena reserve budget array count input inputLength valid before tx heap small aligned txArena countLimit heapArena
      allocationBeforeFrame beforeTx fieldsBeforeFrame inputBeforeTx value run
  have indexBound : (((((((if kind = 0 then (0 : BitVec 64) else 1) + 1) + advance) + 1) + 1) + 1) + 1).toNat ≤ fieldCount.toNat := by
    rw [naturalCount]
    rcases advanceBound with rfl | rfl <;> rcases supported with rfl | rfl | rfl | rfl | rfl <;> decide
  have fieldSpace : tx.toNat + 400 + fieldCount.toNat * 16 ≤ 33806089496 :=
    (Nat.add_le_add_left (Nat.mul_le_mul_right 16 bounded) _).trans heapSpace
  obtain ⟨active,indexEqual,_,endpoint⟩ := transaction_field_array_decode_witness entry tx fieldCount kind
    (((((((if kind = 0 then (0 : BitVec 64) else 1) + 1) + advance) + 1) + 1) + 1) + 1) pointer length scratch frame ceiling atArray atTx atType atIndex indexBound spans scratchPost framePost heapPost
    (entryCode.trans code)
    (by intro address low high; rw [domain]; exact arena address low high)
    (by intro address low high; rw [domain]; exact heapArena address low high) fieldSpace aligned inputBeforeTx
  exact ⟨fieldCount,kind,advance,entry,output,advanceBound,supported,naturalCount,bounded,preserved,available,tail,memory,active,indexEqual,endpoint⟩

#print axioms transaction_body_returned_signature_witness
end InitECandidate.Runtime
