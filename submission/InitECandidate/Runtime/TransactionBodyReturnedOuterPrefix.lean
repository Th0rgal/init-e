import InitECandidate.Runtime.TransactionBodyReturnedSignatureWitness
import InitECandidate.Runtime.TransactionTypedSignatureKindOuterPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

private theorem signature_space {heap count length frame : Nat}
    (bounded : count ≤ length)
    (space : heap + length*56 + (length*48+46)*length + length*296+7 ≤ frame) :
    heap + count*16 + length*40 + (length*48+46)*length + length*296+7 ≤ frame := by omega

theorem transaction_body_returned_outer_prefix {F : Type} (state post : PanSemStateFiniteExact 64 F)
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
    (suffixCountLimit : inputLimit * 120 < 2^64)
    (suffixSpace : tx.toNat + 400 + length.toNat * 56 + (length.toNat * 48 + 46) * length.toNat + length.toNat * 296 + 7 ≤ frame.toNat)
    (suffixBudget : transactionTypedSignatureCost length.toNat ≤ reserve)
    (value : ValueHOL 64)
    (run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_decode_transaction_rlp) = (some (.returned value),post)) :
    RlpSliceInputPrefix post array input inputLength count.toNat := by
  obtain ⟨fieldCount,kind,advance,entry,output,advanceEqual,advanceBound,supported,naturalCount,bounded,preserved,available,tail,memory,
      active,indexEqual,endpoint,fields⟩ := transaction_body_returned_signature_witness state post pointer length scratch frame ceiling inputLimit
    pointerLocal lengthLocal inputRange lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena reserve budget
    array count input inputLength valid before tx heap small aligned txArena countLimit heapArena allocationBeforeFrame beforeTx fieldsBeforeFrame inputBeforeTx
    heapSpace value run
  have geometry : (allocationEnd tx 400).toNat = tx.toNat + 400 := allocationEnd_aligned_toNat tx 400 small aligned (by decide)
  have arrayBelow : (allocationEnd tx 400).toNat + fieldCount.toNat * 16 ≤ frame.toNat := by
    rw [geometry]
    exact (Nat.add_le_add_left (Nat.mul_le_mul_right 16 bounded) _).trans fieldsBeforeFrame
  have space : active.heap.toNat + length.toNat * 40 + (length.toNat * 48 + 46) * length.toNat + length.toNat * 296 + 7 ≤ frame.toNat := by
    rw [endpoint]
    exact signature_space bounded suffixSpace
  have preservedOutput := transaction_typed_signature_returned_outer_prefix_by_kind entry output (allocationEnd tx 400) fieldCount tx kind pointer length scratch frame ceiling inputLimit
    active fields lengthBound limitBound orderedFrame framePositive scratchBelow suffixCountLimit arrayBelow
    (by rw [geometry]; omega) space (suffixBudget.trans available)
    array count input inputLength preserved before beforeTx (by have limit := tx.isLt; omega) value tail
  have metadata := evaluateHOLFiniteState_metadata state (sourceFunctionBody Guest.guestFn_decode_transaction_rlp)
  rw [run] at metadata
  intro slot inside
  obtain ⟨p,n,item⟩ := preservedOutput slot inside
  obtain ⟨oldP,oldN,original⟩ := valid slot inside
  refine ⟨p,n,⟨?_,item.startsWithin,item.endsWithin,item.noWrap⟩⟩
  refine ⟨?_,?_,?_,?_⟩
  · rw [metadata.2.1]; exact original.readable.pointerDomain
  · rw [metadata.2.1]; exact original.readable.lengthDomain
  · rw [memory]; exact item.readable.pointerCell
  · rw [memory]; exact item.readable.lengthCell

#print axioms transaction_body_returned_outer_prefix
end InitECandidate.Runtime
