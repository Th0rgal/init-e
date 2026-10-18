import InitECandidate.Runtime.TransactionBodyReturnedGasEntryContractState
import InitECandidate.Runtime.TransactionGasReturnedOuterContract
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

private theorem gas_reserve {cost reserve before after : Nat}
    (available : cost + reserve ≤ before) (consumed : before ≤ after + cost) : reserve ≤ after := by omega

theorem transaction_body_returned_gas_contract_state {F : Type} (state post : PanSemStateFiniteExact 64 F)
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
    (budget : 402 + ((length.toNat * ((2 * length.toNat + 1) * 15 + 19) + 92635) + (length.toNat * ((2 * length.toNat + 1) * 15 + 19) + length.toNat * 12 + 4 + (length.toNat * ((2 * length.toNat + 1) * 15 + 19) + 92643 + (length.toNat * ((2 * length.toNat + 1) * 15 + 19) + 92668 + (2 * (length.toNat * ((2 * length.toNat + 1) * 15 + 19) + 92668) + (length.toNat * ((2 * length.toNat + 1) * 15 + 19) + 92643 + reserve)))))) ≤ state.clock)
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
    (value : ValueHOL 64)
    (run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_decode_transaction_rlp) = (some (.returned value),post)) :
    ∃ (fieldCount kind advance : BitVec 64) (entry output : PanSemStateFiniteExact 64 F),
      advance = (if 1#64 < kind then 2 else 1) ∧
      (advance = 1 ∨ advance = 2) ∧
      fieldCount.toNat = transactionRequiredFields kind ∧ fieldCount.toNat ≤ length.toNat ∧
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
      entry.locals.lookup (ofString "k") = some (.val (.word (((if kind = 0 then 0 else 1) + 1) + advance))) ∧
      evaluateHOLFiniteState entry (transactionAt 25) = (some (.returned value),output) ∧
      (post.memory = output.memory ∧ post.globals = output.globals) := by
  obtain ⟨fieldCount,kind,advance,ready,output,advanceEqual,advanceBound,naturalCount,bounded,spans,preserved,atArray,atTx,supported,atType,
      heapPost,scratchPost,framePost,readyCode,domain,available,remaining,atIndex,tail,memory⟩ :=
    transaction_body_returned_gas_entry_contract_state state post pointer length scratch frame ceiling inputLimit
      pointerLocal lengthLocal inputRange lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive
      scratchBelow arena _ budget array count input inputLength valid before tx heap small aligned txArena countLimit heapArena
      allocationBeforeFrame beforeTx fieldsBeforeFrame inputBeforeTx value run
  have inside : (((if kind = 0 then (0 : BitVec 64) else 1) + 1) + advance).toNat < fieldCount.toNat := by
    rw [naturalCount]
    rcases advanceBound with rfl | rfl <;> rcases supported with rfl | rfl | rfl | rfl | rfl <;> decide
  have geometry : (allocationEnd tx 400).toNat = tx.toNat + 400 := allocationEnd_aligned_toNat tx 400 small aligned (by decide)
  have arrayBelow : (allocationEnd tx 400).toNat + fieldCount.toNat * 16 ≤ frame.toNat := by
    rw [geometry]
    exact (Nat.add_le_add_left (Nat.mul_le_mul_right 16 bounded) _).trans fieldsBeforeFrame
  have costBudget : length.toNat * ((2 * length.toNat + 1) * 15 + 19) + 92643 ≤ ready.clock :=
    (Nat.le_add_right _ reserve).trans available
  obtain ⟨entry,bodyRun,newSpans,oldSpans,globals,locals,entryCode,entryDomain,consumed,entryRemaining⟩ :=
    transaction_gas_returned_outer_contract ready output (allocationEnd tx 400) (((if kind = 0 then 0 else 1) + 1) + advance)
      pointer length scratch frame fieldCount ceiling inputLimit atArray atIndex spans inside lengthBound limitBound
      scratchPost framePost (readyCode.trans code) orderedFrame framePositive scratchBelow
      (by intro address low high; rw [domain]; exact arena address low high) costBudget arrayBelow tx atTx
      array count input inputLength preserved before beforeTx (by rw [geometry]; omega) value tail
  exact ⟨fieldCount,kind,advance,entry,output,advanceEqual,advanceBound,naturalCount,bounded,newSpans,oldSpans,
    (locals _ (by decide)).trans atArray,(locals _ (by decide)).trans atTx,supported,
    (locals _ (by decide)).trans atType,(globals _).trans heapPost,(globals _).trans scratchPost,(globals _).trans framePost,
    entryCode.trans readyCode,entryDomain.trans domain,gas_reserve available consumed,entryRemaining.trans remaining,
    (locals _ (by decide)).trans atIndex,bodyRun,memory⟩

#print axioms transaction_body_returned_gas_contract_state
end InitECandidate.Runtime
