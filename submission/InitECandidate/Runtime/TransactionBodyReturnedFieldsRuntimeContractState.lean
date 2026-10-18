import InitECandidate.Runtime.TransactionBodyReturnedReservedContractState
import InitECandidate.Runtime.TransactionFieldsReturnedRuntimeInputContractState
import InitECandidate.Runtime.AllocationAligned
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

private theorem fieldsCost_mono {m n : Nat} (h : m ≤ n) :
    m * ((2*m+1)*15+19) + m*12+4 ≤ n * ((2*n+1)*15+19) + n*12+4 := by
  have factors : (2*m+1)*15+19 ≤ (2*n+1)*15+19 := by omega
  have products := Nat.mul_le_mul h factors
  omega

private theorem remaining_reserve {cost reserve before after actual : Nat}
    (available : cost + reserve ≤ before) (consumed : before ≤ after + actual)
    (smaller : actual ≤ cost) : reserve ≤ after := by omega

theorem transaction_body_returned_fields_runtime_contract_state {F : Type} (state post : PanSemStateFiniteExact 64 F)
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
      fieldCount.toNat ≤ length.toNat ∧
      RlpSliceInputPrefix entry (allocationEnd tx 400) pointer length fieldCount.toNat ∧
      RlpSliceInputPrefix entry array input inputLength count.toNat ∧
      entry.locals.lookup (ofString "lst") = some (.rStruct [.val (.word (allocationEnd tx 400)),.val (.word fieldCount)]) ∧
      entry.locals.lookup (ofString "tx") = some (.val (.word tx)) ∧
      (kind = 0 ∨ kind = 1 ∨ kind = 2 ∨ kind = 3 ∨ kind = 4) ∧
      entry.locals.lookup (ofString "t") = some (.val (.word kind)) ∧
      entry.locals.lookup (ofString "nfields") = some (.val (.word (BitVec.ofNat 64 (transactionRequiredFields kind)))) ∧
      entry.globals.lookup (ofString "heap_ptr") = some (.val (.word (allocationEnd (allocationEnd tx 400) (fieldCount * 16)))) ∧
      entry.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)) ∧
      entry.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)) ∧
      entry.code = state.code ∧ entry.memaddrs = state.memaddrs ∧
      reserve ≤ entry.clock ∧ entry.clock ≤ state.clock ∧
      (allocationEnd tx 400).toNat + fieldCount.toNat * 16 ≤ (allocationEnd (allocationEnd tx 400) (fieldCount * 16)).toNat ∧
      (allocationEnd (allocationEnd tx 400) (fieldCount * 16)).toNat ≤ 33806089496 ∧
      (allocationEnd (allocationEnd tx 400) (fieldCount * 16)).toNat % 8 = 0 ∧
      evaluateHOLFiniteState entry (transactionAt 13) = (some (.returned value),output) ∧
      (post.memory = output.memory ∧ post.globals = output.globals) := by
  obtain ⟨middle,parsedOutput,tag,payloadPointer,payload,total,kind,tail,preserved,atTop,
      tagBound,payloadBound,totalBound,ends,noWrap,starts,finalGlobals,finalCode,finalDomain,
      finalTx,supported,typePost,countPost,available,remaining,finalMemory⟩ :=
    transaction_body_returned_reserved_contract_state state post pointer length scratch frame ceiling inputLimit
      pointerLocal lengthLocal inputRange lengthBound limitBound scratchGlobal frameGlobal code orderedFrame
      framePositive scratchBelow arena _ budget array count input inputLength valid before tx heap small aligned txArena beforeTx value run
  have geometry : (allocationEnd tx 400).toNat = tx.toNat + 400 :=
    allocationEnd_aligned_toNat tx 400 small aligned (by decide)
  have scratchMiddle : middle.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)) := by
    rw [finalGlobals]
    simpa [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "heap_ptr" ≠ ofString "scratch_ptr" by decide] using scratchGlobal
  have frameMiddle : middle.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)) := by
    rw [finalGlobals]
    simpa [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "heap_ptr" ≠ ofString "frame_mem_ptr" by decide] using frameGlobal
  have heapMiddle : middle.globals.lookup (ofString "heap_ptr") = some (.val (.word (allocationEnd tx 400))) := by
    rw [finalGlobals]
    simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  obtain ⟨fieldCount,entry,output,bounded,readable,retained,atList,locals,heapPost,scratchPost,framePost,entryCode,entryDomain,consumed,entryRemaining,covered,endpoint,entryAligned,bodyRun,bodyMemory⟩ :=
    transaction_fields_returned_runtime_input_contract_state middle parsedOutput tag payloadPointer payload total scratch frame
      (allocationEnd tx 400) tx kind ceiling inputLimit atTop noWrap (payloadBound.trans lengthBound) limitBound
      scratchMiddle frameMiddle (finalCode.trans code) orderedFrame framePositive scratchBelow
      (by intro address low high; rw [finalDomain]; exact arena address low high)
      heapMiddle (by rw [geometry]; exact small) countLimit
      (by intro address low high; rw [finalDomain]; apply heapArena address; omega; exact high)
      ((fieldsCost_mono payloadBound).trans (Nat.le_trans (Nat.le_add_right _ reserve) available)) array count input inputLength preserved
      (by rw [geometry]; omega) (by rw [geometry]; exact allocationBeforeFrame)
      finalTx typePost beforeTx
      (by exact ends.trans (inputBeforeTx.trans (Nat.le_trans (Nat.le_add_right _ _) allocationBeforeFrame)))
      (by rw [geometry]; exact ends.trans (inputBeforeTx.trans (Nat.le_add_right _ _))) value tail
  have spans : RlpSliceInputPrefix entry (allocationEnd tx 400) pointer length fieldCount.toNat := by
    intro index inside
    obtain ⟨itemPointer,itemLength,item⟩ := readable index inside
    exact ⟨itemPointer,itemLength,item.readable,starts.trans item.startsWithin,item.endsWithin.trans ends,item.noWrap⟩
  refine ⟨fieldCount,kind,entry,output,bounded.trans payloadBound,spans,retained,atList,
    (locals _ (by decide)).trans finalTx,supported,(locals _ (by decide)).trans typePost,
    (locals _ (by decide)).trans countPost,heapPost,scratchPost,framePost,
    entryCode.trans finalCode,entryDomain.trans finalDomain,?_,entryRemaining.trans remaining,
    covered,endpoint,entryAligned,bodyRun,⟨finalMemory.1.trans bodyMemory.1,finalMemory.2.trans bodyMemory.2⟩⟩
  exact remaining_reserve available consumed (fieldsCost_mono payloadBound)

#print axioms transaction_body_returned_fields_runtime_contract_state
end InitECandidate.Runtime
