import InitECandidate.Runtime.TransactionAllocatedParsingReturnedHeapReservedContractState
import InitECandidate.Runtime.TransactionBodyReturnedAllocationWordState
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem transaction_body_returned_heap_reserved_contract_state {F : Type} (state post : PanSemStateFiniteExact 64 F)
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
    (budget : 402 + ((length.toNat * ((2 * length.toNat + 1) * 15 + 19) + 92635) + reserve) ≤ state.clock)
    (array count input inputLength : BitVec 64)
    (valid : RlpSliceInputPrefix state array input inputLength count.toNat)
    (fits : array.toNat + count.toNat * 16 ≤ 2^64)
    (above : ceiling ≤ array.toNat)
    (tx : BitVec 64)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word tx)))
    (small : tx.toNat + 400 ≤ 33806089496) (aligned : tx.toNat % 8 = 0)
    (txArena : ∀ address : BitVec 64, tx.toNat ≤ address.toNat → address.toNat < tx.toNat + 400 → state.memaddrs address)
    (beforeTx : array.toNat + count.toNat * 16 ≤ tx.toNat)
    (value : ValueHOL 64)
    (run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_decode_transaction_rlp) = (some (.returned value),post)) :
    ∃ (middle output : PanSemStateFiniteExact 64 F) (tag payloadPointer payload total kind : BitVec 64),
      evaluateHOLFiniteState middle (transactionAt 10) = (some (.returned value),output) ∧
      RlpSliceInputPrefix middle array input inputLength count.toNat ∧
      middle.locals.lookup (ofString "top") = some (.rStruct [.val (.word tag),.val (.word payloadPointer),.val (.word payload),.val (.word total)]) ∧
      (tag = 0 ∨ tag = 1) ∧ payload.toNat ≤ length.toNat ∧ total.toNat ≤ length.toNat ∧
      payloadPointer.toNat + payload.toNat ≤ pointer.toNat + length.toNat ∧
      payloadPointer.toNat + payload.toNat < 2^64 ∧ pointer.toNat ≤ payloadPointer.toNat ∧
      middle.globals = (setGlobalHOLFinite (ofString "heap_ptr") (.val (.word (allocationEnd tx 400))) state).globals ∧ middle.code = state.code ∧ middle.memaddrs = state.memaddrs ∧
      middle.locals.lookup (ofString "tx") = some (.val (.word tx)) ∧
      (kind = 0 ∨ kind = 1 ∨ kind = 2 ∨ kind = 3 ∨ kind = 4) ∧
      middle.locals.lookup (ofString "t") = some (.val (.word kind)) ∧
      middle.locals.lookup (ofString "nfields") = some (.val (.word (BitVec.ofNat 64 (transactionRequiredFields kind)))) ∧
      reserve ≤ middle.clock ∧ middle.clock ≤ state.clock ∧ (post.memory = output.memory ∧ post.globals = output.globals) := by
  obtain ⟨positive,entry,bodyOutput,byte,bodyRun,memory,globals,entryCode,domain,clock,locals,atByte,bodyMemory⟩ :=
    transaction_body_returned_allocation_word_state state post pointer length value pointerLocal lengthLocal run
  have retained : RlpSliceInputPrefix entry array input inputLength count.toNat := by
    intro index inside
    obtain ⟨pointer,length,item⟩ := valid index inside
    exact ⟨pointer,length,RlpSliceInputEntry.after_frame state entry array index pointer length input inputLength item domain
      (by rw [memory]) (by rw [memory])⟩
  obtain ⟨middle,output,tag,payloadPointer,payload,total,kind,tail,preserved,atTop,tagBound,payloadBound,totalBound,ends,noWrap,starts,
      finalGlobals,finalCode,finalDomain,finalTx,supported,typePost,countPost,available,remaining,finalMemory⟩ :=
    transaction_allocated_parsing_returned_heap_reserved_contract_state entry bodyOutput pointer length scratch frame ceiling inputLimit
      ((locals _ (by decide)).trans pointerLocal) ((locals _ (by decide)).trans lengthLocal)
      positive inputRange lengthBound limitBound
      (by rw [globals]; exact scratchGlobal) (by rw [globals]; exact frameGlobal)
      (entryCode.trans code) orderedFrame framePositive scratchBelow
      (by intro address low high; rw [domain]; exact arena address low high)
      reserve (by rw [clock]; exact budget) array count input inputLength retained fits above
      tx (by rw [globals]; exact heap) small aligned
      (by intro address low high; rw [domain]; exact txArena address low high) beforeTx byte atByte value bodyRun
  refine ⟨middle,output,tag,payloadPointer,payload,total,kind,tail,preserved,atTop,tagBound,payloadBound,totalBound,
    ends,noWrap,starts,?_,finalCode.trans entryCode,finalDomain.trans domain,finalTx,supported,
    typePost,countPost,available,?_,⟨bodyMemory.1.trans finalMemory.1,bodyMemory.2.trans finalMemory.2⟩⟩
  · simpa only [setGlobalHOLFinite,globals] using finalGlobals
  · rw [clock] at remaining
    exact remaining

#print axioms transaction_body_returned_heap_reserved_contract_state
end InitECandidate.Runtime
