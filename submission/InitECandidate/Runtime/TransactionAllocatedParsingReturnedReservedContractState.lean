import InitECandidate.Runtime.TransactionInitializedParsingReturnedReservedContractState
import InitECandidate.Runtime.TransactionAllocationReturnedState
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

private theorem allocated_parser_reserve (clock reserved : Nat) (budget : 402 + reserved ≤ clock) :
    401 + reserved ≤ clock - 1 := by omega

theorem transaction_allocated_parsing_returned_reserved_contract_state {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer length scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (lengthLocal : state.locals.lookup (ofString "len") = some (.val (.word length)))
    (positive : 0 < length.toNat)
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
    (before : array.toNat + count.toNat * 16 ≤ frame.toNat)
    (tx : BitVec 64)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word tx)))
    (small : tx.toNat + 400 ≤ 33806089496) (aligned : tx.toNat % 8 = 0)
    (txArena : ∀ address : BitVec 64, tx.toNat ≤ address.toNat → address.toNat < tx.toNat + 400 → state.memaddrs address)
    (beforeTx : array.toNat + count.toNat * 16 ≤ tx.toNat)
    (byte : BitVec 64)
    (byteLocal : state.locals.lookup (ofString "b0") = some (.val (.word byte)))
    (value : ValueHOL 64)
    (run : evaluateHOLFiniteState state (transactionAt 2) = (some (.returned value),post)) :
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
  have nonzero : state.clock ≠ 0 := by omega
  obtain ⟨entry,allocatedOutput,bodyRun,atTx,locals,memory,entryCode,domain,clock,globals,allocatedMemory⟩ :=
    transaction_allocation_returned_state state post tx value heap code nonzero small aligned run
  have retained : RlpSliceInputPrefix entry array input inputLength count.toNat := by
    intro index inside
    obtain ⟨pointer,length,item⟩ := valid index inside
    exact ⟨pointer,length,RlpSliceInputEntry.after_frame state entry array index pointer length input inputLength item domain
      (by rw [memory]) (by rw [memory])⟩
  have scratchEntry : entry.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)) := by
    rw [globals]
    simpa [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "heap_ptr" ≠ ofString "scratch_ptr" by decide] using scratchGlobal
  have frameEntry : entry.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)) := by
    rw [globals]
    simpa [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "heap_ptr" ≠ ofString "frame_mem_ptr" by decide] using frameGlobal
  obtain ⟨middle,output,tag,payloadPointer,payload,total,kind,tail,preserved,atTop,tagBound,payloadBound,totalBound,ends,noWrap,starts,
      finalGlobals,finalCode,finalDomain,finalTx,supported,typePost,countPost,available,remaining,finalMemory⟩ :=
    transaction_initialized_parsing_returned_reserved_contract_state entry allocatedOutput pointer length scratch frame ceiling inputLimit
      ((locals _ (by decide)).trans pointerLocal) ((locals _ (by decide)).trans lengthLocal)
      positive inputRange lengthBound limitBound scratchEntry frameEntry (entryCode.trans code) orderedFrame framePositive scratchBelow
      (by intro address low high; rw [domain]; exact arena address low high)
      reserve (by rw [clock]; exact allocated_parser_reserve _ _ budget) array count input inputLength retained before
      tx atTx small aligned (by intro address low high; rw [domain]; exact txArena address low high) beforeTx
      byte ((locals _ (by decide)).trans byteLocal) value bodyRun
  refine ⟨middle,output,tag,payloadPointer,payload,total,kind,tail,preserved,atTop,tagBound,payloadBound,totalBound,
    ends,noWrap,starts,finalGlobals.trans globals,finalCode.trans entryCode,finalDomain.trans domain,finalTx,supported,
    typePost,countPost,available,?_,⟨allocatedMemory.1.trans finalMemory.1,allocatedMemory.2.trans finalMemory.2⟩⟩
  rw [clock] at remaining
  exact Nat.le_trans remaining (Nat.sub_le _ _)

#print axioms transaction_allocated_parsing_returned_reserved_contract_state
end InitECandidate.Runtime
