import InitECandidate.Runtime.TransactionInitializedParsingReturnedPrefix
import InitECandidate.Runtime.TransactionAllocationReturnedPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

private theorem parsing_reserve_after_allocation (clock cost : Nat) (budget : 402 + cost ≤ clock) :
    401 + cost ≤ clock - 1 := by omega

theorem transaction_allocated_parsing_returned_input_prefix {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer length scratch frame tx : BitVec 64) (ceiling inputLimit : Nat)
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
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word tx)))
    (small : tx.toNat + 400 ≤ 33806089496) (aligned : tx.toNat % 8 = 0)
    (txArena : ∀ address : BitVec 64, tx.toNat ≤ address.toNat → address.toNat < tx.toNat + 400 → state.memaddrs address)
    (budget : 402 + (length.toNat * ((2 * length.toNat + 1) * 15 + 19) + 92634) ≤ state.clock)
    (array count input inputLength : BitVec 64)
    (valid : RlpSliceInputPrefix state array input inputLength count.toNat)
    (before : array.toNat + count.toNat * 16 ≤ frame.toNat)
    (beforeTx : array.toNat + count.toNat * 16 ≤ tx.toNat)
    (value : ValueHOL 64)
    (run : evaluateHOLFiniteState state (transactionAt 2) = (some (.returned value),post)) :
    ∃ middle output : PanSemStateFiniteExact 64 F,
      evaluateHOLFiniteState middle (transactionAt 10) = (some (.returned value),output) ∧
      RlpSliceInputPrefix middle array input inputLength count.toNat ∧ post.memory = output.memory := by
  obtain ⟨entry,output,bodyRun,atTx,locals,memory,entryCode,domain,clock,globals,finalMemory⟩ :=
    transaction_allocation_returned_prefix state post tx value heap code (by omega) small aligned run
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
  obtain ⟨middle,final,tail,preserved,innerMemory⟩ := transaction_initialized_parsing_returned_input_prefix entry output
    pointer length scratch frame tx ceiling inputLimit
    ((locals _ (by decide)).trans pointerLocal) ((locals _ (by decide)).trans lengthLocal)
    positive inputRange lengthBound limitBound scratchEntry frameEntry (entryCode.trans code) orderedFrame framePositive scratchBelow
    (by intro address low high; rw [domain]; exact arena address low high) atTx small aligned
    (by intro address low high; rw [domain]; exact txArena address low high)
    (by rw [clock]; exact parsing_reserve_after_allocation _ _ budget)
    array count input inputLength retained before beforeTx value bodyRun
  exact ⟨middle,final,tail,preserved,finalMemory.trans innerMemory⟩

#print axioms transaction_allocated_parsing_returned_input_prefix
end InitECandidate.Runtime
