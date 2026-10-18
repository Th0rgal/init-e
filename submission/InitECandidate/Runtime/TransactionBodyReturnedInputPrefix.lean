import InitECandidate.Runtime.TransactionAllocatedParsingReturnedPrefix
import InitECandidate.Runtime.TransactionBodyReturnedAllocation
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem transaction_body_returned_input_prefix {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer length scratch frame tx : BitVec 64) (ceiling inputLimit : Nat)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (lengthLocal : state.locals.lookup (ofString "len") = some (.val (.word length)))
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
    (run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_decode_transaction_rlp) = (some (.returned value),post)) :
    ∃ middle output : PanSemStateFiniteExact 64 F,
      evaluateHOLFiniteState middle (transactionAt 10) = (some (.returned value),output) ∧
      RlpSliceInputPrefix middle array input inputLength count.toNat ∧ post.memory = output.memory := by
  obtain ⟨positive,entry,output,bodyRun,memory,globals,entryCode,domain,clock,locals,finalMemory⟩ :=
    transaction_body_returned_allocation state post length value lengthLocal run
  have retained : RlpSliceInputPrefix entry array input inputLength count.toNat := by
    intro index inside
    obtain ⟨pointer,length,item⟩ := valid index inside
    exact ⟨pointer,length,RlpSliceInputEntry.after_frame state entry array index pointer length input inputLength item domain
      (by rw [memory]) (by rw [memory])⟩
  obtain ⟨middle,final,tail,preserved,innerMemory⟩ := transaction_allocated_parsing_returned_input_prefix entry output
    pointer length scratch frame tx ceiling inputLimit
    ((locals _ (by decide)).trans pointerLocal) ((locals _ (by decide)).trans lengthLocal)
    positive inputRange lengthBound limitBound
    (by rw [globals]; exact scratchGlobal) (by rw [globals]; exact frameGlobal)
    (entryCode.trans code) orderedFrame framePositive scratchBelow
    (by intro address low high; rw [domain]; exact arena address low high)
    (by rw [globals]; exact heap) small aligned
    (by intro address low high; rw [domain]; exact txArena address low high)
    (by rw [clock]; exact budget) array count input inputLength retained before beforeTx value bodyRun
  exact ⟨middle,final,tail,preserved,finalMemory.trans innerMemory⟩

#print axioms transaction_body_returned_input_prefix
end InitECandidate.Runtime
