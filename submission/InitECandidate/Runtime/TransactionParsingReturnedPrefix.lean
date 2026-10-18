import InitECandidate.Runtime.TransactionTypeParseReturnedPrefix
import InitECandidate.Runtime.TransactionParsingScopesReturned
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem transaction_parsing_returned_input_prefix {F : Type} (state post : PanSemStateFiniteExact 64 F)
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
    (budget : length.toNat * ((2 * length.toNat + 1) * 15 + 19) + 92634 ≤ state.clock)
    (array count input inputLength : BitVec 64)
    (valid : RlpSliceInputPrefix state array input inputLength count.toNat)
    (before : array.toNat + count.toNat * 16 ≤ frame.toNat)
    (value : ValueHOL 64)
    (run : evaluateHOLFiniteState state (transactionAt 6) = (some (.returned value),post)) :
    ∃ middle output : PanSemStateFiniteExact 64 F,
      evaluateHOLFiniteState middle (transactionAt 10) = (some (.returned value),output) ∧
      RlpSliceInputPrefix middle array input inputLength count.toNat ∧ post.memory = output.memory := by
  obtain ⟨entry,output,bodyRun,memory,globals,entryCode,domain,clock,locals,finalMemory⟩ :=
    transaction_parsing_scopes_returned state post value run
  have entryValid : RlpSliceInputPrefix entry array input inputLength count.toNat := by
    intro index inside
    obtain ⟨pointer,length,item⟩ := valid index inside
    exact ⟨pointer,length,RlpSliceInputEntry.after_frame state entry array index pointer length input inputLength item domain
      (by rw [memory]) (by rw [memory])⟩
  obtain ⟨middle,_,tail,retained⟩ := transaction_type_parse_returned_input_prefix entry output pointer length scratch frame ceiling inputLimit
    ((locals _ (by decide) (by decide) (by decide)).trans pointerLocal)
    ((locals _ (by decide) (by decide) (by decide)).trans lengthLocal)
    positive inputRange lengthBound limitBound
    (by rw [globals]; exact scratchGlobal) (by rw [globals]; exact frameGlobal)
    (entryCode.trans code) orderedFrame framePositive scratchBelow
    (by intro address low high; rw [domain]; exact arena address low high)
    (by rw [clock]; exact budget) array count input inputLength entryValid before value bodyRun
  exact ⟨middle,output,tail,retained,finalMemory⟩

#print axioms transaction_parsing_returned_input_prefix
end InitECandidate.Runtime
