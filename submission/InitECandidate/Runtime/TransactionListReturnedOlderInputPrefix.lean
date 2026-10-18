import InitECandidate.Runtime.RlpSlicesReturnedDeclarationOlderInputPrefix
import InitECandidate.Runtime.TransactionListSource
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem transaction_list_returned_older_input_prefix {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (tag pointer length total scratch frame array : BitVec 64) (ceiling inputLimit : Nat)
    (topLocal : state.locals.lookup (ofString "top") = some
      (.rStruct [.val (.word tag),.val (.word pointer),.val (.word length),.val (.word total)]))
    (noWrap : pointer.toNat + length.toNat < 2^64) (lengthBound : length.toNat ≤ inputLimit)
    (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word array)))
    (arrayBound : array.toNat ≤ 33806089496) (countLimit : inputLimit * 16 < 2^64)
    (heapArena : ∀ address : BitVec 64, array.toNat ≤ address.toNat → address.toNat < 33806089496 → state.memaddrs address)
    (budget : length.toNat * ((2 * length.toNat + 1) * 15 + 19) + length.toNat * 12 + 4 ≤ state.clock)
    (older olderCount input inputLength : BitVec 64)
    (valid : RlpSliceInputPrefix state older input inputLength olderCount.toNat)
    (before : older.toNat + olderCount.toNat * 16 ≤ array.toNat)
    (arrayBeforeFrame : array.toNat ≤ frame.toNat)
    (finalValue : ValueHOL 64)
    (run : evaluateHOLFiniteState state (transactionAt 12) = (some (.returned finalValue),post)) :
    ∃ (count : BitVec 64) (entry output : PanSemStateFiniteExact 64 F),
      count.toNat ≤ length.toNat ∧ RlpSlicePrefix entry array count.toNat ∧
      RlpSliceInputPrefix entry older input inputLength olderCount.toNat ∧
      entry.locals.lookup (ofString "lst") = some (.rStruct [.val (.word array),.val (.word count)]) ∧
      (∀ name, name ≠ ofString "lst" → entry.locals.lookup name = state.locals.lookup name) ∧
      evaluateHOLFiniteState entry (transactionAt 13) = (some (.returned finalValue),output) ∧ post.memory = output.memory := by
  rw [source_transaction_list] at run
  obtain ⟨count,ready,output,bounded,locals,readable,retained,tail,scope⟩ :=
    evaluate_rlpSlices_returned_declaration_older_input_prefix state post (ofString "lst") (transactionAt 13)
      transactionListArguments pointer length scratch frame array ceiling inputLimit
      (transaction_list_arguments state tag pointer length total topLocal) noWrap lengthBound limitBound
      scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena heap arrayBound countLimit heapArena budget
      older olderCount input inputLength valid before arrayBeforeFrame finalValue run
  let entry := setVarHOLFinite (ofString "lst") (.rStruct [.val (.word array),.val (.word count)]) ready
  have newReadable : RlpSlicePrefix entry array count.toNat := by
    intro index inside
    obtain ⟨pointer,length,item⟩ := readable index inside
    exact ⟨pointer,length,RlpSliceEntry.after_frame ready entry array index pointer length item rfl rfl rfl⟩
  have oldRetained : RlpSliceInputPrefix entry older input inputLength olderCount.toNat := by
    intro index inside
    obtain ⟨pointer,length,item⟩ := retained index inside
    exact ⟨pointer,length,RlpSliceInputEntry.after_frame ready entry older index pointer length input inputLength item rfl rfl rfl⟩
  refine ⟨count,entry,output,bounded,newReadable,oldRetained,?_,?_,tail,?_⟩
  · simp [entry,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  · intro name different
    simp [entry,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different,locals]
  · rw [scope]

#print axioms transaction_list_returned_older_input_prefix
end InitECandidate.Runtime
