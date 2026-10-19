import InitECandidate.Runtime.DecodeStepBranchPlacedMetadata
import InitECandidate.Runtime.DecodeStepPendingTableMetadata
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
theorem decode_step_list_push_returned_placed_table {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (array count input inputLength heap scratch frame pointer length : BitVec 64) (ceiling inputLimit : Nat)
    (atArray : s.locals.lookup (ofString "arr") = some (.val (.word array)))
    (atPointer : s.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (atLength : s.locals.lookup (ofString "n") = some (.val (.word length)))
    (atSlices : s.locals.lookup (ofString "sl") = some (.rStruct [.val (.word array),.val (.word count)]))
    (table : RlpSliceInputPrefix s array input inputLength count.toNat)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitCap : inputLimit ≤ 134217712)
    (atHeap : s.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (heapBound : heap.toNat ≤ 33806089496) (aligned : heap.toNat % 8 = 0)
    (tableBefore : array.toNat + count.toNat*16 ≤ heap.toNat) (arrayAbove : ceiling ≤ array.toNat)
    (scratchGlobal : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : s.code = originalRuntimeCode) (ordered : frame ≤ scratch)
    (framePositive : 0 < frame.toNat) (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → s.memaddrs address)
    (budget : decodeStepTwoCaseCost inputLimit ≤ s.clock) (record : BitVec 64)
    (run : evaluateHOLFiniteState s (decodeStepAt 6) =
      (some (.returned (.rStruct [.val (.word (1 : BitVec 64)),.val (.word record)])),post)) :
    DecoderPlacedPushedTable post record pointer length input inputLength ceiling array.toNat := by
  have tableResult := decode_step_list_push_returned_table s post array count input inputLength heap scratch frame pointer length
    ceiling inputLimit atArray atPointer atLength atSlices table inputBound limitCap atHeap heapBound aligned tableBefore arrayAbove
    scratchGlobal frameGlobal code ordered framePositive scratchBelow arena budget record run
  refine ⟨tableResult,?_⟩
  intro atStage
  obtain ⟨stage,kind,fields⟩ := decode_step_list_push_returned_fields s post array count input inputLength heap scratch frame pointer length
    ceiling inputLimit atArray atPointer atLength atSlices table inputBound limitCap atHeap heapBound aligned tableBefore arrayAbove
    scratchGlobal frameGlobal code ordered framePositive scratchBelow arena budget record run
  have stageEq : stage=2 := HolWordLab.word.inj (fields.1.symm.trans atStage)
  subst stage
  have countEq : count=17 := by
    rcases kind with ⟨impossible,_⟩ | ⟨_,same⟩
    · cases impossible
    · exact same
  subst count
  rw [evaluate_decode_step_seventeen s array atSlices] at run
  have identity := push_pair_record_eq record _ (decode_step_branch_construction_returned_pointer s post scratch frame _
    code (by unfold decodeStepTwoCaseCost at budget; omega) scratchGlobal frameGlobal ordered run)
  rw [identity]
  exact decode_step_branch_construction_returned_placement s post heap scratch frame array pointer length atHeap heapBound aligned
    (by simpa using tableBefore) atArray atPointer atLength scratchGlobal frameGlobal ordered code
    (by unfold decodeStepTwoCaseCost at budget; omega) _ run

#print axioms decode_step_list_push_returned_placed_table
end InitECandidate.Runtime
