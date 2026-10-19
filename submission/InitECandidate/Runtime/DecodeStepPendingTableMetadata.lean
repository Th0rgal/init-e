import InitECandidate.Runtime.DecodeStepListRecordMetadata
import InitECandidate.Runtime.RlpSliceInputPrefixAbove
import InitECandidate.Runtime.RlpSliceInputPrefixBetween
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def DecoderPushedTable {F : Type} (s : PanSemStateFiniteExact 64 F)
    (record pointer length input inputLength : BitVec 64) (ceiling : Nat) : Prop :=
  ∃ array count stage heap : BitVec 64,
    (stage=1 ∧ count=2 ∨ stage=2 ∧ count=17) ∧
    DecoderRecordFields s record array pointer length stage ∧
    RlpSliceInputPrefix s array input inputLength count.toNat ∧
    ceiling ≤ array.toNat ∧ array.toNat+count.toNat*16 ≤ heap.toNat ∧
    s.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)) ∧
    heap.toNat ≤ 33806089496 ∧ heap.toNat%8=0

theorem decode_step_list_push_returned_table {F : Type} (s post : PanSemStateFiniteExact 64 F)
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
    DecoderPushedTable post record pointer length input inputLength ceiling := by
  obtain ⟨stage,kind,fields⟩ := decode_step_list_push_returned_fields s post array count input inputLength heap scratch frame
    pointer length ceiling inputLimit atArray atPointer atLength atSlices table inputBound limitCap atHeap heapBound
    aligned tableBefore arrayAbove scratchGlobal frameGlobal code ordered framePositive scratchBelow arena budget record run
  obtain ⟨nextHeap,heapPost,growth,capped,finishAligned,memory⟩ := decode_step_list_returned_heap_contract s post
    array count input inputLength heap scratch frame pointer length ceiling inputLimit atArray atPointer atLength
    atSlices table inputBound limitCap atHeap heapBound aligned tableBefore arrayAbove scratchGlobal frameGlobal
    code ordered framePositive scratchBelow arena budget _ run
  have metadata := evaluateHOLFiniteState_metadata s (decodeStepAt 6)
  rw [run] at metadata
  have tablePost := RlpSliceInputPrefix.after_memory_between s post array count input inputLength heap ceiling table
    arrayAbove tableBefore metadata.2.1 (fun watched before above => memory watched above before)
  exact ⟨array,count,stage,nextHeap,kind,fields,tablePost,arrayAbove,by omega,heapPost,capped,finishAligned⟩

theorem DecoderPushedTable.after_frame {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (record pointer length input inputLength : BitVec 64) (ceiling : Nat)
    (valid : DecoderPushedTable s record pointer length input inputLength ceiling)
    (memory : post.memory=s.memory) (globals : post.globals=s.globals) (domain : post.memaddrs=s.memaddrs) :
    DecoderPushedTable post record pointer length input inputLength ceiling := by
  obtain ⟨array,count,stage,heap,kind,fields,table,above,extent,heapGlobal,capped,aligned⟩ := valid
  refine ⟨array,count,stage,heap,kind,?_,?_,above,extent,?_,capped,aligned⟩
  · simpa [DecoderRecordFields,memory] using fields
  · intro index inside
    obtain ⟨p,n,entry⟩ := table index inside
    exact ⟨p,n,entry.after_frame s post array index p n input inputLength domain (congrFun memory _) (congrFun memory _)⟩
  · rw [globals]; exact heapGlobal

#print axioms DecoderPushedTable.after_frame
#print axioms decode_step_list_push_returned_table
end InitECandidate.Runtime
