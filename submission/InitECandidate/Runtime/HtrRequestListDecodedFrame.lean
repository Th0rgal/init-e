import InitECandidate.Runtime.HtrRequestListMemory
import InitECandidate.Runtime.RlpSliceRecordFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A request-list hash preserves any decoded field of an earlier five-entry
request record, so later list counts can still be used in the runtime bound. -/
theorem htrRequestList_call_normal_decoded_frame {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (arguments : List (ExpHOL 64))
    (sha accelerator zeroHashes chunk kind pointer count size heap out record index fieldPointer fieldLength : BitVec 64)
    (layout : ListHashMemoryLayout state sha accelerator zeroHashes chunk heap out record)
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments =
      some [.val (.word kind),.val (.word pointer),.val (.word count),.val (.word size),.val (.word out)])
    (entry : RlpSliceEntry state record index fieldPointer fieldLength) (indexBound : index.toNat ≤ 4)
    (recordHeap : record.toNat + 72 < heap.toNat) (recordOut : record.toNat + 72 < out.toNat)
    (shaRecord : sha.toNat + 64 ≤ record.toNat) (accelRecord : accelerator.toNat + 96 ≤ record.toNat)
    (chunkRecord : chunk.toNat + 32 ≤ record.toNat)
    (small : count.toNat ≤ 134217712) (budget : htrRequestListBodyCost count + 1 ≤ state.clock)
    (run : evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htr_request_list") arguments) = (none,post)) :
    RlpSliceEntry post record index fieldPointer fieldLength := by
  have metadata := evaluateHOLFiniteState_metadata state (.call (some (none,none)) (ofString "htr_request_list") arguments)
  rw [run] at metadata
  apply entry.after_record_frame state post record index fieldPointer fieldLength indexBound
    (by have := heap.isLt; omega) metadata.2.1
  intro watched lo hi
  have watchedLayout : ListHashMemoryLayout state sha accelerator zeroHashes chunk heap out watched :=
    ⟨⟨layout.atSha,layout.atAccel,layout.atZero,layout.atHeap,layout.outAligned,layout.outFits,Or.inl (by omega),
      layout.heapAligned,layout.heapFits,(by omega),layout.accelAligned,layout.accelFits,layout.shaFits,
      Or.inr (by omega),Or.inr (by omega),layout.code⟩,
      layout.atChunk,layout.chunkAligned,layout.chunkFits,Or.inr (by omega)⟩
  exact htrRequestList_call_normal_memory state post arguments sha accelerator zeroHashes chunk kind pointer count size heap out watched
    watchedLayout args small budget run

#print axioms htrRequestList_call_normal_decoded_frame
end InitECandidate.Runtime
