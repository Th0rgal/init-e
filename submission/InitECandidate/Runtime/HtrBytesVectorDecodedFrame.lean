import InitECandidate.Runtime.HtrBytesVectorMemory
import InitECandidate.Runtime.RlpSliceRecordFrame
import InitECandidate.Runtime.RlpSliceInputPrefixFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A vector hash preserves decoded metadata below its output and temporary heap,
provided the decoder data is above the SHA workspace. -/
theorem htrBytesVector_call_normal_decoded_frame {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (arguments : List (ExpHOL 64))
    (sha accelerator zeroHashes source length heap destination payload index pointer size array input inputLength : BitVec 64)
    (count : Nat)
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments =
      some [.val (.word source),.val (.word length),.val (.word destination)])
    (shaGlobal : state.globals.lookup (ofString "sha_st") = some (.val (.word sha)))
    (accelGlobal : state.globals.lookup (ofString "sha_accel") = some (.val (.word accelerator)))
    (zeroGlobal : state.globals.lookup (ofString "zero_hashes") = some (.val (.word zeroHashes)))
    (heapGlobal : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (entry : RlpSliceEntry state payload index pointer size) (indexBound : index.toNat ≤ 4)
    (slices : RlpSliceInputPrefix state array input inputLength count)
    (aligned : destination.toNat % 8 = 0) (fits : destination.toNat + 32 ≤ 33806089496)
    (recordBefore : payload.toNat + 72 < destination.toNat)
    (arrayBefore : array.toNat + count * 16 ≤ destination.toNat)
    (small : length.toNat ≤ 134217712)
    (heapAligned : heap.toNat % 8 = 0) (heapFits : heap.toNat ≤ 33806089496)
    (recordHeap : payload.toNat + 72 < heap.toNat) (arrayHeap : array.toNat + count * 16 ≤ heap.toNat)
    (accelAligned : accelerator.toNat % 8 = 0)
    (accelRecord : accelerator.toNat + 96 ≤ payload.toNat) (shaRecord : sha.toNat + 64 ≤ payload.toNat)
    (accelArray : accelerator.toNat + 96 ≤ array.toNat) (shaArray : sha.toNat + 64 ≤ array.toNat)
    (code : state.code = originalRuntimeCode) (budget : htrBytesVectorBodyCost + 1 ≤ state.clock)
    (run : evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htr_bytes_vector") arguments) = (none,post)) :
    RlpSliceEntry post payload index pointer size ∧ RlpSliceInputPrefix post array input inputLength count := by
  have frame (watched : BitVec 64) (before : watched.toNat < destination.toNat)
      (heapBefore : watched.toNat < heap.toNat)
      (accelBefore : accelerator.toNat + 96 ≤ watched.toNat) (shaBefore : sha.toNat + 64 ≤ watched.toNat) :
      post.memory watched = state.memory watched := by
    exact htrBytesVector_call_normal_memory state post arguments sha accelerator zeroHashes source length heap destination watched
      args shaGlobal accelGlobal zeroGlobal heapGlobal aligned fits (Or.inl before) small heapAligned heapFits heapBefore
      accelAligned (by omega) (by omega) (Or.inr accelBefore) (Or.inr shaBefore) code budget run
  have metadata := evaluateHOLFiniteState_metadata state (.call (some (none,none)) (ofString "htr_bytes_vector") arguments)
  rw [run] at metadata
  constructor
  · apply entry.after_record_frame state post payload index pointer size indexBound (by have := destination.isLt; omega) metadata.2.1
    intro watched lo hi
    exact frame watched (by omega) (by omega) (by omega) (by omega)
  · apply slices.after_interval_frame state post array input inputLength count (by have := destination.isLt; omega) metadata.2.1
    intro watched lo hi
    exact frame watched (by omega) (by omega) (by omega) (by omega)

#print axioms htrBytesVector_call_normal_decoded_frame
end InitECandidate.Runtime
