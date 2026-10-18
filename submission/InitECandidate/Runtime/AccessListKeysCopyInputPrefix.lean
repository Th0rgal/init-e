import InitECandidate.Runtime.AccessListKeysCopyMemory
import InitECandidate.Runtime.BlobHashesCopySeparation
import InitECandidate.Runtime.RlpSliceInputPrefixBelow
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem access_keys_copy_normal_input_prefix {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (buffer index source array count input inputLength : BitVec 64)
    (bufferLocal : state.locals.lookup (ofString "keys") = some (.val (.word buffer)))
    (indexLocal : state.locals.lookup (ofString "j") = some (.val (.word index)))
    (sourceLocal : state.locals.lookup (ofString "k") = some (.val (.word source)))
    (code : state.code = originalRuntimeCode)
    (valid : RlpSliceInputPrefix state array input inputLength count.toNat)
    (before : array.toNat + count.toNat * 16 ≤ buffer.toNat)
    (aligned : buffer.toNat % 8 = 0)
    (fits : buffer.toNat + index.toNat * 32 + 32 ≤ 2^64)
    (budget : 16 ≤ state.clock)
    (run : evaluateHOLFiniteState state accessKeysCopy = (none,post)) :
    RlpSliceInputPrefix post array input inputLength count.toNat := by
  have metadata := evaluateHOLFiniteState_metadata state accessKeysCopy
  rw [run] at metadata
  apply valid.after_memory_below state post array count input inputLength buffer before metadata.2.1
  intro watched below
  exact access_keys_copy_normal_memory state post buffer index source watched bufferLocal indexLocal sourceLocal code
    (fun offset inside => (blobHashes_copy_cells_after_buffer buffer index watched aligned fits below offset inside).1)
    (fun offset inside => (blobHashes_copy_cells_after_buffer buffer index watched aligned fits below offset inside).2) budget run

#print axioms access_keys_copy_normal_input_prefix
end InitECandidate.Runtime
