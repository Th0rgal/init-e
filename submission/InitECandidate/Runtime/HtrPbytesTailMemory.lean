import InitECandidate.Runtime.HtrPlistChunksMemory
import InitECandidate.Runtime.HtrPbytesBound
import InitECandidate.Runtime.HeapReleaseMemory
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem htrPbytes_tail_returned_memory {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer accelerator zeroHashes chunk roots n length heap out mark watched : BitVec 64) (value : ValueHOL 64)
    (atPointer : state.globals.lookup (ofString "sha_st") = some (.val (.word pointer)))
    (atAccel : state.globals.lookup (ofString "sha_accel") = some (.val (.word accelerator)))
    (atChunk : state.globals.lookup (ofString "ssz_len_chunk") = some (.val (.word chunk)))
    (atLength : state.locals.lookup (ofString "n") = some (.val (.word length)))
    (atMark : state.locals.lookup (ofString "mark") = some (.val (.word mark)))
    (chunkAligned : chunk.toNat % 8 = 0) (chunkFits : chunk.toNat + 32 ≤ 33806089496)
    (chunkOutside : watched.toNat < chunk.toNat ∨ chunk.toNat + 32 ≤ watched.toNat)
    (atZero : state.globals.lookup (ofString "zero_hashes") = some (.val (.word zeroHashes)))
    (atPacked : state.locals.lookup (ofString "pk") = some (.rStruct [.val (.word roots),.val (.word n)]))
    (hh : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (atOut : state.locals.lookup (ofString "out") = some (.val (.word out)))
    (outAligned : out.toNat % 8 = 0) (outFits : out.toNat + 32 ≤ 33806089496)
    (outOutside : watched.toNat < out.toNat ∨ out.toNat + 32 ≤ watched.toNat)
    (small : n.toNat ≤ 134217712)
    (heapAligned : heap.toNat % 8 = 0) (heapFits : heap.toNat ≤ 33806089496) (heapBefore : watched.toNat < heap.toNat)
    (accelAligned : accelerator.toNat % 8 = 0)
    (accelFits : accelerator.toNat + 96 ≤ 33806089496) (pointerFits : pointer.toNat + 64 ≤ 33806089496)
    (accelOutside : watched.toNat < accelerator.toNat ∨ accelerator.toNat + 96 ≤ watched.toNat)
    (pointerOutside : watched.toNat < pointer.toNat ∨ pointer.toNat + 64 ≤ watched.toNat)
    (code : state.code = originalRuntimeCode) (budget : htrPbytesTailCost ≤ state.clock)
    (run : evaluateHOLFiniteState state (htrPbytesAt 2) = (some (.returned value),post)) :
    post.memory watched = state.memory watched := by
  let arguments : List (ExpHOL 64) :=
    [.rfield 0 (.var .local (ofString "pk")),.rfield 1 (.var .local (ofString "pk")),
      .var .local (ofString "n"),.var .local (ofString "out")]
  have args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments =
      some [.val (.word roots),.val (.word n),.val (.word length),.val (.word out)] := by
    rw [evalListHOLFinite_eq_toExact]
    simp [arguments,evalListHOLExact,evalHOLExact,atPacked,atLength,atOut]
  have firstBudget : htrPlistChunksCost + 1 ≤ state.clock := (Nat.le_add_right _ 1).trans budget
  rw [source_htrPbytes_tail] at run
  obtain ⟨middle,normal,tail⟩ := seq_returned_of_nonreturning_first
    (fun v => evaluate_discard_call_no_return state (ofString "htr_plist_chunks") arguments v) run
  have frame := htrPlistChunks_call_normal_memory state middle arguments pointer accelerator zeroHashes chunk roots n length heap out watched
    args atPointer atAccel atChunk chunkAligned chunkFits chunkOutside atZero hh
    outAligned outFits outOutside small heapAligned heapFits heapBefore accelAligned accelFits pointerFits
    accelOutside pointerOutside code firstBudget normal
  have keepMark : middle.locals.lookup (ofString "mark") = some (.val (.word mark)) := by
    have kept := evaluate_avoidsLocal_flowing (ofString "mark") (.call (some (none,none)) (ofString "htr_plist_chunks") arguments)
      rfl state (by rw [normal]; exact Or.inl rfl)
    rw [normal] at kept
    exact kept.trans atMark
  have metadata := evaluateHOLFiniteState_metadata state (.call (some (none,none)) (ofString "htr_plist_chunks") arguments)
  rw [normal] at metadata
  obtain ⟨released,releaseRun,finishRun⟩ := seq_returned_of_nonreturning_first
    (fun v => evaluate_discard_call_no_return middle (ofString "heap_release") [.var .local (ofString "mark")] v) tail
  have releaseFrame := heapRelease_call_normal_memory middle released (.var .local (ofString "mark")) mark
    (metadata.1.trans code) (by simp [evalListHOLExact,evalHOLExact,keepMark]) releaseRun
  obtain ⟨finishMemory,_,_,_⟩ := return_const_state released post 0 value finishRun
  rw [finishMemory,releaseFrame]
  exact frame

#print axioms htrPbytes_tail_returned_memory
end InitECandidate.Runtime
