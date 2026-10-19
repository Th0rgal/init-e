import InitECandidate.Runtime.HtrBytesListBound
import InitECandidate.Runtime.MerkleizeMemory
import InitECandidate.Runtime.MerkleHeapGlobals
import InitECandidate.Runtime.MixInLengthMemory
import InitECandidate.Runtime.HeapReleaseMemory
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem htrBytesList_tail_returned_memory {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer accelerator zeroHashes chunk roots n length limit heap out mark watched : BitVec 64) (value : ValueHOL 64)
    (atPointer : state.globals.lookup (ofString "sha_st") = some (.val (.word pointer)))
    (atAccel : state.globals.lookup (ofString "sha_accel") = some (.val (.word accelerator)))
    (atChunk : state.globals.lookup (ofString "ssz_len_chunk") = some (.val (.word chunk)))
    (atLength : state.locals.lookup (ofString "n") = some (.val (.word length)))
    (atLimit : state.locals.lookup (ofString "limit_chunks") = some (.val (.word limit)))
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
    (code : state.code = originalRuntimeCode) (budget : htrBytesListTailCost ≤ state.clock)
    (run : evaluateHOLFiniteState state (htrBytesListAt 2) = (some (.returned value),post)) :
    post.memory watched = state.memory watched := by
  let arguments : List (ExpHOL 64) :=
    [.rfield 0 (.var .local (ofString "pk")),.rfield 1 (.var .local (ofString "pk")),
      .var .local (ofString "limit_chunks"),.var .local (ofString "out")]
  have args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments =
      some [.val (.word roots),.val (.word n),.val (.word limit),.val (.word out)] := by
    rw [evalListHOLFinite_eq_toExact]
    simp [arguments,evalListHOLExact,evalHOLExact,atPacked,atLimit,atOut]
  have firstBudget : merkleBodyCost + 1 ≤ state.clock := (Nat.le_add_right _ 157).trans budget
  rw [source_htrBytesList_tail] at run
  obtain ⟨middle,normal,tail⟩ := seq_returned_of_nonreturning_first
    (fun v => evaluate_discard_call_no_return state (ofString "merkleize") arguments v) run
  have frame := merkleize_call_normal_memory state middle arguments pointer accelerator heap zeroHashes limit out n roots watched
    args atPointer atAccel atZero hh heapFits small outAligned outFits outOutside heapAligned heapBefore
    accelAligned accelFits pointerFits accelOutside pointerOutside code firstBudget normal
  have globals := merkleize_call_normal_globals state middle arguments roots n limit out heap args hh code normal
  have keep (key : MlS) : middle.locals.lookup key = state.locals.lookup key := by
    have kept := evaluate_avoidsLocal_flowing key (.call (some (none,none)) (ofString "merkleize") arguments) rfl state
      (by rw [normal]; exact Or.inl rfl)
    simpa only [normal] using kept
  have metadata := evaluateHOLFiniteState_metadata state (.call (some (none,none)) (ofString "merkleize") arguments)
  have spent := (runBounded_merkleize_call state none arguments roots n limit out heap args small hh heapFits code firstBudget).1
  rw [normal] at metadata spent
  have afterBudget : 157 ≤ middle.clock := Nat.le_of_add_le_add_right
    ((show 157 + (merkleBodyCost + 1) ≤ state.clock from by simpa only [htrBytesListTailCost,Nat.add_comm] using budget).trans spent)
  obtain ⟨released,releaseRun,finish⟩ := seq_returned_of_nonreturning_first
    (fun v => evaluate_discard_call_no_return middle (ofString "heap_release") [.var .local (ofString "mark")] v) tail
  have releaseFrame := heapRelease_call_normal_memory middle released (.var .local (ofString "mark")) mark
    (metadata.1.trans code) (by simp [evalListHOLExact,evalHOLExact,keep,atMark]) releaseRun
  have releaseRelation := normalRel_discard_call heapGlobalsRel_preorder (ofString "heap_release") [.var .local (ofString "mark")] _ _ _
    originalRuntimeCode_heap_release_lookup heapRelease_returned_heapGlobals
  have releaseGlobals := normalRel_apply releaseRelation (X := middle) (by rw [releaseRun]; exact Or.inl rfl) (metadata.1.trans code)
  have releaseMeta := evaluateHOLFiniteState_metadata middle
    (.call (some (none,none)) (ofString "heap_release") [.var .local (ofString "mark")])
  have releaseSpent := (RunBounded.ofProg (state := middle) (ProgBounded.call vmBound_heap_release none [.var .local (ofString "mark")])
    (metadata.1.trans code) (by exact (Nat.le_add_right _ 156).trans afterBudget)).1
  rw [releaseRun] at releaseGlobals releaseMeta releaseSpent
  have releaseKeep (key : MlS) : released.locals.lookup key = middle.locals.lookup key := by
    have kept := evaluate_avoidsLocal_flowing key
      (.call (some (none,none)) (ofString "heap_release") [.var .local (ofString "mark")]) rfl middle
      (by rw [releaseRun]; exact Or.inl rfl)
    simpa only [releaseRun] using kept
  let mixArgs : List (ExpHOL 64) := [.var .local (ofString "out"),.var .local (ofString "n"),.var .local (ofString "out")]
  have mixValues : evalListHOLFinite released (h := fun a => Classical.propDecidable (released.memaddrs a)) mixArgs =
      some [.val (.word out),.val (.word length),.val (.word out)] := by
    simp [mixArgs,evalListHOLExact,evalHOLExact,releaseKeep,keep,atOut,atLength]
  obtain ⟨finished,mixRun,finishRun⟩ := seq_returned_of_nonreturning_first
    (fun v => evaluate_discard_call_no_return released (ofString "mix_in_length") mixArgs v) finish
  have mixBudget : 139 ≤ released.clock := by
    change middle.clock ≤ released.clock + 1 at releaseSpent
    omega
  have mixFrame := mixLength_call_normal_memory released finished mixArgs pointer accelerator chunk out out length watched mixValues
    (by rw [releaseGlobals _ (by decide),globals]; exact atPointer)
    (by rw [releaseGlobals _ (by decide),globals]; exact atAccel)
    (by rw [releaseGlobals _ (by decide),globals]; exact atChunk)
    accelAligned chunkAligned outAligned accelFits pointerFits chunkFits outFits
    accelOutside pointerOutside chunkOutside outOutside (releaseMeta.1.trans (metadata.1.trans code)) mixBudget mixRun
  obtain ⟨finishMemory,_,_,_⟩ := return_const_state finished post 0 value finishRun
  rw [finishMemory]
  exact mixFrame.trans ((congrFun releaseFrame watched).trans frame)

#print axioms htrBytesList_tail_returned_memory
end InitECandidate.Runtime
