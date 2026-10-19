import InitECandidate.Runtime.ProgressiveMemory
import InitECandidate.Runtime.ProgressiveHeapGlobals
import InitECandidate.Runtime.HtrPlistChunksCallBound
import InitECandidate.Runtime.MixInLengthMemory
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem htrPlistChunks_body_returned_memory {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer accelerator zeroHashes chunk roots n length heap out watched : BitVec 64) (value : ValueHOL 64)
    (atPointer : state.globals.lookup (ofString "sha_st") = some (.val (.word pointer)))
    (atAccel : state.globals.lookup (ofString "sha_accel") = some (.val (.word accelerator)))
    (atChunk : state.globals.lookup (ofString "ssz_len_chunk") = some (.val (.word chunk)))
    (atLength : state.locals.lookup (ofString "len") = some (.val (.word length)))
    (chunkAligned : chunk.toNat % 8 = 0) (chunkFits : chunk.toNat + 32 ≤ 33806089496)
    (chunkOutside : watched.toNat < chunk.toNat ∨ chunk.toNat + 32 ≤ watched.toNat)
    (atZero : state.globals.lookup (ofString "zero_hashes") = some (.val (.word zeroHashes)))
    (hr : state.locals.lookup (ofString "roots") = some (.val (.word roots)))
    (hn : state.locals.lookup (ofString "n") = some (.val (.word n)))
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
    (code : state.code = originalRuntimeCode) (budget : htrPlistChunksCost ≤ state.clock)
    (run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_htr_plist_chunks) = (some (.returned value),post)) :
    post.memory watched = state.memory watched := by
  let progArgs : List (ExpHOL 64) := [.var .local (ofString "roots"),.var .local (ofString "n"),.var .local (ofString "out")]
  let mixArgs : List (ExpHOL 64) := [.var .local (ofString "out"),.var .local (ofString "len"),.var .local (ofString "out")]
  have source : sourceFunctionBody Guest.guestFn_htr_plist_chunks =
      .seq (.call (some (none,none)) (ofString "merkleize_progressive") progArgs)
        (.seq (.call (some (none,none)) (ofString "mix_in_length") mixArgs) (.return (.const 0))) := by
    rw [sourceFunctionBody_eq_structural]; rfl
  have args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) progArgs =
      some [.val (.word roots),.val (.word n),.val (.word out)] := by
    simp [progArgs,evalListHOLExact,evalHOLExact,hr,hn,atOut]
  have firstBudget : progressiveBodyCost + 1 ≤ state.clock := (Nat.le_add_right _ 156).trans budget
  rw [source] at run
  obtain ⟨middle,normal,tail⟩ := seq_returned_of_nonreturning_first
    (fun v => evaluate_discard_call_no_return state (ofString "merkleize_progressive") progArgs v) run
  have frame := progressive_call_normal_memory state middle progArgs pointer accelerator zeroHashes roots n heap out watched
    args atPointer atAccel atZero hh outAligned outFits outOutside small heapAligned heapFits heapBefore
    accelAligned accelFits pointerFits accelOutside pointerOutside code firstBudget normal
  have globals := progressive_call_normal_globals state middle progArgs roots n out heap args hh code normal
  have keep (key : MlS) : middle.locals.lookup key = state.locals.lookup key := by
    have kept := evaluate_avoidsLocal_flowing key (.call (some (none,none)) (ofString "merkleize_progressive") progArgs) rfl state
      (by rw [normal]; exact Or.inl rfl)
    simpa only [normal] using kept
  have metadata := evaluateHOLFiniteState_metadata state (.call (some (none,none)) (ofString "merkleize_progressive") progArgs)
  have spent := (runBounded_progressive_call state none progArgs roots n out heap args small hh heapFits code firstBudget).1
  rw [normal] at metadata spent
  have mixBudget : 139 ≤ middle.clock := by
    have remaining : 156 ≤ middle.clock := Nat.le_of_add_le_add_right
      ((show 156 + (progressiveBodyCost + 1) ≤ state.clock from by simpa only [htrPlistChunksCost,Nat.add_comm] using budget).trans spent)
    exact (by decide : 139 ≤ 156).trans remaining
  have mixValues : evalListHOLFinite middle (h := fun a => Classical.propDecidable (middle.memaddrs a)) mixArgs =
      some [.val (.word out),.val (.word length),.val (.word out)] := by
    simp [mixArgs,evalListHOLExact,evalHOLExact,keep,atOut,atLength]
  obtain ⟨finished,mixRun,finishRun⟩ := seq_returned_of_nonreturning_first
    (fun v => evaluate_discard_call_no_return middle (ofString "mix_in_length") mixArgs v) tail
  have mixFrame := mixLength_call_normal_memory middle finished mixArgs pointer accelerator chunk out out length watched mixValues
    (by rw [globals]; exact atPointer) (by rw [globals]; exact atAccel) (by rw [globals]; exact atChunk)
    accelAligned chunkAligned outAligned accelFits pointerFits chunkFits outFits
    accelOutside pointerOutside chunkOutside outOutside (metadata.1.trans code) mixBudget mixRun
  obtain ⟨memory,_,_,_⟩ := return_const_state finished post 0 value finishRun
  rw [memory]
  exact mixFrame.trans frame

#print axioms htrPlistChunks_body_returned_memory
theorem htrPlistChunks_call_normal_memory {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (arguments : List (ExpHOL 64)) (pointer accelerator zeroHashes chunk roots n length heap out watched : BitVec 64)
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments =
      some [.val (.word roots),.val (.word n),.val (.word length),.val (.word out)])
    (atPointer : state.globals.lookup (ofString "sha_st") = some (.val (.word pointer)))
    (atAccel : state.globals.lookup (ofString "sha_accel") = some (.val (.word accelerator)))
    (atChunk : state.globals.lookup (ofString "ssz_len_chunk") = some (.val (.word chunk)))
    (chunkAligned : chunk.toNat % 8 = 0) (chunkFits : chunk.toNat + 32 ≤ 33806089496)
    (chunkOutside : watched.toNat < chunk.toNat ∨ chunk.toNat + 32 ≤ watched.toNat)
    (atZero : state.globals.lookup (ofString "zero_hashes") = some (.val (.word zeroHashes)))
    (hh : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (outAligned : out.toNat % 8 = 0) (outFits : out.toNat + 32 ≤ 33806089496)
    (outOutside : watched.toNat < out.toNat ∨ out.toNat + 32 ≤ watched.toNat)
    (small : n.toNat ≤ 134217712)
    (heapAligned : heap.toNat % 8 = 0) (heapFits : heap.toNat ≤ 33806089496) (heapBefore : watched.toNat < heap.toNat)
    (accelAligned : accelerator.toNat % 8 = 0)
    (accelFits : accelerator.toNat + 96 ≤ 33806089496) (pointerFits : pointer.toNat + 64 ≤ 33806089496)
    (accelOutside : watched.toNat < accelerator.toNat ∨ accelerator.toNat + 96 ≤ watched.toNat)
    (pointerOutside : watched.toNat < pointer.toNat ∨ pointer.toNat + 64 ≤ watched.toNat)
    (code : state.code = originalRuntimeCode) (budget : htrPlistChunksCost + 1 ≤ state.clock)
    (run : evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htr_plist_chunks") arguments) = (none,post)) :
    post.memory watched = state.memory watched := by
  have installed : state.code.lookup (ofString "htr_plist_chunks") =
      some ([(ofString "roots",.one),(ofString "n",.one),(ofString "len",.one),(ofString "out",.one)],
        sourceFunctionBody Guest.guestFn_htr_plist_chunks,.one) := by
    rw [code]; exact originalRuntimeCode_htr_plist_chunks_lookup
  have lookup := pan_four_word_lookup state.code.lookup (ofString "htr_plist_chunks")
    (ofString "roots") (ofString "n") (ofString "len") (ofString "out")
    (sourceFunctionBody Guest.guestFn_htr_plist_chunks) roots n length out
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) installed
  obtain ⟨returned,output,bodyRun,_,scope⟩ := evaluate_discardCall_normal_result state post (ofString "htr_plist_chunks")
    .one arguments _ _ _ args lookup run
  let entry := callEntryStateHOLFinite state
    ((((HolFiniteMapExact.empty.update (ofString "roots",.val (.word roots))).update (ofString "n",.val (.word n))).update
      (ofString "len",.val (.word length))).update (ofString "out",.val (.word out)))
  rw [scope]
  exact htrPlistChunks_body_returned_memory entry output pointer accelerator zeroHashes chunk roots n length heap out watched returned
    atPointer atAccel atChunk
    (by simp (config := {decide := true}) [entry,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    chunkAligned chunkFits chunkOutside atZero
    (by simp (config := {decide := true}) [entry,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    (by simp (config := {decide := true}) [entry,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]) hh
    (by simp [entry,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    outAligned outFits outOutside small heapAligned heapFits heapBefore accelAligned accelFits pointerFits
    accelOutside pointerOutside code (by change htrPlistChunksCost ≤ state.clock - 1; exact Nat.le_sub_of_add_le budget) bodyRun

#print axioms htrPlistChunks_call_normal_memory
end InitECandidate.Runtime
