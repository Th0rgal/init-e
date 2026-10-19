import InitECandidate.Runtime.HtrBytesListPackMemory
import InitECandidate.Runtime.HeapMarkCall
import InitECandidate.Runtime.HtrBytesListCallBound
import InitECandidate.Runtime.PanDiscardCallNormalResult
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxHeartbeats 2000000

theorem htrBytesList_body_returned_memory {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer accelerator zeroHashes chunk p n limit heap out watched : BitVec 64) (value : ValueHOL 64)
    (atPointer : state.globals.lookup (ofString "sha_st") = some (.val (.word pointer)))
    (atAccel : state.globals.lookup (ofString "sha_accel") = some (.val (.word accelerator)))
    (atChunk : state.globals.lookup (ofString "ssz_len_chunk") = some (.val (.word chunk)))
    (atLimit : state.locals.lookup (ofString "limit_chunks") = some (.val (.word limit)))
    (atLength : state.locals.lookup (ofString "n") = some (.val (.word n)))
    (chunkAligned : chunk.toNat % 8 = 0) (chunkFits : chunk.toNat + 32 ≤ 33806089496)
    (chunkOutside : watched.toNat < chunk.toNat ∨ chunk.toNat + 32 ≤ watched.toNat)
    (atZero : state.globals.lookup (ofString "zero_hashes") = some (.val (.word zeroHashes)))
    (atInput : state.locals.lookup (ofString "p") = some (.val (.word p)))
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
    (code : state.code = originalRuntimeCode) (budget : htrBytesListBodyCost ≤ state.clock)
    (run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_htr_bytes_list) = (some (.returned value),post)) :
    post.memory watched = state.memory watched := by
  have enough : 1 ≤ state.clock := (Nat.le_add_right 1 _).trans budget
  obtain ⟨marked,_,clock,memory,globals,locals,installed,_,_,declaration⟩ :=
    evaluate_heapMark_call_and_declaration state heap code hh (by omega)
  rw [sourceFunctionBody_eq_structural] at run
  change evaluateHOLFiniteState state (htrBytesListAt 0) = _ at run
  rw [source_htrBytesList_mark,declaration] at run
  let next := setVarHOLFinite (ofString "mark") (.val (.word heap)) marked
  change (let output := evaluateHOLFiniteState next (htrBytesListAt 1);
    (output.1,{output.2 with locals := HolFiniteMapExact.resVarEq output.2.locals (ofString "mark",state.locals.lookup (ofString "mark"))})) =
      (some (.returned value),post) at run
  cases tailRun : evaluateHOLFiniteState next (htrBytesListAt 1) with
  | mk result inner =>
    rw [tailRun] at run
    obtain ⟨resultEq,postEq⟩ := Prod.mk.inj run
    change result = some (.returned value) at resultEq
    subst result
    have keep (key : MlS) (different : key ≠ ofString "mark") : next.locals.lookup key = state.locals.lookup key := by
      simp [next,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different,locals]
    have remaining : htrBytesListPackCost ≤ next.clock := by
      change _ ≤ marked.clock
      unfold htrBytesListBodyCost at budget
      omega
    have frame := htrBytesList_pack_returned_memory next inner pointer accelerator zeroHashes chunk p n limit heap out heap watched value
      (by change marked.globals.lookup _ = _; rw [globals]; exact atPointer)
      (by change marked.globals.lookup _ = _; rw [globals]; exact atAccel)
      (by change marked.globals.lookup _ = _; rw [globals]; exact atChunk)
      ((keep _ (by decide)).trans atLength)
      ((keep _ (by decide)).trans atLimit)
      (by simp [next,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
      chunkAligned chunkFits chunkOutside
      (by change marked.globals.lookup _ = _; rw [globals]; exact atZero)
      ((keep _ (by decide)).trans atInput)
      (by change marked.globals.lookup _ = _; rw [globals]; exact hh)
      ((keep _ (by decide)).trans atOut)
      outAligned outFits outOutside small heapAligned heapFits heapBefore accelAligned accelFits pointerFits
      accelOutside pointerOutside (installed.trans code) remaining tailRun
    rw [← postEq]
    exact frame.trans (congrFun memory watched)

#print axioms htrBytesList_body_returned_memory
theorem htrBytesList_call_normal_memory {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (arguments : List (ExpHOL 64)) (pointer accelerator zeroHashes chunk p n limit heap out watched : BitVec 64)
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments =
      some [.val (.word p),.val (.word n),.val (.word limit),.val (.word out)])
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
    (code : state.code = originalRuntimeCode) (budget : htrBytesListBodyCost + 1 ≤ state.clock)
    (run : evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htr_bytes_list") arguments) = (none,post)) :
    post.memory watched = state.memory watched := by
  have installed : state.code.lookup (ofString "htr_bytes_list") =
      some ([(ofString "p",.one),(ofString "n",.one),(ofString "limit_chunks",.one),(ofString "out",.one)],
        sourceFunctionBody Guest.guestFn_htr_bytes_list,.one) := by
    rw [code]; exact originalRuntimeCode_htr_bytes_list_lookup
  have lookup := pan_four_word_lookup state.code.lookup (ofString "htr_bytes_list")
    (ofString "p") (ofString "n") (ofString "limit_chunks") (ofString "out")
    (sourceFunctionBody Guest.guestFn_htr_bytes_list) p n limit out
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) installed
  obtain ⟨returned,output,bodyRun,_,scope⟩ := evaluate_discardCall_normal_result state post (ofString "htr_bytes_list")
    .one arguments _ _ _ args lookup run
  let entry := callEntryStateHOLFinite state
    ((((HolFiniteMapExact.empty.update (ofString "p",.val (.word p))).update (ofString "n",.val (.word n))).update
      (ofString "limit_chunks",.val (.word limit))).update (ofString "out",.val (.word out)))
  rw [scope]
  exact htrBytesList_body_returned_memory entry output pointer accelerator zeroHashes chunk p n limit heap out watched returned
    atPointer atAccel atChunk
    (by simp (config := {decide := true}) [entry,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    (by simp (config := {decide := true}) [entry,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    chunkAligned chunkFits chunkOutside atZero
    (by simp (config := {decide := true}) [entry,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]) hh
    (by simp [entry,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    outAligned outFits outOutside small heapAligned heapFits heapBefore accelAligned accelFits pointerFits
    accelOutside pointerOutside code (by change htrBytesListBodyCost ≤ state.clock - 1; exact Nat.le_sub_of_add_le budget) bodyRun

#print axioms htrBytesList_call_normal_memory
end InitECandidate.Runtime
