import InitECandidate.Runtime.MixInLengthSuffixMemory
import InitECandidate.Runtime.MemzeroNormalFrame
import InitECandidate.Runtime.MemzeroCallBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem mixLength_body_returned_memory {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer accelerator chunk out root length watched : BitVec 64) (value : ValueHOL 64)
    (atPointer : state.globals.lookup (ofString "sha_st") = some (.val (.word pointer)))
    (atAccel : state.globals.lookup (ofString "sha_accel") = some (.val (.word accelerator)))
    (atChunk : state.globals.lookup (ofString "ssz_len_chunk") = some (.val (.word chunk)))
    (atOut : state.locals.lookup (ofString "out") = some (.val (.word out)))
    (atRoot : state.locals.lookup (ofString "root") = some (.val (.word root)))
    (atLength : state.locals.lookup (ofString "len") = some (.val (.word length)))
    (accelAligned : accelerator.toNat % 8 = 0) (chunkAligned : chunk.toNat % 8 = 0)
    (outAligned : out.toNat % 8 = 0)
    (accelFits : accelerator.toNat + 96 ≤ 33806089496) (pointerFits : pointer.toNat + 64 ≤ 33806089496)
    (chunkFits : chunk.toNat + 32 ≤ 33806089496) (outFits : out.toNat + 32 ≤ 33806089496)
    (accelOutside : watched.toNat < accelerator.toNat ∨ accelerator.toNat + 96 ≤ watched.toNat)
    (pointerOutside : watched.toNat < pointer.toNat ∨ pointer.toNat + 64 ≤ watched.toNat)
    (chunkOutside : watched.toNat < chunk.toNat ∨ chunk.toNat + 32 ≤ watched.toNat)
    (outOutside : watched.toNat < out.toNat ∨ out.toNat + 32 ≤ watched.toNat)
    (code : state.code = originalRuntimeCode) (budget : 138 ≤ state.clock)
    (run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_mix_in_length) = (some (.returned value),post)) :
    post.memory watched = state.memory watched := by
  rw [sourceFunctionBody_eq_structural] at run
  change evaluateHOLFiniteState state (mixLengthAt 0) = _ at run
  rw [source_mixLength_zero] at run
  let arguments : List (ExpHOL 64) := [.var .global (ofString "ssz_len_chunk"),.const 32]
  have args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments =
      some [.val (.word chunk),.val (.word (32#64))] := by
    simp [arguments,evalListHOLExact,evalHOLExact,atChunk]
  obtain ⟨middle,normal,tail⟩ := seq_returned_of_nonreturning_first
    (fun v => evaluate_discard_call_no_return state (ofString "memzero") arguments v) run
  obtain ⟨frame,locals⟩ := memzero_call_normal_memory state middle arguments chunk (32#64) watched
    args code chunkAligned chunkFits chunkOutside normal
  have globals := memzero_call_globals_frame arguments state code
  have meta' := evaluateHOLFiniteState_metadata state (.call (some (none,none)) (ofString "memzero") arguments)
  have clocks := evaluate_memzero_call_bounded state arguments chunk (32#64) args code
    (by decide) (by change 16 ≤ state.clock; omega)
  rw [normal] at globals meta' clocks
  have suffix := mixLength_store_returned_memory middle post pointer accelerator chunk out root length watched value
    (by rw [globals]; exact atPointer) (by rw [globals]; exact atAccel) (by rw [globals]; exact atChunk)
    (by rw [locals]; exact atOut) (by rw [locals]; exact atRoot) (by rw [locals]; exact atLength)
    accelAligned chunkAligned outAligned accelFits pointerFits chunkFits outFits
    accelOutside pointerOutside chunkOutside outOutside (meta'.1.trans code)
    (by change state.clock ≤ middle.clock + 16 ∧ _ at clocks; omega) tail
  exact suffix.trans frame

theorem mixLength_call_normal_memory {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (arguments : List (ExpHOL 64)) (pointer accelerator chunk out root length watched : BitVec 64)
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments =
      some [.val (.word root),.val (.word length),.val (.word out)])
    (atPointer : state.globals.lookup (ofString "sha_st") = some (.val (.word pointer)))
    (atAccel : state.globals.lookup (ofString "sha_accel") = some (.val (.word accelerator)))
    (atChunk : state.globals.lookup (ofString "ssz_len_chunk") = some (.val (.word chunk)))
    (accelAligned : accelerator.toNat % 8 = 0) (chunkAligned : chunk.toNat % 8 = 0)
    (outAligned : out.toNat % 8 = 0)
    (accelFits : accelerator.toNat + 96 ≤ 33806089496) (pointerFits : pointer.toNat + 64 ≤ 33806089496)
    (chunkFits : chunk.toNat + 32 ≤ 33806089496) (outFits : out.toNat + 32 ≤ 33806089496)
    (accelOutside : watched.toNat < accelerator.toNat ∨ accelerator.toNat + 96 ≤ watched.toNat)
    (pointerOutside : watched.toNat < pointer.toNat ∨ pointer.toNat + 64 ≤ watched.toNat)
    (chunkOutside : watched.toNat < chunk.toNat ∨ chunk.toNat + 32 ≤ watched.toNat)
    (outOutside : watched.toNat < out.toNat ∨ out.toNat + 32 ≤ watched.toNat)
    (code : state.code = originalRuntimeCode) (budget : 139 ≤ state.clock)
    (run : evaluateHOLFiniteState state (.call (some (none,none)) (ofString "mix_in_length") arguments) = (none,post)) :
    post.memory watched = state.memory watched := by
  have installed : state.code.lookup (ofString "mix_in_length") =
      some ([(ofString "root",.one),(ofString "len",.one),(ofString "out",.one)],
        sourceFunctionBody Guest.guestFn_mix_in_length,.one) := by
    rw [code]; exact originalRuntimeCode_mixInLength_lookup
  have lookup := pan_three_word_lookup state.code.lookup (ofString "mix_in_length")
    (ofString "root") (ofString "len") (ofString "out")
    (sourceFunctionBody Guest.guestFn_mix_in_length) root length out (by decide) (by decide) (by decide) installed
  obtain ⟨returned,output,bodyRun,_,postEq⟩ := evaluate_discardCall_normal_result state post (ofString "mix_in_length")
    .one arguments _ _ _ args lookup run
  rw [postEq]
  let entry := callEntryStateHOLFinite state
    (((HolFiniteMapExact.empty.update (ofString "root",.val (.word root))).update
      (ofString "len",.val (.word length))).update (ofString "out",.val (.word out)))
  exact mixLength_body_returned_memory entry output pointer accelerator chunk out root length watched returned
    atPointer atAccel atChunk
    (by simp [entry,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    (by simp (config := {decide := true}) [entry,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    (by simp (config := {decide := true}) [entry,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    accelAligned chunkAligned outAligned accelFits pointerFits chunkFits outFits
    accelOutside pointerOutside chunkOutside outOutside code (by change 138 ≤ state.clock - 1; omega) bodyRun

#print axioms mixLength_body_returned_memory
#print axioms mixLength_call_normal_memory
end InitECandidate.Runtime
