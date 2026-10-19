import InitECandidate.Runtime.Sha256BlockPackedMemory
import InitECandidate.Runtime.Sha256BlockCopyMemory
import InitECandidate.Runtime.PanDiscardCallNormalResult
import InitECandidate.Runtime.PanTwoWordLookup
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem shaBlock_body_returned_memory {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer block accelerator watched : BitVec 64) (value : ValueHOL 64)
    (atPointer : state.locals.lookup (ofString "stp") = some (.val (.word pointer)))
    (atBlock : state.locals.lookup (ofString "blk") = some (.val (.word block)))
    (atAccel : state.globals.lookup (ofString "sha_accel") = some (.val (.word accelerator)))
    (aligned : accelerator.toNat % 8 = 0)
    (accelFits : accelerator.toNat + 96 ≤ 33806089496) (pointerFits : pointer.toNat + 64 ≤ 33806089496)
    (accelOutside : watched.toNat < accelerator.toNat ∨ accelerator.toNat + 96 ≤ watched.toNat)
    (pointerOutside : watched.toNat < pointer.toNat ∨ pointer.toNat + 64 ≤ watched.toNat)
    (code : state.code = originalRuntimeCode) (budget : 29 ≤ state.clock)
    (run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_sha256_block) = (some (.returned value),post)) :
    post.memory watched = state.memory watched := by
  rw [sourceFunctionBody_eq_structural] at run
  change evaluateHOLFiniteState state (shaBlockAt 0) = _ at run
  rw [source_shaBlock_copy_check] at run
  obtain ⟨middle,normal,tail⟩ := seq_returned_of_nonreturning_first
    (fun v => evaluate_noDirectReturnWhile _ (by decide) state v) run
  have frame := shaBlockCopy_normal_memory state middle block accelerator watched atBlock atAccel aligned
    accelFits accelOutside code (by omega) normal
  have keep (key : MlS) : middle.locals.lookup key = state.locals.lookup key := by
    have locals := evaluate_avoidsLocal_flowing key shaBlockCopyCheck rfl state (by rw [normal]; exact Or.inl rfl)
    simpa only [normal] using locals
  have globals := shaBlockCopy_globals state code
  have meta' := evaluateHOLFiniteState_metadata state shaBlockCopyCheck
  rw [normal] at globals meta'
  exact (shaBlockCounter_suffix_returned_memory middle post pointer accelerator watched value ((keep _).trans atPointer)
    (by rw [globals]; exact atAccel) aligned accelFits pointerFits accelOutside pointerOutside (meta'.1.trans code) tail).trans frame

/-- Actual original block hashing changes memory only inside the 64-byte
state and 96-byte accelerator buffers, for every normally returned FFI. -/
theorem shaBlock_call_normal_memory {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (arguments : List (ExpHOL 64)) (pointer block accelerator watched : BitVec 64)
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments =
      some [.val (.word pointer),.val (.word block)])
    (atAccel : state.globals.lookup (ofString "sha_accel") = some (.val (.word accelerator)))
    (aligned : accelerator.toNat % 8 = 0)
    (accelFits : accelerator.toNat + 96 ≤ 33806089496) (pointerFits : pointer.toNat + 64 ≤ 33806089496)
    (accelOutside : watched.toNat < accelerator.toNat ∨ accelerator.toNat + 96 ≤ watched.toNat)
    (pointerOutside : watched.toNat < pointer.toNat ∨ pointer.toNat + 64 ≤ watched.toNat)
    (code : state.code = originalRuntimeCode) (budget : 30 ≤ state.clock)
    (run : evaluateHOLFiniteState state (.call (some (none,none)) (ofString "sha256_block") arguments) = (none,post)) :
    post.memory watched = state.memory watched := by
  have installed : state.code.lookup (ofString "sha256_block") =
      some ([(ofString "stp",.one),(ofString "blk",.one)],sourceFunctionBody Guest.guestFn_sha256_block,.one) := by
    rw [code]; exact originalRuntimeCode_sha256Block_lookup
  have lookup := pan_two_word_lookup state.code.lookup (ofString "sha256_block") (ofString "stp") (ofString "blk")
    (sourceFunctionBody Guest.guestFn_sha256_block) pointer block (by decide) installed
  obtain ⟨value,output,bodyRun,_,postEq⟩ := evaluate_discardCall_normal_result state post (ofString "sha256_block")
    .one arguments _ _ _ args lookup run
  rw [postEq]
  let entry := callEntryStateHOLFinite state
    ((HolFiniteMapExact.empty.update (ofString "stp",.val (.word pointer))).update (ofString "blk",.val (.word block)))
  exact shaBlock_body_returned_memory entry output pointer block accelerator watched value
    (by simp (config := {decide := true}) [entry,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    (by simp [entry,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    atAccel aligned accelFits pointerFits accelOutside pointerOutside code (by change 29 ≤ state.clock - 1; omega) bodyRun

#print axioms shaBlock_body_returned_memory
#print axioms shaBlock_call_normal_memory
end InitECandidate.Runtime
