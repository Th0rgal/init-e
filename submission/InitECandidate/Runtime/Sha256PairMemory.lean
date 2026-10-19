import InitECandidate.Runtime.Sha256PairCopyAMemory
import InitECandidate.Runtime.Sha256StateInitMemory
import InitECandidate.Runtime.VmFn_sha256_state_init
import InitECandidate.Runtime.OriginalSha256PairCode
import InitECandidate.Runtime.PanThreeWordLookup
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem shaPair_body_returned_memory {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer accelerator out inputA inputB watched : BitVec 64) (value : ValueHOL 64)
    (atPointer : state.globals.lookup (ofString "sha_st") = some (.val (.word pointer)))
    (atAccel : state.globals.lookup (ofString "sha_accel") = some (.val (.word accelerator)))
    (atOut : state.locals.lookup (ofString "out") = some (.val (.word out)))
    (atA : state.locals.lookup (ofString "input_a") = some (.val (.word inputA)))
    (atB : state.locals.lookup (ofString "input_b") = some (.val (.word inputB)))
    (accelAligned : accelerator.toNat % 8 = 0) (outAligned : out.toNat % 8 = 0)
    (accelFits : accelerator.toNat + 96 ≤ 33806089496) (pointerFits : pointer.toNat + 64 ≤ 33806089496)
    (outFits : out.toNat + 32 ≤ 33806089496)
    (accelOutside : watched.toNat < accelerator.toNat ∨ accelerator.toNat + 96 ≤ watched.toNat)
    (pointerOutside : watched.toNat < pointer.toNat ∨ pointer.toNat + 64 ≤ watched.toNat)
    (outOutside : watched.toNat < out.toNat ∨ out.toNat + 32 ≤ watched.toNat)
    (code : state.code = originalRuntimeCode) (budget : 118 ≤ state.clock)
    (run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_sha256_pair) = (some (.returned value),post)) :
    post.memory watched = state.memory watched := by
  rw [sourceFunctionBody_eq_structural] at run
  change evaluateHOLFiniteState state (shaPairAt 0) = _ at run
  rw [source_shaPair_init] at run
  let arguments : List (ExpHOL 64) := [.var .global (ofString "sha_st")]
  obtain ⟨middle,normal,tail⟩ := seq_returned_of_nonreturning_first
    (fun v => evaluate_discard_call_no_return state (ofString "sha256_state_init") arguments v) run
  have frame := shaStateInit_call_normal_memory state middle (.var .global (ofString "sha_st")) pointer watched
    (by simp [evalListHOLExact,evalHOLExact,atPointer]) code pointerFits pointerOutside normal
  have globals := shaStateInit_call_globals_frame arguments state code
  have meta' := evaluateHOLFiniteState_metadata state (.call (some (none,none)) (ofString "sha256_state_init") arguments)
  have clocks := vmBound_sha256_state_init.call_bounded state none arguments code (by omega)
  rw [normal] at globals meta' clocks
  have keep (key : MlS) : middle.locals.lookup key = state.locals.lookup key := by
    have locals := evaluate_avoidsLocal_flowing key (.call (some (none,none)) (ofString "sha256_state_init") arguments)
      rfl state (by rw [normal]; exact Or.inl rfl)
    simpa only [normal] using locals
  have suffix := shaPair_copyA_returned_memory middle post pointer accelerator out inputA inputB watched value
    (by rw [globals]; exact atPointer) (by rw [globals]; exact atAccel) ((keep _).trans atOut)
    ((keep _).trans atA) ((keep _).trans atB)
    accelAligned outAligned accelFits pointerFits outFits accelOutside pointerOutside outOutside
    (meta'.1.trans code) (by dsimp only at clocks; omega) tail
  exact suffix.trans frame

/-- Installed original SHA-pair calls preserve every word outside their three
write buffers; neither input slice needs an assumed readable-memory domain. -/
theorem shaPair_call_normal_memory {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (arguments : List (ExpHOL 64)) (pointer accelerator out inputA inputB watched : BitVec 64)
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments =
      some [.val (.word inputA),.val (.word inputB),.val (.word out)])
    (atPointer : state.globals.lookup (ofString "sha_st") = some (.val (.word pointer)))
    (atAccel : state.globals.lookup (ofString "sha_accel") = some (.val (.word accelerator)))
    (accelAligned : accelerator.toNat % 8 = 0) (outAligned : out.toNat % 8 = 0)
    (accelFits : accelerator.toNat + 96 ≤ 33806089496) (pointerFits : pointer.toNat + 64 ≤ 33806089496)
    (outFits : out.toNat + 32 ≤ 33806089496)
    (accelOutside : watched.toNat < accelerator.toNat ∨ accelerator.toNat + 96 ≤ watched.toNat)
    (pointerOutside : watched.toNat < pointer.toNat ∨ pointer.toNat + 64 ≤ watched.toNat)
    (outOutside : watched.toNat < out.toNat ∨ out.toNat + 32 ≤ watched.toNat)
    (code : state.code = originalRuntimeCode) (budget : 119 ≤ state.clock)
    (run : evaluateHOLFiniteState state (.call (some (none,none)) (ofString "sha256_pair") arguments) = (none,post)) :
    post.memory watched = state.memory watched := by
  have installed : state.code.lookup (ofString "sha256_pair") =
      some ([(ofString "input_a",.one),(ofString "input_b",.one),(ofString "out",.one)],
        sourceFunctionBody Guest.guestFn_sha256_pair,.one) := by
    rw [code]; exact originalRuntimeCode_sha256Pair_lookup
  have lookup := pan_three_word_lookup state.code.lookup (ofString "sha256_pair")
    (ofString "input_a") (ofString "input_b") (ofString "out")
    (sourceFunctionBody Guest.guestFn_sha256_pair) inputA inputB out (by decide) (by decide) (by decide) installed
  obtain ⟨returned,output,bodyRun,_,postEq⟩ := evaluate_discardCall_normal_result state post (ofString "sha256_pair")
    .one arguments _ _ _ args lookup run
  rw [postEq]
  let entry := callEntryStateHOLFinite state
    (((HolFiniteMapExact.empty.update (ofString "input_a",.val (.word inputA))).update
      (ofString "input_b",.val (.word inputB))).update (ofString "out",.val (.word out)))
  exact shaPair_body_returned_memory entry output pointer accelerator out inputA inputB watched returned
    atPointer atAccel
    (by simp [entry,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    (by simp (config := {decide := true}) [entry,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    (by simp (config := {decide := true}) [entry,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    accelAligned outAligned accelFits pointerFits outFits accelOutside pointerOutside outOutside code
    (by change 118 ≤ state.clock - 1; omega) bodyRun

#print axioms shaPair_body_returned_memory
#print axioms shaPair_call_normal_memory
end InitECandidate.Runtime
