import InitECandidate.Runtime.Sha256PairFirstBlockMemory
import InitECandidate.Runtime.MemcpyCallMemory
import InitECandidate.Runtime.MemcpyIntervalFrame
import InitECandidate.Runtime.MemcpyCallBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem shaPair_copyB_returned_memory {F : Type} (state post : PanSemStateFiniteExact 64 F)
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
    (code : state.code = originalRuntimeCode) (budget : 101 ≤ state.clock)
    (run : evaluateHOLFiniteState state (shaPairAt 2) = (some (.returned value),post)) :
    post.memory watched = state.memory watched := by
  have shifted : (accelerator + (64#64)).toNat = accelerator.toNat + 64 := by
    rw [BitVec.toNat_add_of_lt (by change accelerator.toNat + 64 < 2 ^ 64; omega)]; rfl
  have destinationAligned : (accelerator + (64#64)).toNat % 8 = 0 := by rw [shifted]; omega
  have destinationFits : (accelerator + (64#64)).toNat + (32#64).toNat ≤ 33806089496 := by
    change _ + 32 ≤ _; rw [shifted]; omega
  have destinationOutside : watched.toNat < (accelerator + (64#64)).toNat ∨
      (accelerator + (64#64)).toNat + (32#64).toNat ≤ watched.toNat := by
    change watched.toNat < _ ∨ _ + 32 ≤ watched.toNat
    rw [shifted]
    rcases accelOutside with before | after
    · left; omega
    · right; omega
  have separate := memcpy_interval_separate (accelerator + (64#64)) (32#64) watched
    destinationAligned destinationFits destinationOutside
  let arguments : List (ExpHOL 64) := [shaPairAccelOffset 64,.var .local (ofString "input_b"),.const 32]
  have args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments =
      some [.val (.word (accelerator + (64#64))),.val (.word inputB),.val (.word (32#64))] := by
    simp [arguments,shaPairAccelOffset,evalListHOLExact,evalHOLExact,atAccel,atB,wordOpHOL,wordOp,valueIsWord,valueWord]
  rw [source_shaPair_copy_b] at run
  obtain ⟨middle,normal,tail⟩ := seq_returned_of_nonreturning_first
    (fun v => evaluate_discard_call_no_return state (ofString "memcpy") arguments v) run
  have frame := memcpy_call_normal_memory state middle arguments (accelerator + (64#64)) inputB (32#64)
    watched args code (fun offset inside => (separate offset inside).1)
    (fun offset inside => (separate offset inside).2) (by decide) (by change 16 ≤ state.clock; omega) normal
  have globals := memcpy_call_globals_frame arguments state code
  have meta' := evaluateHOLFiniteState_metadata state (.call (some (none,none)) (ofString "memcpy") arguments)
  have clocks := evaluate_memcpy_call_bounded state arguments (accelerator + (64#64)) inputB (32#64) args code
    (by decide) (by change 16 ≤ state.clock; omega)
  rw [normal] at globals meta' clocks
  have keep (key : MlS) : middle.locals.lookup key = state.locals.lookup key := by
    have locals := evaluate_avoidsLocal_flowing key (.call (some (none,none)) (ofString "memcpy") arguments)
      rfl state (by rw [normal]; exact Or.inl rfl)
    simpa only [normal] using locals
  have suffix := shaPair_firstBlock_returned_memory middle post pointer accelerator out watched value
    (by rw [globals]; exact atPointer) (by rw [globals]; exact atAccel) ((keep _).trans atOut)
    accelAligned outAligned accelFits pointerFits outFits accelOutside pointerOutside outOutside
    (meta'.1.trans code) (by change state.clock ≤ middle.clock + 16 ∧ _ at clocks; omega) tail
  exact suffix.trans frame

#print axioms shaPair_copyB_returned_memory
end InitECandidate.Runtime
