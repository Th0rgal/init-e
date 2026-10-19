import InitECandidate.Runtime.Sha256PairFinishMemory
import InitECandidate.Runtime.Sha256BlockMemory
import InitECandidate.Runtime.Sha256GlobalsFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem shaPair_lastBlock_returned_memory {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer accelerator out watched : BitVec 64) (value : ValueHOL 64)
    (atPointer : state.globals.lookup (ofString "sha_st") = some (.val (.word pointer)))
    (atAccel : state.globals.lookup (ofString "sha_accel") = some (.val (.word accelerator)))
    (atOut : state.locals.lookup (ofString "out") = some (.val (.word out)))
    (accelAligned : accelerator.toNat % 8 = 0) (outAligned : out.toNat % 8 = 0)
    (accelFits : accelerator.toNat + 96 ≤ 33806089496) (pointerFits : pointer.toNat + 64 ≤ 33806089496)
    (outFits : out.toNat + 32 ≤ 33806089496)
    (accelOutside : watched.toNat < accelerator.toNat ∨ accelerator.toNat + 96 ≤ watched.toNat)
    (pointerOutside : watched.toNat < pointer.toNat ∨ pointer.toNat + 64 ≤ watched.toNat)
    (outOutside : watched.toNat < out.toNat ∨ out.toNat + 32 ≤ watched.toNat)
    (code : state.code = originalRuntimeCode) (budget : 30 ≤ state.clock)
    (run : evaluateHOLFiniteState state (shaPairAt 7) = (some (.returned value),post)) :
    post.memory watched = state.memory watched := by
  rw [source_shaPair_block_last] at run
  obtain ⟨middle,normal,tail⟩ := seq_returned_of_nonreturning_first
    (fun v => evaluate_discard_call_no_return state (ofString "sha256_block") shaPairBlockArguments v) run
  have frame := shaBlock_call_normal_memory state middle shaPairBlockArguments pointer
    (accelerator + (32#64)) accelerator watched
    (by simp [shaPairBlockArguments,shaPairAccelOffset,evalListHOLExact,evalHOLExact,atPointer,atAccel,
      wordOpHOL,wordOp,valueIsWord,valueWord]) atAccel accelAligned accelFits pointerFits
    accelOutside pointerOutside code budget normal
  have globals := shaBlock_call_globals_frame shaPairBlockArguments state code
  have meta' := evaluateHOLFiniteState_metadata state (.call (some (none,none)) (ofString "sha256_block") shaPairBlockArguments)
  rw [normal] at globals meta'
  have locals := evaluate_avoidsLocal_flowing (ofString "out")
    (.call (some (none,none)) (ofString "sha256_block") shaPairBlockArguments) rfl state
    (by rw [normal]; exact Or.inl rfl)
  rw [normal] at locals
  have suffix := shaPair_finish_returned_memory middle post pointer out watched value
    (by rw [globals]; exact atPointer) (locals.trans atOut) outAligned outFits outOutside
    (meta'.1.trans code) tail
  exact suffix.trans frame

#print axioms shaPair_lastBlock_returned_memory
end InitECandidate.Runtime
