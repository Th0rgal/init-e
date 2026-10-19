import InitECandidate.Runtime.Sha256PairLastBlockMemory
import InitECandidate.Runtime.StoreBE64AlignedMemory
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem shaPair_length_returned_memory {F : Type} (state post : PanSemStateFiniteExact 64 F)
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
    (code : state.code = originalRuntimeCode) (budget : 34 ≤ state.clock)
    (run : evaluateHOLFiniteState state (shaPairAt 6) = (some (.returned value),post)) :
    post.memory watched = state.memory watched := by
  have shifted : (accelerator + (88#64)).toNat = accelerator.toNat + 88 := by
    rw [BitVec.toNat_add_of_lt (by change accelerator.toNat + 88 < 2 ^ 64; omega)]; rfl
  have lengthAligned : (accelerator + (88#64)).toNat % 8 = 0 := by rw [shifted]; omega
  have separate : watched ≠ accelerator + (88#64) := by
    intro same
    have natural := congrArg BitVec.toNat same
    rw [shifted] at natural
    rcases accelOutside with before | after <;> omega
  rw [source_shaPair_length] at run
  let arguments : List (ExpHOL 64) := [shaPairAccelOffset 88,.const 512]
  obtain ⟨middle,normal,tail⟩ := seq_returned_of_nonreturning_first
    (fun v => evaluate_discard_call_no_return state (ofString "st_be64") arguments v) run
  have frame := storeBE64_aligned_call_normal_memory state middle arguments (accelerator + (88#64)) 512 watched
    (by simp [arguments,shaPairAccelOffset,evalListHOLExact,evalHOLExact,atAccel,
      wordOpHOL,wordOp,valueIsWord,valueWord]) code lengthAligned separate normal
  have globals := storeBE64_call_globals_frame arguments state code
  have meta' := evaluateHOLFiniteState_metadata state (.call (some (none,none)) (ofString "st_be64") arguments)
  have clocks := evaluate_storeBE64_call_bounded state none arguments code (by omega)
  rw [normal] at globals meta' clocks
  have locals := evaluate_avoidsLocal_flowing (ofString "out")
    (.call (some (none,none)) (ofString "st_be64") arguments) rfl state
    (by rw [normal]; exact Or.inl rfl)
  rw [normal] at locals
  have suffix := shaPair_lastBlock_returned_memory middle post pointer accelerator out watched value
    (by rw [globals]; exact atPointer) (by rw [globals]; exact atAccel) (locals.trans atOut)
    accelAligned outAligned accelFits pointerFits outFits accelOutside pointerOutside outOutside
    (meta'.1.trans code) (by dsimp only at clocks; omega) tail
  exact suffix.trans frame

#print axioms shaPair_length_returned_memory
end InitECandidate.Runtime
