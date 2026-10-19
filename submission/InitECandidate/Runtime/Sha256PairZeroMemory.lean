import InitECandidate.Runtime.Sha256PairPaddingMemory
import InitECandidate.Runtime.MemzeroNormalFrame
import InitECandidate.Runtime.MemzeroCallBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem shaPair_zero_returned_memory {F : Type} (state post : PanSemStateFiniteExact 64 F)
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
    (code : state.code = originalRuntimeCode) (budget : 55 ≤ state.clock)
    (run : evaluateHOLFiniteState state (shaPairAt 4) = (some (.returned value),post)) :
    post.memory watched = state.memory watched := by
  have shifted : (accelerator + (32#64)).toNat = accelerator.toNat + 32 := by
    rw [BitVec.toNat_add_of_lt (by change accelerator.toNat + 32 < 2 ^ 64; omega)]; rfl
  have destinationAligned : (accelerator + (32#64)).toNat % 8 = 0 := by rw [shifted]; omega
  have destinationFits : (accelerator + (32#64)).toNat + (64#64).toNat ≤ 33806089496 := by
    change _ + 64 ≤ _; rw [shifted]; omega
  have destinationOutside : watched.toNat < (accelerator + (32#64)).toNat ∨
      (accelerator + (32#64)).toNat + (64#64).toNat ≤ watched.toNat := by
    change watched.toNat < _ ∨ _ + 64 ≤ watched.toNat
    rw [shifted]
    rcases accelOutside with before | after
    · left; omega
    · right; omega
  let arguments : List (ExpHOL 64) := [shaPairAccelOffset 32,.const 64]
  have args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments =
      some [.val (.word (accelerator + (32#64))),.val (.word (64#64))] := by
    simp [arguments,shaPairAccelOffset,evalListHOLExact,evalHOLExact,atAccel,wordOpHOL,wordOp,valueIsWord,valueWord]
  rw [source_shaPair_zero] at run
  obtain ⟨middle,normal,tail⟩ := seq_returned_of_nonreturning_first
    (fun v => evaluate_discard_call_no_return state (ofString "memzero") arguments v) run
  obtain ⟨frame,locals⟩ := memzero_call_normal_memory state middle arguments (accelerator + (32#64))
    (64#64) watched args code destinationAligned destinationFits destinationOutside normal
  have globals := memzero_call_globals_frame arguments state code
  have meta' := evaluateHOLFiniteState_metadata state (.call (some (none,none)) (ofString "memzero") arguments)
  have clocks := evaluate_memzero_call_bounded state arguments (accelerator + (32#64)) (64#64) args code
    (by decide) (by change 21 ≤ state.clock; omega)
  rw [normal] at globals meta' clocks
  have suffix := shaPair_padding_returned_memory middle post pointer accelerator out watched value
    (by rw [globals]; exact atPointer) (by rw [globals]; exact atAccel)
    (by rw [locals]; exact atOut) accelAligned outAligned accelFits pointerFits outFits
    accelOutside pointerOutside outOutside (meta'.1.trans code)
    (by change state.clock ≤ middle.clock + 21 ∧ _ at clocks; omega) tail
  exact suffix.trans frame

#print axioms shaPair_zero_returned_memory
end InitECandidate.Runtime
