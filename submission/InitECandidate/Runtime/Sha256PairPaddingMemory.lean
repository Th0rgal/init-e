import InitECandidate.Runtime.Sha256PairLengthMemory
import InitECandidate.Runtime.AllocationSeparation
import InitECandidate.Runtime.ByteStoreMemoryFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem shaPair_padding_returned_memory {F : Type} (state post : PanSemStateFiniteExact 64 F)
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
    (run : evaluateHOLFiniteState state (shaPairAt 5) = (some (.returned value),post)) :
    post.memory watched = state.memory watched := by
  have interval := hashOccupancy_aligned_interval accelerator (96#64) (32#64) accelAligned
    (by change accelerator.toNat + 96 ≤ 2 ^ 64; omega) (by decide)
  have separate : watched ≠ panByteAlignHOL (accelerator + (32#64)) := by
    intro same
    have natural := congrArg BitVec.toNat same
    change accelerator.toNat ≤ _ ∧ _ < accelerator.toNat + 96 at interval
    rcases accelOutside with before | after <;> omega
  have control := evaluate_storeByte_control_frame state (shaPairAccelOffset 32) (.const 128)
  rw [source_shaPair_padding] at run
  obtain ⟨middle,normal,tail⟩ := seq_returned_of_nonreturning_first
    (fun v => by rcases control.1 with h | h <;> rw [h] <;> simp) run
  have frame := evaluate_storeByte_memory_frame state (shaPairAccelOffset 32) (.const 128)
    (accelerator + (32#64)) watched
    (by simp [shaPairAccelOffset,evalHOLExact,evalListHOLExact,atAccel,wordOpHOL,wordOp,valueIsWord,valueWord]) separate
  rw [normal] at frame control
  obtain ⟨_,clock,locals,globals,installed,_,_⟩ := control
  have suffix := shaPair_length_returned_memory middle post pointer accelerator out watched value
    (by rw [globals]; exact atPointer) (by rw [globals]; exact atAccel)
    (by rw [locals]; exact atOut) accelAligned outAligned accelFits pointerFits outFits
    accelOutside pointerOutside outOutside (installed.trans code) (by rw [clock]; exact budget) tail
  exact suffix.trans frame

#print axioms shaPair_padding_returned_memory
end InitECandidate.Runtime
