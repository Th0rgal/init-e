import InitECandidate.Runtime.Sha256UnpackReturnedMemory
import InitECandidate.Runtime.ExternalCallMemoryFrame
import InitECandidate.Runtime.ExternalCallNoReturn
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem shaBlockExternal_suffix_returned_memory {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (index pointer accelerator watched : BitVec 64) (value : ValueHOL 64)
    (atIndex : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (atPointer : state.locals.lookup (ofString "stp") = some (.val (.word pointer)))
    (atAccel : state.globals.lookup (ofString "sha_accel") = some (.val (.word accelerator)))
    (aligned : accelerator.toNat % 8 = 0) (accelFits : accelerator.toNat + 96 ≤ 33806089496)
    (pointerFits : pointer.toNat + 64 ≤ 33806089496)
    (accelOutside : watched.toNat < accelerator.toNat ∨ accelerator.toNat + 96 ≤ watched.toNat)
    (pointerOutside : watched.toNat < pointer.toNat ∨ pointer.toNat + 64 ≤ watched.toNat)
    (code : state.code = originalRuntimeCode)
    (run : evaluateHOLFiniteState state (shaBlockAt 3) = (some (.returned value),post)) :
    post.memory watched = state.memory watched := by
  rw [source_shaBlock_external] at run
  obtain ⟨middle,normal,tail⟩ := seq_returned_of_nonreturning_first
    (fun v => evaluate_external_no_return state _ _ _ _ _ v) run
  have frame := evaluate_external_interval_frame state (ofString "sha256f")
    (.var .global (ofString "sha_accel")) (.const 0) (.var .global (ofString "sha_accel")) (.const 96)
    accelerator 0 accelerator 96 watched
    (by simp [evalHOLExact,atAccel]) rfl (by simp [evalHOLExact,atAccel]) rfl aligned accelFits accelOutside
  rw [normal] at frame
  have keep (key : MlS) : middle.locals.lookup key = state.locals.lookup key := by
    have localFrame := evaluate_avoidsLocal_flowing key
      (.extCall (ofString "sha256f") (.var .global (ofString "sha_accel")) (.const 0)
        (.var .global (ofString "sha_accel")) (.const 96)) rfl state (by rw [normal]; exact Or.inl rfl)
    simpa only [normal] using localFrame
  have meta' := evaluateHOLFiniteState_metadata state
    (.extCall (ofString "sha256f") (.var .global (ofString "sha_accel")) (.const 0)
      (.var .global (ofString "sha_accel")) (.const 96))
  rw [normal] at meta'
  exact (shaBlockReset_suffix_returned_memory middle post index pointer watched value
    ((keep _).trans atIndex) ((keep _).trans atPointer) pointerFits pointerOutside (meta'.1.trans code) tail).trans frame

#print axioms shaBlockExternal_suffix_returned_memory
end InitECandidate.Runtime
