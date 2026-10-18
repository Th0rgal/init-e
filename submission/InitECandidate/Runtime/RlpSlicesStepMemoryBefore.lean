import InitECandidate.Runtime.RlpSlicesStepMemoryFrame
import InitECandidate.Runtime.RlpSlicesMemoryInvariant
import InitECandidate.Runtime.RlpSliceAddressSeparation
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- The actual filling iteration preserves every earlier word, including
an outer slice array allocated before the current inner array. -/
theorem rlpSlices_step_memory_before {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer count array : BitVec 64) (valid : RlpSlicesMemoryWitness state pointer count array)
    (inside : valid.control.index.toNat < count.toNat) (ticks : 11 ≤ state.clock)
    (run : evaluateHOLFiniteState state rlpSlicesStep = (none,post))
    (watched : BitVec 64) (before : watched.toNat < array.toNat) :
    post.memory watched = state.memory watched := by
  have frame := rlpSlices_step_memory_frame state post array valid.control.index pointer valid.control.offset
    valid.arrayLocal valid.control.indexLocal valid.control.pointerLocal valid.control.offsetLocal
    (valid.domain _ inside).1 (valid.domain _ inside).2 valid.control.code ticks run
  have cell0 := rlpSlice_cell_toNat array valid.control.index count 0 inside (by decide) valid.fits
  have cell8 := rlpSlice_cell_toNat array valid.control.index count 8 inside (by decide) valid.fits
  apply frame watched
  · intro same
    have equal := congrArg BitVec.toNat same
    simp only [BitVec.add_zero,Nat.add_zero] at cell0
    rw [cell0] at equal
    omega
  · intro same
    have equal := congrArg BitVec.toNat same
    rw [cell8] at equal
    omega

#print axioms rlpSlices_step_memory_before
end InitECandidate.Runtime
