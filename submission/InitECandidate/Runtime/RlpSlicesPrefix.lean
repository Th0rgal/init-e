import InitECandidate.Runtime.RlpSlicesStepEntryFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Every filled slot in the prefix contains a readable pointer/length entry. -/
def RlpSlicePrefix {F : Type} (state : PanSemStateFiniteExact 64 F) (array : BitVec 64) (filled : Nat) : Prop :=
  ∀ index : BitVec 64, index.toNat < filled → ∃ pointer length, RlpSliceEntry state array index pointer length

theorem rlpSlicePrefix_empty {F : Type} (state : PanSemStateFiniteExact 64 F) (array : BitVec 64) :
    RlpSlicePrefix state array 0 := by
  intro index inside
  omega

/-- The actual normal iteration extends the readable prefix by one slot,
including the first iteration where no previous entry exists. -/
theorem rlpSlices_step_extends_prefix {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (array index pointer offset : BitVec 64)
    (arrayLocal : state.locals.lookup (ofString "arr") = some (.val (.word array)))
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (offsetLocal : state.locals.lookup (ofString "off") = some (.val (.word offset)))
    (domain0 : state.memaddrs (array + index * 16#64))
    (domain8 : state.memaddrs (array + index * 16#64 + 8#64))
    (count : BitVec 64) (inside : index.toNat < count.toNat)
    (fits : array.toNat + count.toNat * 16 ≤ 2^64)
    (filledPrefix : RlpSlicePrefix state array index.toNat)
    (code : state.code = originalRuntimeCode) (ticks : 11 ≤ state.clock)
    (run : evaluateHOLFiniteState state rlpSlicesStep = (none,post)) :
    RlpSlicePrefix post array (index + 1).toNat := by
  intro slot filled
  have progress := rlpSlices_index_progress index count inside
  by_cases same : slot = index
  · subst slot
    obtain ⟨total,entry⟩ := rlpSlices_step_establishes_entry state post array index pointer offset
      arrayLocal indexLocal pointerLocal offsetLocal domain0 domain8 code ticks run
    exact ⟨pointer + offset,total,entry⟩
  · have earlier : slot.toNat < index.toNat := by
      have different : slot.toNat ≠ index.toNat := fun equal => same (BitVec.eq_of_toNat_eq equal)
      omega
    obtain ⟨oldPointer,oldLength,entry⟩ := filledPrefix slot earlier
    obtain ⟨_,_,retained⟩ := rlpSlices_step_preserves_earlier state post array index pointer offset
      arrayLocal indexLocal pointerLocal offsetLocal domain0 domain8 slot count oldPointer oldLength earlier inside fits entry code ticks run
    exact ⟨oldPointer,oldLength,retained⟩

#print axioms rlpSlices_step_extends_prefix
end InitECandidate.Runtime
