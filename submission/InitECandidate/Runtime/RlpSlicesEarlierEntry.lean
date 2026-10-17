import InitECandidate.Runtime.RlpSlicesStoredEntry
import InitECandidate.Runtime.RlpSliceAddressSeparation
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Actual slice updates establish the current entry and preserve every
specified earlier entry in a nonwrapping allocated array. -/
theorem evaluate_rlpSlices_updates_preserve_earlier {F : Type} (state : PanSemStateFiniteExact 64 F)
    (array index pointer offset total : BitVec 64)
    (arrayLocal : state.locals.lookup (ofString "arr") = some (.val (.word array)))
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (offsetLocal : state.locals.lookup (ofString "off") = some (.val (.word offset)))
    (totalLocal : state.locals.lookup (ofString "total") = some (.val (.word total)))
    (domain0 : state.memaddrs (array + index * 16#64))
    (domain8 : state.memaddrs (array + index * 16#64 + 8#64))
    (earlier count oldPointer oldLength : BitVec 64)
    (ordered : earlier.toNat < index.toNat) (inside : index.toNat < count.toNat)
    (fits : array.toNat + count.toNat * 16 ≤ 2^64)
    (old : RlpSliceEntry state array earlier oldPointer oldLength) :
    ∃ post, evaluateHOLFiniteState state rlpSlicesUpdates = (none,post) ∧
      RlpSliceEntry post array index (pointer + offset) total ∧
      RlpSliceEntry post array earlier oldPointer oldLength ∧ post.clock = state.clock := by
  obtain ⟨post,run,current,clock,domain,frame⟩ := evaluate_rlpSlices_updates_entry_frame state array index pointer offset total
    arrayLocal indexLocal pointerLocal offsetLocal totalLocal domain0 domain8
  have separate := fun left right leftBound rightBound =>
    rlpSlice_cells_separate array earlier index count left right ordered inside leftBound rightBound fits
  have preserved := RlpSliceEntry.after_frame state post array earlier oldPointer oldLength old domain
    (frame _ (by simpa only [BitVec.add_zero] using separate 0 0 (by decide) (by decide))
      (by simpa only [BitVec.add_zero] using separate 0 8 (by decide) (by decide)))
    (frame _ (by simpa only [BitVec.add_zero] using separate 8 0 (by decide) (by decide))
      (separate 8 8 (by decide) (by decide)))
  exact ⟨post,run,current,preserved,clock⟩

#print axioms evaluate_rlpSlices_updates_preserve_earlier
end InitECandidate.Runtime
