import InitECandidate.Runtime.RlpSlicesStoredEntry
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A readable slice entry whose byte interval lies inside the original input. -/
structure RlpSliceInputEntry {F : Type} (state : PanSemStateFiniteExact 64 F)
    (array index pointer length input inputLength : BitVec 64) : Prop where
  readable : RlpSliceEntry state array index pointer length
  startsWithin : input.toNat ≤ pointer.toNat
  endsWithin : pointer.toNat + length.toNat ≤ input.toNat + inputLength.toNat
  noWrap : pointer.toNat + length.toNat < 2^64

/-- A subinterval inside a nonwrapping input inherits its length bound. -/
theorem RlpSliceInputEntry.length_bound {F : Type} (state : PanSemStateFiniteExact 64 F)
    (array index pointer length input inputLength : BitVec 64)
    (valid : RlpSliceInputEntry state array index pointer length input inputLength) :
    length.toNat ≤ inputLength.toNat := by
  have lower := valid.startsWithin
  have upper := valid.endsWithin
  omega

/-- Bounded cursor/size arithmetic turns the actual slice-store result into
an input-span contract; no modular pointer wrap can hide an out-of-range end. -/
theorem rlpSliceInputEntry_of_cursor {F : Type} (state : PanSemStateFiniteExact 64 F)
    (array index input inputLength offset total : BitVec 64)
    (entry : RlpSliceEntry state array index (input + offset) total)
    (noWrap : input.toNat + inputLength.toNat < 2^64)
    (fits : offset.toNat + total.toNat ≤ inputLength.toNat) :
    RlpSliceInputEntry state array index (input + offset) total input inputLength := by
  have pointerNat : (input + offset).toNat = input.toNat + offset.toNat :=
    BitVec.toNat_add_of_lt (by omega)
  refine ⟨entry,?_,?_,?_⟩ <;> rw [pointerNat] <;> omega

/-- A memory frame retains both readability and the pure input-span bounds. -/
theorem RlpSliceInputEntry.after_frame {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (array index pointer length input inputLength : BitVec 64)
    (valid : RlpSliceInputEntry state array index pointer length input inputLength)
    (domain : post.memaddrs = state.memaddrs)
    (pointerFrame : post.memory (array + index * 16#64) = state.memory (array + index * 16#64))
    (lengthFrame : post.memory (array + index * 16#64 + 8#64) = state.memory (array + index * 16#64 + 8#64)) :
    RlpSliceInputEntry post array index pointer length input inputLength :=
  ⟨RlpSliceEntry.after_frame state post _ _ _ _ valid.readable domain pointerFrame lengthFrame,
    valid.startsWithin,valid.endsWithin,valid.noWrap⟩


/-- The original store/update block establishes a span-bounded concrete entry
whenever its cursor and item size fit within the input. -/
theorem evaluate_rlpSlices_updates_input_entry {F : Type} (state : PanSemStateFiniteExact 64 F)
    (array index pointer offset total : BitVec 64)
    (arrayLocal : state.locals.lookup (ofString "arr") = some (.val (.word array)))
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (offsetLocal : state.locals.lookup (ofString "off") = some (.val (.word offset)))
    (totalLocal : state.locals.lookup (ofString "total") = some (.val (.word total)))
    (domain0 : state.memaddrs (array + index * 16#64))
    (domain8 : state.memaddrs (array + index * 16#64 + 8#64))
    (inputLength : BitVec 64) (inputNoWrap : pointer.toNat + inputLength.toNat < 2^64)
    (itemFits : offset.toNat + total.toNat ≤ inputLength.toNat) :
    ∃ post, evaluateHOLFiniteState state rlpSlicesUpdates = (none,post) ∧
      RlpSliceInputEntry post array index (pointer + offset) total pointer inputLength ∧ post.clock = state.clock := by
  obtain ⟨post,run,entry,clock⟩ := evaluate_rlpSlices_updates_entry state array index pointer offset total
    arrayLocal indexLocal pointerLocal offsetLocal totalLocal domain0 domain8
  exact ⟨post,run,rlpSliceInputEntry_of_cursor post array index pointer inputLength offset total entry inputNoWrap itemFits,clock⟩

#print axioms evaluate_rlpSlices_updates_input_entry

#print axioms rlpSliceInputEntry_of_cursor
#print axioms RlpSliceInputEntry.length_bound
#print axioms RlpSliceInputEntry.after_frame
end InitECandidate.Runtime
