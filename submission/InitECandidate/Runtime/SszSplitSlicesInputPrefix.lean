import InitECandidate.Runtime.SszSplitVarListSlices
import InitECandidate.Runtime.RlpSliceInputPrefix
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- The SSZ array contract supplies the same concrete, input-bounded slice
predicate consumed by transaction and versioned-hash validation. -/
theorem sszSplitSlices_input_prefix {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer length first array count : BitVec 64)
    (domain : post.memaddrs = state.memaddrs)
    (inputFits : pointer.toNat + length.toNat < 2 ^ 64)
    (slices : SszSplitSlices state.memory state.memaddrs pointer length first array count post.memory) :
    RlpSliceInputPrefix post array pointer length count.toNat := by
  obtain ⟨off,cells,_⟩ := slices
  intro index inside
  obtain ⟨_,ordered,within,pointerDomain,pointerCell,lengthDomain,lengthCell⟩ := cells index inside
  have unsigned : off index ≤ sszSliceEnd off length count index := BitVec.not_lt.mp ordered
  have difference := BitVec.toNat_sub_of_le unsigned
  have totalFits : (off index).toNat + (sszSliceEnd off length count index - off index).toNat ≤ length.toNat := by
    rw [difference]
    change ¬ length.toNat < (sszSliceEnd off length count index).toNat at within
    change (off index).toNat ≤ (sszSliceEnd off length count index).toNat at unsigned
    omega
  have readable : RlpSliceEntry post array index (pointer + off index) (sszSliceEnd off length count index - off index) := by
    refine ⟨?_,?_,pointerCell,lengthCell⟩
    · rw [domain]; exact pointerDomain
    · rw [domain]; exact lengthDomain
  exact ⟨pointer + off index,sszSliceEnd off length count index - off index,
    rlpSliceInputEntry_of_cursor post array index pointer length (off index)
      (sszSliceEnd off length count index - off index) readable inputFits totalFits⟩

#print axioms sszSplitSlices_input_prefix
end InitECandidate.Runtime
