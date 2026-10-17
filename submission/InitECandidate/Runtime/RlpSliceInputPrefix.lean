import InitECandidate.Runtime.RlpSliceInputSpan
import InitECandidate.Runtime.RlpSlicesPrefix
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Every filled slice entry is readable and wholly inside the original input. -/
def RlpSliceInputPrefix {F : Type} (state : PanSemStateFiniteExact 64 F)
    (array input inputLength : BitVec 64) (filled : Nat) : Prop :=
  ∀ slot : BitVec 64, slot.toNat < filled → ∃ pointer length,
    RlpSliceInputEntry state array slot pointer length input inputLength

theorem rlpSliceInputPrefix_empty {F : Type} (state : PanSemStateFiniteExact 64 F)
    (array input inputLength : BitVec 64) : RlpSliceInputPrefix state array input inputLength 0 := by
  intro slot inside
  omega

/-- Later real filling stores retain the input bounds of each earlier entry. -/
theorem rlpSlices_step_preserves_input_entry {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (array index pointer offset : BitVec 64)
    (arrayLocal : state.locals.lookup (ofString "arr") = some (.val (.word array)))
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (offsetLocal : state.locals.lookup (ofString "off") = some (.val (.word offset)))
    (domain0 : state.memaddrs (array + index * 16#64))
    (domain8 : state.memaddrs (array + index * 16#64 + 8#64))
    (earlier count oldPointer oldLength input inputLength : BitVec 64)
    (ordered : earlier.toNat < index.toNat) (inside : index.toNat < count.toNat)
    (fits : array.toNat + count.toNat * 16 ≤ 2^64)
    (old : RlpSliceInputEntry state array earlier oldPointer oldLength input inputLength)
    (code : state.code = originalRuntimeCode) (ticks : 11 ≤ state.clock)
    (run : evaluateHOLFiniteState state rlpSlicesStep = (none,post)) :
    RlpSliceInputEntry post array earlier oldPointer oldLength input inputLength := by
  obtain ⟨_,_,retained⟩ := rlpSlices_step_preserves_earlier state post array index pointer offset
    arrayLocal indexLocal pointerLocal offsetLocal domain0 domain8 earlier count oldPointer oldLength
    ordered inside fits old.readable code ticks run
  exact ⟨retained,old.startsWithin,old.endsWithin,old.noWrap⟩

/-- A bounded current entry extends the input-bounded prefix through a real iteration. -/
theorem rlpSlices_step_extends_input_prefix {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (array index pointer offset : BitVec 64)
    (arrayLocal : state.locals.lookup (ofString "arr") = some (.val (.word array)))
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (offsetLocal : state.locals.lookup (ofString "off") = some (.val (.word offset)))
    (domain0 : state.memaddrs (array + index * 16#64))
    (domain8 : state.memaddrs (array + index * 16#64 + 8#64))
    (count input inputLength : BitVec 64) (inside : index.toNat < count.toNat)
    (fits : array.toNat + count.toNat * 16 ≤ 2^64)
    (filledPrefix : RlpSliceInputPrefix state array input inputLength index.toNat)
    (current : ∃ p n, RlpSliceInputEntry post array index p n input inputLength)
    (code : state.code = originalRuntimeCode) (ticks : 11 ≤ state.clock)
    (run : evaluateHOLFiniteState state rlpSlicesStep = (none,post)) :
    RlpSliceInputPrefix post array input inputLength (index + 1).toNat := by
  intro slot filled
  have progress := rlpSlices_index_progress index count inside
  by_cases same : slot = index
  · subst slot; exact current
  · have earlier : slot.toNat < index.toNat := by
      have different : slot.toNat ≠ index.toNat := fun equal => same (BitVec.eq_of_toNat_eq equal)
      omega
    obtain ⟨p,n,entry⟩ := filledPrefix slot earlier
    exact ⟨p,n,rlpSlices_step_preserves_input_entry state post array index pointer offset arrayLocal indexLocal pointerLocal
      offsetLocal domain0 domain8 slot count p n input inputLength earlier inside fits entry code ticks run⟩

#print axioms rlpSlices_step_preserves_input_entry
#print axioms rlpSlices_step_extends_input_prefix
end InitECandidate.Runtime
