import InitECandidate.Runtime.RlpSliceInputPrefix
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- A slice array bounded by a nested list is also bounded by the enclosing
original input, preserving its real readable cells and nonwrapping entries. -/
theorem RlpSliceInputPrefix.within_outer {F : Type} (state : PanSemStateFiniteExact 64 F)
    (array pointer length input inputLength : BitVec 64) (filled : Nat)
    (valid : RlpSliceInputPrefix state array pointer length filled)
    (starts : input.toNat ≤ pointer.toNat)
    (ends : pointer.toNat + length.toNat ≤ input.toNat + inputLength.toNat) :
    RlpSliceInputPrefix state array input inputLength filled := by
  intro slot inside
  obtain ⟨p,n,item⟩ := valid slot inside
  exact ⟨p,n,item.readable,Nat.le_trans starts item.startsWithin,Nat.le_trans item.endsWithin ends,item.noWrap⟩

#print axioms RlpSliceInputPrefix.within_outer
end InitECandidate.Runtime
