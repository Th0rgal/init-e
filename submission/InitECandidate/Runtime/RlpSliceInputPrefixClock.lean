import InitECandidate.Runtime.RlpSliceInputPrefix
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- Clock changes preserve the actual readable input-bounded slice prefix. -/
theorem RlpSliceInputPrefix.with_clock {F : Type} (state : PanSemStateFiniteExact 64 F)
    (array input inputLength : BitVec 64) (filled ticks : Nat)
    (valid : RlpSliceInputPrefix state array input inputLength filled) :
    RlpSliceInputPrefix {state with clock := ticks} array input inputLength filled := by
  intro slot inside
  obtain ⟨pointer,length,entry⟩ := valid slot inside
  exact ⟨pointer,length,RlpSliceInputEntry.after_frame state _ array slot pointer length input inputLength entry rfl rfl rfl⟩

theorem RlpSliceInputPrefix.fix_clock {F B : Type} (old state : PanSemStateFiniteExact 64 F)
    (result : B) (array input inputLength : BitVec 64) (filled : Nat)
    (valid : RlpSliceInputPrefix state array input inputLength filled) :
    RlpSliceInputPrefix (fixClockHOLFinite old (result,state)).2 array input inputLength filled := by
  exact valid.with_clock state array input inputLength filled _

theorem RlpSliceInputPrefix.dec_clock {F : Type} (state : PanSemStateFiniteExact 64 F)
    (array input inputLength : BitVec 64) (filled : Nat)
    (valid : RlpSliceInputPrefix state array input inputLength filled) :
    RlpSliceInputPrefix (decClockHOLFinite state) array input inputLength filled := by
  exact valid.with_clock state array input inputLength filled _

#print axioms RlpSliceInputPrefix.with_clock
#print axioms RlpSliceInputPrefix.fix_clock
#print axioms RlpSliceInputPrefix.dec_clock
end InitECandidate.Runtime
