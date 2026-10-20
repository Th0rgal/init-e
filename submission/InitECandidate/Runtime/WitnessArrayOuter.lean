import InitECandidate.Runtime.WitnessArrayLinked
import InitECandidate.Runtime.RlpSliceInputPrefixOuter
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- Re-express actual readable nested witness arrays in one enclosing input
span; the count bound follows from the actual nested span containment. -/
theorem WitnessArrayLinked.within_outer {F : Type} (state : PanSemStateFiniteExact 64 F)
    (si first second array count pointer length input inputLength heap : BitVec 64)
    (valid : WitnessArrayLinked state si first second array count pointer length heap)
    (starts : input.toNat≤pointer.toNat)
    (ends : pointer.toNat+length.toNat≤input.toNat+inputLength.toNat) :
    WitnessArrayLinked state si first second array count input inputLength heap := by
  have lengths : length.toNat≤inputLength.toNat := by omega
  exact ⟨valid.pointerDomain,valid.countDomain,valid.pointerCell,valid.countCell,
    valid.slices.within_outer state array pointer length input inputLength count.toNat starts ends,
    Nat.le_trans valid.countBound (Nat.div_le_div_right lengths),valid.arrayEnd⟩

#print axioms WitnessArrayLinked.within_outer
end InitECandidate.Runtime
