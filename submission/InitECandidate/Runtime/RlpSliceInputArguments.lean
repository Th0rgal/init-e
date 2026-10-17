import InitECandidate.Runtime.RlpSliceInputPrefix
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Fixed-byte extraction loads a nonwrapping, input-bounded item directly
from any entry in the established input-span prefix. -/
theorem rlpSliceInputPrefix_fixed_bytes_arguments {F : Type} (state : PanSemStateFiniteExact 64 F)
    (array index input inputLength : BitVec 64) (filled : Nat)
    (arrayLocal : state.locals.lookup (ofString "arr") = some (.val (.word array)))
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (valid : RlpSliceInputPrefix state array input inputLength filled)
    (inside : index.toNat < filled) :
    ∃ pointer length : BitVec 64,
      evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) txFixedBytesArguments =
        some [.val (.word pointer),.val (.word length)] ∧
      pointer.toNat + length.toNat < 2^64 ∧ length.toNat ≤ inputLength.toNat ∧
      input.toNat ≤ pointer.toNat ∧ pointer.toNat + length.toNat ≤ input.toNat + inputLength.toNat := by
  obtain ⟨pointer,length,entry⟩ := valid index inside
  exact ⟨pointer,length,eval_txFixedBytes_arguments state array index pointer length arrayLocal indexLocal entry.readable,
    entry.noWrap,entry.length_bound state array index pointer length input inputLength,entry.startsWithin,entry.endsWithin⟩

#print axioms rlpSliceInputPrefix_fixed_bytes_arguments
end InitECandidate.Runtime
