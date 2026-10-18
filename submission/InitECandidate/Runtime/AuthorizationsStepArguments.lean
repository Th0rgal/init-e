import InitECandidate.Runtime.RlpSliceInputPrefix
import InitECandidate.Runtime.AuthorizationsStepSource
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Authorization item parsing loads a nonwrapping, input-bounded item directly
from any entry in the established input-span prefix. -/
theorem rlpSliceInputPrefix_authorization_arguments {F : Type} (state : PanSemStateFiniteExact 64 F)
    (array index count input inputLength : BitVec 64) (filled : Nat)
    (listLocal : state.locals.lookup (ofString "lst") = some (.rStruct [.val (.word array),.val (.word count)]))
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (valid : RlpSliceInputPrefix state array input inputLength filled)
    (inside : index.toNat < filled) :
    ∃ pointer length : BitVec 64,
      evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) authorizationStepArguments =
        some [.val (.word pointer),.val (.word length)] ∧
      pointer.toNat + length.toNat < 2^64 ∧ length.toNat ≤ inputLength.toNat ∧
      input.toNat ≤ pointer.toNat ∧ pointer.toNat + length.toNat ≤ input.toNat + inputLength.toNat := by
  obtain ⟨pointer,length,entry⟩ := valid index inside
  have args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) authorizationStepArguments =
      some [.val (.word pointer),.val (.word length)] := by
    simp [authorizationStepArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,listLocal,indexLocal,
      wordOpHOL,wordOp,panOpHOL,valueIsWord,valueWord,isWfShapeExactHOL,memLoadHOLExact,List.map_cons,List.map_nil]
    rw [if_pos entry.readable.pointerDomain,entry.readable.pointerCell]
    have d8 : state.memaddrs (array + (index * 16#64 + 8#64)) := by
      simpa only [BitVec.add_assoc] using entry.readable.lengthDomain
    have c8 : state.memory (array + (index * 16#64 + 8#64)) = .word length := by
      simpa only [BitVec.add_assoc] using entry.readable.lengthCell
    rw [if_pos d8,c8]
  exact ⟨pointer,length,args,entry.noWrap,entry.length_bound state array index pointer length input inputLength,
    entry.startsWithin,entry.endsWithin⟩

#print axioms rlpSliceInputPrefix_authorization_arguments
end InitECandidate.Runtime
