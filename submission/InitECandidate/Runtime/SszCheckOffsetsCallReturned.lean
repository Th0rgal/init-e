import InitECandidate.Runtime.SszCheckOffsetsBody
import InitECandidate.Runtime.PanFourWordLookup
import InitECandidate.Runtime.PanDiscardCallNormalResult
import InitECandidate.Runtime.SszBodyFrames
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Normal offset-check calls expose the checked input offsets and preserve
memory, globals, accessible addresses and caller locals. -/
theorem sszCheckOffsets_call_returned {F : Type} (state : PanSemStateFiniteExact 64 F)
    (arguments : List (ExpHOL 64))
    (offsets count fixed length : BitVec 64)
    (args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments =
      some [.val (.word offsets),.val (.word count),.val (.word fixed),.val (.word length)])
    (code : state.code = originalRuntimeCode) (small : count.toNat < 2 ^ 63)
    (post : PanSemStateFiniteExact 64 F)
    (run : evaluateHOLFiniteState state (.call (some (none,none)) (ofString "ssz_check_offsets") arguments) = (none,post)) :
    SszCheckOffsetsReturned state offsets count fixed length (.val (.word 0)) ∧
      post.memory = state.memory ∧ post.globals = state.globals ∧ post.memaddrs = state.memaddrs ∧ post.locals = state.locals := by
  let callee : HolFiniteMapExact MlS (ValueHOL 64) :=
    (((HolFiniteMapExact.empty.update (ofString "offs",.val (.word offsets))).update
      (ofString "n",.val (.word count))).update (ofString "fixed",.val (.word fixed))).update
      (ofString "len",.val (.word length))
  let entry := callEntryStateHOLFinite state callee
  have atOffsets : entry.locals.lookup (ofString "offs") = some (.val (.word offsets)) := by
    simp [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "n" ≠ ofString "offs" by decide,show ofString "fixed" ≠ ofString "offs" by decide,
      show ofString "len" ≠ ofString "offs" by decide]
  have atCount : entry.locals.lookup (ofString "n") = some (.val (.word count)) := by
    simp [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "fixed" ≠ ofString "n" by decide,show ofString "len" ≠ ofString "n" by decide]
  have atFixed : entry.locals.lookup (ofString "fixed") = some (.val (.word fixed)) := by
    simp [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "len" ≠ ofString "fixed" by decide]
  have atLength : entry.locals.lookup (ofString "len") = some (.val (.word length)) := by
    simp [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have bounded := evaluate_sszCheckOffsets_body entry offsets count fixed length code
    atOffsets atCount atFixed atLength small
  have lookup := pan_four_word_lookup state.code.lookup (ofString "ssz_check_offsets")
    (ofString "offs") (ofString "n") (ofString "fixed") (ofString "len")
    (sourceFunctionBody Guest.guestFn_ssz_check_offsets) offsets count fixed length
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [code]; exact originalRuntimeCode_sszCheckOffsets_lookup)
  obtain ⟨value,bodyPost,bodyRun,checked,restored⟩ := evaluate_discardCall_normal_result state post
    (ofString "ssz_check_offsets") .one arguments
    [.val (.word offsets),.val (.word count),.val (.word fixed),.val (.word length)]
    (sourceFunctionBody Guest.guestFn_ssz_check_offsets) callee args lookup run
  rw [bodyRun] at bounded
  dsimp only at bounded
  have returned := bounded.2.2.2.2 value rfl
  obtain ⟨rfl,offsetFacts,first⟩ := returned
  have frame := evaluate_sszCheckOffsets_body_frame entry code
  have metadata := evaluateHOLFiniteState_metadata entry (sourceFunctionBody Guest.guestFn_ssz_check_offsets)
  rw [bodyRun] at frame metadata
  obtain ⟨memory,globals⟩ := frame (Or.inr (Or.inr (Or.inr ⟨_,rfl⟩)))
  refine ⟨⟨rfl,offsetFacts,first⟩,?_,?_,?_,?_⟩
  all_goals rw [restored]
  · exact memory
  · exact globals
  · exact metadata.2.1

#print axioms sszCheckOffsets_call_returned
end InitECandidate.Runtime
