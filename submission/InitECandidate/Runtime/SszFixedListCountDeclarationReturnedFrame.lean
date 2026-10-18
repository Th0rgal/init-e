import InitECandidate.Runtime.SszFixedListCountFrame
import InitECandidate.Runtime.OriginalSszFixedListCountCode
import InitECandidate.Runtime.PanThreeWordLookup
import InitECandidate.Runtime.PanDecCallCheckedReturnedExactScope
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A returned declaration exposes the checked count and a continuation entry
whose memory, globals and accessible addresses equal those of its caller. -/
theorem sszFixedListCount_declaration_returned_frame {F : Type} (state : PanSemStateFiniteExact 64 F)
    (name : MlS) (continuation : ProgHOL 64) (arguments : List (ExpHOL 64))
    (length size limit : BitVec 64)
    (args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments =
      some [.val (.word length),.val (.word size),.val (.word limit)])
    (code : state.code = originalRuntimeCode) (nonzeroSize : size ≠ 0)
    (post : PanSemStateFiniteExact 64 F) (finalValue : ValueHOL 64)
    (run : evaluateHOLFiniteState state (.decCall name .one (ofString "ssz_fixed_list_count") arguments continuation) =
      (some (.returned finalValue),post)) :
    length % size = 0 ∧ ¬ limit < length / size ∧
      ∃ (bodyPost output : PanSemStateFiniteExact 64 F),
        bodyPost.memory = state.memory ∧ bodyPost.globals = state.globals ∧ bodyPost.memaddrs = state.memaddrs ∧
        evaluateHOLFiniteState
        (setVarHOLFinite name (.val (.word (length / size))) {bodyPost with locals := state.locals}) continuation =
          (some (.returned finalValue),output) ∧
        post.memory = output.memory ∧ post.globals = output.globals ∧ post.memaddrs = output.memaddrs := by
  let callee : HolFiniteMapExact MlS (ValueHOL 64) :=
    ((HolFiniteMapExact.empty.update (ofString "len",.val (.word length))).update
      (ofString "sz",.val (.word size))).update (ofString "lim",.val (.word limit))
  let entry := callEntryStateHOLFinite state callee
  have atLength : entry.locals.lookup (ofString "len") = some (.val (.word length)) := by
    simp [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "sz" ≠ ofString "len" by decide,show ofString "lim" ≠ ofString "len" by decide]
  have atSize : entry.locals.lookup (ofString "sz") = some (.val (.word size)) := by
    simp [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "lim" ≠ ofString "sz" by decide]
  have atLimit : entry.locals.lookup (ofString "lim") = some (.val (.word limit)) := by
    simp [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have bounded := evaluate_sszFixedListCount_body entry length size limit code atLength atSize atLimit nonzeroSize
  have lookup := pan_three_word_lookup state.code.lookup (ofString "ssz_fixed_list_count")
    (ofString "len") (ofString "sz") (ofString "lim") (sourceFunctionBody Guest.guestFn_ssz_fixed_list_count)
    length size limit (by decide) (by decide) (by decide) (by rw [code]; exact originalRuntimeCode_sszFixedListCount_lookup)
  obtain ⟨value,bodyPost,output,bodyRun,checked,tail,restored⟩ := evaluate_decCall_checked_returned_exact_scope state post name
    (ofString "ssz_fixed_list_count") .one .one arguments [.val (.word length),.val (.word size),.val (.word limit)]
    (sourceFunctionBody Guest.guestFn_ssz_fixed_list_count) continuation callee finalValue args lookup run
  rw [bodyRun] at bounded
  dsimp only at bounded
  obtain ⟨rfl,divisible,within⟩ := bounded.2.2.2.2 value rfl
  have frame := evaluate_sszFixedListCount_body_frame entry length size code atLength atSize nonzeroSize
  have metadata := evaluateHOLFiniteState_metadata entry (sourceFunctionBody Guest.guestFn_ssz_fixed_list_count)
  rw [bodyRun] at frame metadata
  obtain ⟨memory,globals⟩ := frame (Or.inr (Or.inr (Or.inr ⟨_,rfl⟩)))
  refine ⟨divisible,within,bodyPost,output,memory,globals,metadata.2.1,tail,?_,?_,?_⟩
  all_goals rw [restored]

#print axioms sszFixedListCount_declaration_returned_frame
end InitECandidate.Runtime
