import InitECandidate.Runtime.SszFixedListCountFrame
import InitECandidate.Runtime.OriginalSszFixedListCountCode
import InitECandidate.Runtime.PanThreeWordLookup
import InitECandidate.Runtime.PanLocalCallNormalResult
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Normal fixed-list calls preserve the caller memory, globals and address domain. -/
theorem sszFixedListCount_local_call_frame {F : Type} (state : PanSemStateFiniteExact 64 F)
    (name : MlS) (arguments : List (ExpHOL 64))
    (length size limit : BitVec 64)
    (args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments =
      some [.val (.word length),.val (.word size),.val (.word limit)])
    (code : state.code = originalRuntimeCode) (nonzeroSize : size ≠ 0)
    (post : PanSemStateFiniteExact 64 F)
    (run : evaluateHOLFiniteState state (.call (some (some (.local,name),none)) (ofString "ssz_fixed_list_count") arguments) = (none,post)) :
    post.memory = state.memory ∧ post.globals = state.globals ∧ post.memaddrs = state.memaddrs := by
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
  have lookup := pan_three_word_lookup state.code.lookup (ofString "ssz_fixed_list_count")
    (ofString "len") (ofString "sz") (ofString "lim") (sourceFunctionBody Guest.guestFn_ssz_fixed_list_count)
    length size limit (by decide) (by decide) (by decide) (by rw [code]; exact originalRuntimeCode_sszFixedListCount_lookup)
  obtain ⟨value,bodyPost,bodyRun,checked,restored⟩ := evaluate_localCall_normal_result state post name
    (ofString "ssz_fixed_list_count") .one arguments [.val (.word length),.val (.word size),.val (.word limit)]
    (sourceFunctionBody Guest.guestFn_ssz_fixed_list_count) callee args lookup run
  have frame := evaluate_sszFixedListCount_body_frame entry length size code atLength atSize nonzeroSize
  have metadata := evaluateHOLFiniteState_metadata entry (sourceFunctionBody Guest.guestFn_ssz_fixed_list_count)
  rw [bodyRun] at frame metadata
  obtain ⟨memory,globals⟩ := frame (Or.inr (Or.inr (Or.inr ⟨value,rfl⟩)))
  rw [restored]
  exact ⟨memory,globals,metadata.2.1⟩

#print axioms sszFixedListCount_local_call_frame
end InitECandidate.Runtime
