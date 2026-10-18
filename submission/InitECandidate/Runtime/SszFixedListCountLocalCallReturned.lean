import InitECandidate.Runtime.SszFixedListCountBody
import InitECandidate.Runtime.OriginalSszFixedListCountCode
import InitECandidate.Runtime.PanThreeWordLookup
import InitECandidate.Runtime.PanLocalCallNormalResult
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A normally completed original fixed-list call binds the exact quotient,
with zero remainder and the checked count limit. No clock budget is assumed. -/
theorem sszFixedListCount_local_call_returned {F : Type} (state : PanSemStateFiniteExact 64 F)
    (name : MlS) (arguments : List (ExpHOL 64))
    (length size limit : BitVec 64)
    (args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments =
      some [.val (.word length),.val (.word size),.val (.word limit)])
    (code : state.code = originalRuntimeCode) (nonzeroSize : size ≠ 0)
    (post : PanSemStateFiniteExact 64 F)
    (run : evaluateHOLFiniteState state (.call (some (some (.local,name),none)) (ofString "ssz_fixed_list_count") arguments) = (none,post)) :
    post.locals.lookup name = some (.val (.word (length / size))) ∧ length % size = 0 ∧ ¬ limit < length / size := by
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
  obtain ⟨value,bodyPost,bodyRun,checked,restored⟩ := evaluate_localCall_normal_result state post name
    (ofString "ssz_fixed_list_count") .one arguments [.val (.word length),.val (.word size),.val (.word limit)]
    (sourceFunctionBody Guest.guestFn_ssz_fixed_list_count) callee args lookup run
  rw [bodyRun] at bounded
  dsimp only at bounded
  obtain ⟨rfl,divisible,within⟩ := bounded.2.2.2.2 value rfl
  refine ⟨?_,divisible,within⟩
  rw [restored]
  simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]

#print axioms sszFixedListCount_local_call_returned
end InitECandidate.Runtime
