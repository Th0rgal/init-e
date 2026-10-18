import InitECandidate.Runtime.SszFixedListCountBody
import InitECandidate.Runtime.OriginalSszFixedListCountCode
import InitECandidate.Runtime.PanThreeWordLookup
import InitECandidate.Runtime.CallBodyClockNoTimeout
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- An actual fixed-list count call with nonzero element size consumes at most
67 source ticks, including the entry tick and either SSZ rejection call. -/
theorem evaluate_sszFixedListCount_call_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (destination : Option (VarKind × MlS)) (arguments : List (ExpHOL 64))
    (length size limit : BitVec 64)
    (args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments =
      some [.val (.word length),.val (.word size),.val (.word limit)])
    (code : state.code = originalRuntimeCode) (nonzeroSize : size ≠ 0) (budget : 67 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (.call (some (destination,none)) (ofString "ssz_fixed_list_count") arguments)
    state.clock ≤ evaluated.2.clock + 67 ∧ evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
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
  cases bodyRun : evaluateHOLFiniteState entry (sourceFunctionBody Guest.guestFn_ssz_fixed_list_count) with
  | mk result post =>
    rw [bodyRun] at bounded
    dsimp only at bounded
    have output := evaluate_call_body_clock_no_timeout state post (ofString "ssz_fixed_list_count") destination arguments _
      (sourceFunctionBody Guest.guestFn_ssz_fixed_list_count) callee .one result args lookup (by omega) bodyRun
      (bounded.2.2.1 (by change 66 ≤ state.clock - 1; omega))
    dsimp only
    rw [output.2]
    refine ⟨?_,?_,output.1⟩
    · have spent := bounded.1
      change state.clock - 1 ≤ post.clock + 66 at spent
      change state.clock ≤ post.clock + 67
      omega
    · have remaining := bounded.2.1
      change post.clock ≤ state.clock - 1 at remaining
      change post.clock ≤ state.clock
      omega

#print axioms evaluate_sszFixedListCount_call_bounded
end InitECandidate.Runtime
