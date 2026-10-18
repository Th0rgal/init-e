import InitECandidate.Runtime.SszSplitVarListBody
import InitECandidate.Runtime.OriginalSszSplitVarListCode
import InitECandidate.Runtime.PanThreeWordShapeLookup
import InitECandidate.Runtime.CallBodyClockNoTimeout
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The original variable-list call includes one entry tick in addition to
the complete body bound, including allocation and SSZ rejection paths. -/
theorem evaluate_sszSplitVarList_call_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (destination : Option (VarKind × MlS)) (arguments : List (ExpHOL 64))
    (pointer length limit heapPointer : BitVec 64)
    (args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments =
      some [.val (.word pointer),.val (.word length),.val (.word limit)])
    (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heapPointer)))
    (pointerBound : heapPointer.toNat ≤ 33806089496) (budget : sszSplitBound length + 1 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (.call (some (destination,none)) (ofString "ssz_split_var_list") arguments)
    state.clock ≤ evaluated.2.clock + (sszSplitBound length + 1) ∧ evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  let callee : HolFiniteMapExact MlS (ValueHOL 64) :=
    ((HolFiniteMapExact.empty.update (ofString "p",.val (.word pointer))).update
      (ofString "len",.val (.word length))).update (ofString "lim",.val (.word limit))
  let entry := callEntryStateHOLFinite state callee
  have atPointer : entry.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
    simp [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "len" ≠ ofString "p" by decide,show ofString "lim" ≠ ofString "p" by decide]
  have atLength : entry.locals.lookup (ofString "len") = some (.val (.word length)) := by
    simp [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "lim" ≠ ofString "len" by decide]
  have atLimit : entry.locals.lookup (ofString "lim") = some (.val (.word limit)) := by
    simp [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have bounded := evaluate_sszSplitVarList_body entry pointer length limit heapPointer code atPointer atLength atLimit heap pointerBound
  have lookup := pan_three_word_shape_lookup state.code.lookup (ofString "ssz_split_var_list")
    (ofString "p") (ofString "len") (ofString "lim") (sourceFunctionBody Guest.guestFn_ssz_split_var_list)
    (.comb [.one,.one]) pointer length limit (by decide) (by decide) (by decide) (by rw [code]; exact originalRuntimeCode_sszSplitVarList_lookup)
  cases bodyRun : evaluateHOLFiniteState entry (sourceFunctionBody Guest.guestFn_ssz_split_var_list) with
  | mk result post =>
    rw [bodyRun] at bounded
    dsimp only at bounded
    have output := evaluate_call_body_clock_no_timeout state post (ofString "ssz_split_var_list") destination arguments _
      (sourceFunctionBody Guest.guestFn_ssz_split_var_list) callee (.comb [.one,.one]) result args lookup (by omega) bodyRun
      (bounded.2.2.1 (by change sszSplitBound length ≤ state.clock - 1; omega))
    dsimp only
    rw [output.2]
    refine ⟨?_,?_,output.1⟩
    · have spent := bounded.1
      change state.clock - 1 ≤ post.clock + sszSplitBound length at spent
      change state.clock ≤ post.clock + (sszSplitBound length + 1)
      omega
    · have remaining := bounded.2.1
      change post.clock ≤ state.clock - 1 at remaining
      change post.clock ≤ state.clock
      omega

#print axioms evaluate_sszSplitVarList_call_bounded
end InitECandidate.Runtime
