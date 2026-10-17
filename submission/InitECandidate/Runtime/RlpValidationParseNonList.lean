import InitECandidate.Runtime.RlpValidationHeaderGeometry
import InitECandidate.Runtime.RlpValidationNonListInvariant
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The complete original header-call path preserves validator invariants
and decreases rank when its parsed item is a non-list, including both call
and temporary declaration scope restorations. -/
theorem rlpValidation_parse_non_list_invariant {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (position stop : BitVec 64) (frontier : Nat) (frames : List RlpValidationFrame)
    (positionLocal : state.locals.lookup (ofString "pos") = some (.val (.word position)))
    (stopLocal : state.locals.lookup (ofString "end") = some (.val (.word stop)))
    (topLocal : state.locals.lookup (ofString "top") = some (.val (.word (rlpValidationStackTop frames))))
    (stack : RlpValidationStack state.memory frontier frames)
    (intervals : RlpValidationIntervals position stop frames)
    (inputBound : (stop - position).toNat + 9 < 2^64)
    (code : state.code = originalRuntimeCode) (ticks : 12 ≤ state.clock)
    (run : evaluateHOLFiniteState state rlpValidationHeaderCall = (none,post)) :
    ∃ (header payload kind : BitVec 64) (ready output : PanSemStateFiniteExact 64 F),
      (kind = 0 ∨ kind = 1) ∧ ready.locals = state.locals ∧ ready.memory = state.memory ∧
      evaluateHOLFiniteState (setVarHOLFinite (ofString "h")
        (.rStruct [.val (.word header),.val (.word payload),.val (.word kind)]) ready)
        rlpValidationHeaderContinuation = (none,output) ∧
      post = {output with locals := HolFiniteMapExact.resVarEq output.locals (ofString "h",state.locals.lookup (ofString "h"))} ∧
      (kind = 0 →
        post.locals.lookup (ofString "pos") = some (.val (.word (position + header + payload))) ∧
        post.locals.lookup (ofString "end") = some (.val (.word stop)) ∧
        post.locals.lookup (ofString "top") = some (.val (.word (rlpValidationStackTop frames))) ∧
        RlpValidationStack post.memory frontier frames ∧
        RlpValidationIntervals (position + header + payload) stop frames ∧
        rlpValidationRank (position + header + payload) stop frames < rlpValidationRank position stop frames ∧
        post.memory = state.memory) := by
  have ordered : position.toNat ≤ stop.toNat := by
    cases intervals with
    | nil _ _ ordered => exact ordered
    | cons _ _ _ _ ordered _ _ => exact ordered
  obtain ⟨header,payload,kind,ready,output,flag,advances,bounded,_,locals,memory,tail,restored⟩ :=
    evaluate_rlpValidation_header_geometry state post position stop positionLocal stopLocal ordered inputBound code ticks run
  refine ⟨header,payload,kind,ready,output,flag,locals,memory,tail,restored,?_⟩
  intro nonList
  subst kind
  let entered := setVarHOLFinite (ofString "h")
    (.rStruct [.val (.word header),.val (.word payload),.val (.word 0)]) ready
  have atPosition : entered.locals.lookup (ofString "pos") = some (.val (.word position)) := by
    simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,locals,show ofString "h" ≠ ofString "pos" by decide] using positionLocal
  have atHeader : entered.locals.lookup (ofString "h") =
      some (.rStruct [.val (.word header),.val (.word payload),.val (.word 0)]) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have actual := evaluate_rlpValidation_non_list entered position header payload atPosition atHeader
  have same := (Prod.mk.inj (tail.symm.trans actual)).2
  have fields := rlpValidation_non_list_post entered position header payload
  have endFrame := rlpValidation_non_list_other_local entered position header payload (ofString "end") (by decide) (by decide) (by decide)
  have topFrame := rlpValidation_non_list_other_local entered position header payload (ofString "top") (by decide) (by decide) (by decide)
  have atStop : entered.locals.lookup (ofString "end") = some (.val (.word stop)) := by
    simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,locals,show ofString "h" ≠ ofString "end" by decide] using stopLocal
  have atTop : entered.locals.lookup (ofString "top") = some (.val (.word (rlpValidationStackTop frames))) := by
    simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,locals,show ofString "h" ≠ ofString "top" by decide] using topLocal
  rw [restored,same]
  refine ⟨?_,?_,?_,?_,intervals.reposition bounded,rlpValidation_rank_advance position _ stop frames advances bounded,?_⟩
  · rw [restore_other_local _ _ (ofString "pos") _ (by decide)]
    exact fields.1
  · rw [restore_other_local _ _ (ofString "end") _ (by decide)]
    exact endFrame.trans atStop
  · rw [restore_other_local _ _ (ofString "top") _ (by decide)]
    exact topFrame.trans atTop
  · change RlpValidationStack (rlpValidationNonListPost entered position header payload).memory frontier frames
    change RlpValidationStack ready.memory frontier frames
    rw [memory]
    exact stack
  · exact fields.2.2.1.trans memory

#print axioms rlpValidation_parse_non_list_invariant
end InitECandidate.Runtime
