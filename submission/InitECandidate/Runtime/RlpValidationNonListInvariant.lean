import InitECandidate.Runtime.RlpValidationInitialization
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The non-list continuation preserves the loop/stack locals outside its
cursor assignment and temporary payload/after scopes. -/
theorem rlpValidation_non_list_other_local {F : Type} (state : PanSemStateFiniteExact 64 F)
    (position header payload : BitVec 64) (name : MlS)
    (notPosition : name ≠ ofString "pos") (notPayload : name ≠ ofString "payload")
    (notAfter : name ≠ ofString "after") :
    (rlpValidationNonListPost state position header payload).locals.lookup name = state.locals.lookup name := by
  dsimp only [rlpValidationNonListPost]
  rw [restore_other_local _ _ name _ notPayload,restore_other_local _ _ name _ notAfter]
  simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm notPosition,Ne.symm notPayload,Ne.symm notAfter]

/-- The actual original non-list continuation preserves the stack and interval
invariants and strictly decreases the checked validator measure. -/
theorem evaluate_rlpValidation_non_list_invariant {F : Type} (state : PanSemStateFiniteExact 64 F)
    (position stop header payload : BitVec 64) (frontier : Nat) (frames : List RlpValidationFrame)
    (positionLocal : state.locals.lookup (ofString "pos") = some (.val (.word position)))
    (stopLocal : state.locals.lookup (ofString "end") = some (.val (.word stop)))
    (topLocal : state.locals.lookup (ofString "top") = some (.val (.word (rlpValidationStackTop frames))))
    (headerLocal : state.locals.lookup (ofString "h") =
      some (.rStruct [.val (.word header),.val (.word payload),.val (.word 0)]))
    (stack : RlpValidationStack state.memory frontier frames)
    (intervals : RlpValidationIntervals position stop frames)
    (positive : 0 < (header + payload).toNat)
    (bounded : (header + payload).toNat ≤ (stop - position).toNat) :
    ∃ post, evaluateHOLFiniteState state rlpValidationHeaderContinuation = (none,post) ∧
      post.locals.lookup (ofString "pos") = some (.val (.word (position + header + payload))) ∧
      post.locals.lookup (ofString "end") = some (.val (.word stop)) ∧
      post.locals.lookup (ofString "top") = some (.val (.word (rlpValidationStackTop frames))) ∧
      RlpValidationStack post.memory frontier frames ∧
      RlpValidationIntervals (position + header + payload) stop frames ∧
      rlpValidationRank (position + header + payload) stop frames < rlpValidationRank position stop frames ∧
      post.clock = state.clock ∧ post.memory = state.memory := by
  let post := rlpValidationNonListPost state position header payload
  have run := evaluate_rlpValidation_non_list state position header payload positionLocal headerLocal
  have fields := rlpValidation_non_list_post state position header payload
  have ordered : position.toNat ≤ stop.toNat := by
    cases intervals with
    | nil _ _ ordered => exact ordered
    | cons _ _ _ _ ordered _ _ => exact ordered
  have advance := rlp_header_cursor_advance position stop header payload ordered positive bounded
  have endFrame := rlpValidation_non_list_other_local state position header payload (ofString "end")
    (by decide) (by decide) (by decide)
  have topFrame := rlpValidation_non_list_other_local state position header payload (ofString "top")
    (by decide) (by decide) (by decide)
  exact ⟨post,run,fields.1,endFrame.trans stopLocal,topFrame.trans topLocal,stack,
    intervals.reposition advance.2.1,rlpValidation_rank_advance position (position + header + payload) stop frames
      advance.1 advance.2.1,fields.2.1,fields.2.2.1⟩

#print axioms rlpValidation_non_list_other_local
#print axioms evaluate_rlpValidation_non_list_invariant
end InitECandidate.Runtime
