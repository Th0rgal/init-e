import InitECandidate.Runtime.RlpValidationPushStores
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

noncomputable def rlpValidationPushPost {F : Type} (state : PanSemStateFiniteExact 64 F)
    (record after stop top payload : BitVec 64) : PanSemStateFiniteExact 64 F :=
  let written := sourceWriteWord (sourceWriteWord (sourceWriteWord state record after) (record + 8) stop) (record + 16) top
  setVarHOLFinite (ofString "end") (.val (.word after))
    (setVarHOLFinite (ofString "pos") (.val (.word payload))
      (setVarHOLFinite (ofString "top") (.val (.word record)) written))

/-- The original post-allocation list push saves its parent interval and
enters the nested payload, with an exact final state and no source-clock cost. -/
theorem evaluate_rlpValidation_push_execution {F : Type} (state : PanSemStateFiniteExact 64 F)
    (position stop top record payload after : BitVec 64)
    (positionLocal : state.locals.lookup (ofString "pos") = some (.val (.word position)))
    (stopLocal : state.locals.lookup (ofString "end") = some (.val (.word stop)))
    (topLocal : state.locals.lookup (ofString "top") = some (.val (.word top)))
    (recordLocal : state.locals.lookup (ofString "rec") = some (.val (.word record)))
    (payloadLocal : state.locals.lookup (ofString "payload") = some (.val (.word payload)))
    (afterLocal : state.locals.lookup (ofString "after") = some (.val (.word after)))
    (domain0 : state.memaddrs record) (domain8 : state.memaddrs (record + 8))
    (domain16 : state.memaddrs (record + 16)) :
    evaluateHOLFiniteState state rlpValidationPushStores =
      (none,rlpValidationPushPost state record after stop top payload) := by
  rw [evaluate_rlpValidation_push_stores state record after stop top recordLocal afterLocal stopLocal topLocal
    domain0 domain8 domain16]
  apply evaluate_rlpValidation_push_updates _ top position stop record payload after
  all_goals simpa only [sourceWriteWord]

theorem rlpValidation_push_post {F : Type} (state : PanSemStateFiniteExact 64 F)
    (record after stop top payload : BitVec 64) :
    let post := rlpValidationPushPost state record after stop top payload
    post.locals.lookup (ofString "pos") = some (.val (.word payload)) ∧
      post.locals.lookup (ofString "end") = some (.val (.word after)) ∧
      post.locals.lookup (ofString "top") = some (.val (.word record)) ∧
      post.memory record = .word after ∧ post.memory (record + 8) = .word stop ∧
      post.memory (record + 16) = .word top ∧ post.clock = state.clock ∧ post.globals = state.globals := by
  simp [rlpValidationPushPost,setVarHOLFinite,sourceWriteWord,HolFiniteMapExact.lookup_update,FUPDATE,
    show ofString "end" ≠ ofString "pos" by decide,
    show ofString "end" ≠ ofString "top" by decide,show ofString "pos" ≠ ofString "top" by decide]

#print axioms evaluate_rlpValidation_push_execution
#print axioms rlpValidation_push_post
end InitECandidate.Runtime
