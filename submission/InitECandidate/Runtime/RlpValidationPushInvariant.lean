import InitECandidate.Runtime.RlpValidationPopInvariant
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The original post-allocation list-push execution extends the linked stack,
preserves interval ordering and decreases rank despite adding a pending pop. -/
theorem evaluate_rlpValidation_push_invariant {F : Type} (state : PanSemStateFiniteExact 64 F)
    (position stop payload after scratch : BitVec 64) (frames : List RlpValidationFrame)
    (positionLocal : state.locals.lookup (ofString "pos") = some (.val (.word position)))
    (stopLocal : state.locals.lookup (ofString "end") = some (.val (.word stop)))
    (topLocal : state.locals.lookup (ofString "top") = some (.val (.word (rlpValidationStackTop frames))))
    (recordLocal : state.locals.lookup (ofString "rec") = some (.val (.word (scratchAllocationEnd scratch 24))))
    (payloadLocal : state.locals.lookup (ofString "payload") = some (.val (.word payload)))
    (afterLocal : state.locals.lookup (ofString "after") = some (.val (.word after)))
    (stack : RlpValidationStack state.memory scratch.toNat frames)
    (intervals : RlpValidationIntervals position stop frames)
    (fits : 24 ≤ scratch.toNat) (nonzero : scratchAllocationEnd scratch 24 ≠ 0)
    (headerPositive : position.toNat < payload.toNat)
    (payloadOrdered : payload.toNat ≤ after.toNat) (bounded : after.toNat ≤ stop.toNat)
    (domain0 : state.memaddrs (scratchAllocationEnd scratch 24))
    (domain8 : state.memaddrs (scratchAllocationEnd scratch 24 + 8))
    (domain16 : state.memaddrs (scratchAllocationEnd scratch 24 + 16)) :
    let record := scratchAllocationEnd scratch 24
    let extended := {record := record,resume := after,stop := stop} :: frames
    ∃ post, evaluateHOLFiniteState state rlpValidationPushStores = (none,post) ∧
      post.locals.lookup (ofString "pos") = some (.val (.word payload)) ∧
      post.locals.lookup (ofString "end") = some (.val (.word after)) ∧
      post.locals.lookup (ofString "top") = some (.val (.word record)) ∧
      RlpValidationStack post.memory record.toNat extended ∧
      RlpValidationIntervals payload after extended ∧
      rlpValidationRank payload after extended < rlpValidationRank position stop frames ∧ post.clock = state.clock := by
  let record := scratchAllocationEnd scratch 24
  let post := rlpValidationPushPost state record after stop (rlpValidationStackTop frames) payload
  have run := evaluate_rlpValidation_push_execution state position stop (rlpValidationStackTop frames) record payload after
    positionLocal stopLocal topLocal recordLocal payloadLocal afterLocal domain0 domain8 domain16
  have fields := rlpValidation_push_post state record after stop (rlpValidationStackTop frames) payload
  have stackPost := stack.push state scratch after stop payload fits nonzero
  have intervalPost := intervals.push (record := record) payloadOrdered bounded
  have decreases := rlpValidation_rank_push position payload after stop record frames headerPositive payloadOrdered bounded
  exact ⟨post,run,fields.1,fields.2.1,fields.2.2.1,stackPost,intervalPost,decreases,fields.2.2.2.2.2.2.1⟩

#print axioms evaluate_rlpValidation_push_invariant
end InitECandidate.Runtime
