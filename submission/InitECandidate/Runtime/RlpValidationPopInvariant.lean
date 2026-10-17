import InitECandidate.Runtime.RlpValidationNonListInvariant
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual completed-interval step restores its saved parent, preserves
the remaining linked stack and interval order, and strictly decreases rank. -/
theorem evaluate_rlpValidation_pop_invariant {F : Type} (state : PanSemStateFiniteExact 64 F)
    (stop : BitVec 64) (frontier : Nat) (frame : RlpValidationFrame) (rest : List RlpValidationFrame)
    (positionLocal : state.locals.lookup (ofString "pos") = some (.val (.word stop)))
    (stopLocal : state.locals.lookup (ofString "end") = some (.val (.word stop)))
    (topLocal : state.locals.lookup (ofString "top") = some (.val (.word frame.record)))
    (stack : RlpValidationStack state.memory frontier (frame :: rest))
    (intervals : RlpValidationIntervals stop stop (frame :: rest))
    (domain0 : state.memaddrs frame.record) (domain8 : state.memaddrs (frame.record + 8))
    (domain16 : state.memaddrs (frame.record + 16)) :
    ∃ post, evaluateHOLFiniteState state rlpValidationStep = (none,post) ∧
      post.locals.lookup (ofString "pos") = some (.val (.word frame.resume)) ∧
      post.locals.lookup (ofString "end") = some (.val (.word frame.stop)) ∧
      post.locals.lookup (ofString "top") = some (.val (.word (rlpValidationStackTop rest))) ∧
      RlpValidationStack post.memory frontier rest ∧ RlpValidationIntervals frame.resume frame.stop rest ∧
      rlpValidationRank frame.resume frame.stop rest < rlpValidationRank stop stop (frame :: rest) ∧
      post.clock = state.clock ∧ post.memory = state.memory := by
  obtain ⟨post,run,positionPost,stopPost,topPost,stackPost,clock,memory⟩ :=
    evaluate_rlpValidation_stack_pop state stop stop frontier frame rest positionLocal stopLocal topLocal stack domain0 domain8 domain16
  have step := evaluate_rlpValidation_step_stack_pop state stop frontier frame rest positionLocal stopLocal topLocal stack
  have decreases := rlpValidation_rank_pop stop frame rest
  exact ⟨post,step.trans run,positionPost,stopPost,topPost,stackPost,intervals.pop,by omega,clock,memory⟩

#print axioms evaluate_rlpValidation_pop_invariant
end InitECandidate.Runtime
