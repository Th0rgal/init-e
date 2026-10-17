import InitECandidate.Runtime.RlpValidationListStack
import InitECandidate.Runtime.RlpHeaderSizedGeometry
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Normal original list-continuation execution preserves linked-stack and
interval invariants and decreases rank using the checked header predicate. -/
theorem rlpValidation_list_continuation_invariant {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (position stop header payload scratch frame : BitVec 64) (frames : List RlpValidationFrame)
    (positionLocal : state.locals.lookup (ofString "pos") = some (.val (.word position)))
    (stopLocal : state.locals.lookup (ofString "end") = some (.val (.word stop)))
    (topLocal : state.locals.lookup (ofString "top") = some (.val (.word (rlpValidationStackTop frames))))
    (headerLocal : state.locals.lookup (ofString "h") = some
      (.rStruct [.val (.word header),.val (.word payload),.val (.word 1)]))
    (valid : RlpHeaderSizedProgress (.rStruct [.val (.word header),.val (.word payload),.val (.word 1)]) (stop - position))
    (stack : RlpValidationStack state.memory scratch.toNat frames)
    (intervals : RlpValidationIntervals position stop frames)
    (inputBound : (stop - position).toNat + 9 < 2^64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (ticks : 2 ≤ state.clock)
    (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < scratch.toNat → state.memaddrs address)
    (run : evaluateHOLFiniteState state rlpValidationHeaderContinuation = (none,post)) :
    let record := scratchAllocationEnd scratch 24
    let extended := {record := record,resume := position + header + payload,stop := stop} :: frames
    post.locals.lookup (ofString "pos") = some (.val (.word (position + header))) ∧
      post.locals.lookup (ofString "end") = some (.val (.word (position + header + payload))) ∧
      post.locals.lookup (ofString "top") = some (.val (.word record)) ∧
      RlpValidationStack post.memory record.toNat extended ∧
      RlpValidationIntervals (position + header) (position + header + payload) extended ∧
      rlpValidationRank (position + header) (position + header + payload) extended < rlpValidationRank position stop frames ∧
      post.clock = state.clock - 1 := by
  have fields := rlpValidation_list_continuation_post state post position stop (rlpValidationStackTop frames)
    header payload scratch frame positionLocal stopLocal topLocal headerLocal scratchGlobal frameGlobal
    code ticks orderedFrame arena run
  have linked := rlpValidation_list_continuation_stack state post position stop header payload scratch frame frames
    positionLocal stopLocal topLocal headerLocal scratchGlobal frameGlobal code ticks orderedFrame arena stack framePositive run
  have ordered : position.toNat ≤ stop.toNat := by
    cases intervals with
    | nil _ _ ordered => exact ordered
    | cons _ _ _ _ ordered _ _ => exact ordered
  have geometry := valid.list_geometry position stop header payload ordered inputBound
  have intervalPost := intervals.push (record := scratchAllocationEnd scratch 24) geometry.2.1 geometry.2.2
  have decreases := rlpValidation_rank_push position (position + header) (position + header + payload) stop
    (scratchAllocationEnd scratch 24) frames geometry.1 geometry.2.1 geometry.2.2
  exact ⟨fields.2.1,fields.2.2.1,fields.2.2.2.1,linked,intervalPost,decreases,fields.1⟩

#print axioms rlpValidation_list_continuation_invariant
end InitECandidate.Runtime
