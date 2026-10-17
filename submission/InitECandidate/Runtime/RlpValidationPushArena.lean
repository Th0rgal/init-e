import InitECandidate.Runtime.RlpValidationPushAllocation
import InitECandidate.Runtime.ScratchAllocationFields
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The original list push allocates its 24-byte stack record, saves the
parent interval, enters the payload and restores the temporary record local. -/
theorem evaluate_rlpValidation_list_push_arena {F : Type} (state : PanSemStateFiniteExact 64 F)
    (position stop top payload after scratch frame : BitVec 64)
    (positionLocal : state.locals.lookup (ofString "pos") = some (.val (.word position)))
    (stopLocal : state.locals.lookup (ofString "end") = some (.val (.word stop)))
    (topLocal : state.locals.lookup (ofString "top") = some (.val (.word top)))
    (payloadLocal : state.locals.lookup (ofString "payload") = some (.val (.word payload)))
    (afterLocal : state.locals.lookup (ofString "after") = some (.val (.word after)))
    (code : state.code = originalRuntimeCode) (ticks : 1 ≤ state.clock)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (request : (24 : BitVec 64) ≤ scratch - frame) (within : frame ≤ scratchAllocationEnd scratch 24)
    (fits : 24 ≤ scratch.toNat)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < scratch.toNat → state.memaddrs address) :
    ∃ post, evaluateHOLFiniteState state rlpValidationListPush = (none,post) ∧
      post.clock = state.clock - 1 ∧
      post.locals.lookup (ofString "pos") = some (.val (.word payload)) ∧
      post.locals.lookup (ofString "end") = some (.val (.word after)) ∧
      post.locals.lookup (ofString "top") = some (.val (.word (scratchAllocationEnd scratch 24))) ∧
      post.memory (scratchAllocationEnd scratch 24) = .word after ∧
      post.memory (scratchAllocationEnd scratch 24 + 8) = .word stop ∧
      post.memory (scratchAllocationEnd scratch 24 + 16) = .word top := by
  have domain : ∀ field : Nat, field < 24 → state.memaddrs (scratchAllocationEnd scratch 24 + BitVec.ofNat 64 field) := by
    intro field inside
    have geometry := scratchAllocation_field_nat scratch 24 field fits inside
    apply arena _ _ geometry.2
    have lower := BitVec.le_def.mp within
    rw [geometry.1]
    omega
  exact evaluate_rlpValidation_list_push state position stop top payload after scratch frame
    positionLocal stopLocal topLocal payloadLocal afterLocal code ticks scratchGlobal frameGlobal request within
    (by simpa using domain 0 (by decide)) (domain 8 (by decide)) (domain 16 (by decide))

#print axioms evaluate_rlpValidation_list_push_arena
end InitECandidate.Runtime
