import InitECandidate.Runtime.GuestCostOpAddOuter
import InitECandidate.Runtime.GuestFrameOpAddBridge
import InitECandidate.Runtime.GuestCostOpAddPost
import InitECandidate.Runtime.RunFramesIteration
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Runtime.FineCost
open InitECandidate.Proofs.FrontendCodecComputation

set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

/-- The real `op_dispatch` body runs the ADD arm for `op = 1`, starting from
the reusable frame invariant. The catch-all tail is never evaluated because the
arm returns. -/
theorem opAdd_dispatch_body_run_direct (coeff : FineCost.Work)
    (d : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame sp cap base pc : BitVec 64) (funding : GasFunding)
    (a0 a1 a2 a3 b0 b1 b2 b3 : BitVec 64)
    (inv : FineCost.GuestFrameInvariant d frame sp cap base pc funding a0 a1 a2 a3 b0 b1 b2 b3)
    (opcode : d.locals.lookup (ofString "op") = some (.val (.word (1 : BitVec 64))))
    (clock : 8 ≤ d.clock) :
    ∃ bodyPost bodyEvents, StatementRun d (sourceFunctionBody Guest.guestFn_op_dispatch)
      (some (.returned (.val (.word 0)))) (FineCost.opAddDispatchArmPost d bodyPost)
      (FineCost.opAddOuterThirtyTwoEvents d bodyPost bodyEvents) ∧
      HasGasFunding bodyPost frame (funding.charge 3) ∧
      bodyPost.memory (frame + 0) = .word (pc + 1) ∧
      bodyPost.clock = d.clock - 7
:= by
  classical
  let entry := callEntryStateHOLFinite d HolFiniteMapExact.empty
  have entryInv : FineCost.GuestFrameInvariant entry frame sp cap base pc funding
      a0 a1 a2 a3 b0 b1 b2 b3 :=
    FineCost.GuestFrameInvariant.callEntry_GuestFrameInvariant d HolFiniteMapExact.empty inv (by
      change 7 ≤ d.clock - 1
      omega)
  let bodyPost := FineCost.opAddFinalPost entry frame sp cap base pc
    (FineCost.fourWordValue a0 a1 a2 a3) (FineCost.fourWordValue b0 b1 b2 b3)
    funding a0 a1 a2 a3 b0 b1 b2 b3
  let bodyEvents := FineCost.opAddEvents entry frame sp cap base pc funding
    a0 a1 a2 a3 b0 b1 b2 b3
  have bodyRun : StatementRun entry (sourceFunctionBody Guest.guestFn_op_add)
      (some (.returned (.val (.word 0)))) bodyPost bodyEvents :=
    FineCost.opAdd_body_run_of_frame (coeff := coeff) entry frame sp cap base pc funding
      a0 a1 a2 a3 b0 b1 b2 b3 entryInv
  have arm := FineCost.opAdd_dispatch_arm_run (coeff := coeff) d bodyPost bodyEvents bodyRun
    (by have h := inv.clock; omega) (by exact inv.code)
  refine ⟨bodyPost, bodyEvents, ?_, ?_, ?_, ?_⟩
  unfold sourceFunctionBody
  rw [declToHOL_eq]
  simp only [Guest.guestFn_op_dispatch, declToHOLStructural, funDeclToHOLStructural,
    progToHOLStructural, expToHOLStructural, shapeToHOLStructural, expListToHOLStructural,
    List.map_cons, List.map_nil, Option.map_none]
  · exact FineCost.opAddOuter_lt32_run (coeff := coeff) d bodyPost bodyEvents _ _ _ _ _ arm opcode
  · change HasGasFunding (FineCost.opAddFinalPost entry frame sp cap base pc
      (FineCost.fourWordValue a0 a1 a2 a3) (FineCost.fourWordValue b0 b1 b2 b3)
      funding a0 a1 a2 a3 b0 b1 b2 b3) frame (funding.charge 3)
    exact FineCost.opAddFinalPost_funding entry frame sp cap base pc funding a0 a1 a2 a3 b0 b1 b2 b3 entryInv
  · change (FineCost.opAddFinalPost entry frame sp cap base pc
      (FineCost.fourWordValue a0 a1 a2 a3) (FineCost.fourWordValue b0 b1 b2 b3)
      funding a0 a1 a2 a3 b0 b1 b2 b3).memory (frame + 0) = .word (pc + 1)
    exact FineCost.opAddFinalPost_pc entry frame sp cap base pc funding a0 a1 a2 a3 b0 b1 b2 b3
  · change (FineCost.opAddFinalPost entry frame sp cap base pc
      (FineCost.fourWordValue a0 a1 a2 a3) (FineCost.fourWordValue b0 b1 b2 b3)
      funding a0 a1 a2 a3 b0 b1 b2 b3).clock = d.clock - 7
    rw [FineCost.opAddFinalPost_clock]
    change entry.clock - 6 = d.clock - 7
    change d.clock - 1 - 6 = d.clock - 7
    omega

#print axioms opAdd_dispatch_body_run_direct
end InitECandidate.Runtime
