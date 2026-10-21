import InitECandidate.Runtime.RunFramesOpAdd
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Runtime.FineCost

set_option maxHeartbeats 4000000

/-- The `run_frames` dispatcher call executes the ADD arm for `op = 1`: it
returns normally, charges three gas units, advances `ev+0`, and restores the
caller's locals. -/
theorem opAdd_dispatch_call_progress (coeff : FineCost.Work)
    (state : PanSemStateFiniteExact 64 Guest.HostMemory)
    (argument : ExpHOL 64) (handler : Option (MlS × MlS × ProgHOL 64))
    (arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) [argument] =
      some [.val (.word (1 : BitVec 64))])
    (frame sp cap base pc : BitVec 64) (funding : GasFunding)
    (a0 a1 a2 a3 b0 b1 b2 b3 : BitVec 64)
    (inv : GuestFrameInvariant state frame sp cap base pc funding a0 a1 a2 a3 b0 b1 b2 b3)
    (clock : 9 ≤ state.clock) (budget : funding.potential ≤ 200000000)
    (enough : (3 : BitVec 64) ≤ funding.left) :
    ∃ (entry bodyPost : PanSemStateFiniteExact 64 Guest.HostMemory),
      evaluateHOLFiniteState state
        (.call (some (none, handler)) (ofString "op_dispatch") [argument]) =
        (none, { bodyPost with locals := state.locals }) ∧
      entry = callEntryStateHOLFinite state
        (HolFiniteMapExact.empty.update (ofString "op", .val (.word (1 : BitVec 64)))) ∧
      HasGasFunding bodyPost frame (funding.charge 3) ∧
      bodyPost.memory (frame + 0) = .word (pc + 1) ∧
      bodyPost.clock = state.clock - 8 ∧
      (funding.charge 3).potential = funding.potential ∧
      (funding.charge 3).used.toNat = funding.used.toNat + 3 := by
  classical
  let callee : HolFiniteMapExact MlS (ValueHOL 64) :=
    HolFiniteMapExact.empty.update (ofString "op", .val (.word (1 : BitVec 64)))
  let entry := callEntryStateHOLFinite state callee
  have opcode : entry.locals.lookup (ofString "op") = some (.val (.word (1 : BitVec 64))) := by
    simp [entry, callee, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have entryInv : GuestFrameInvariant entry frame sp cap base pc funding
      a0 a1 a2 a3 b0 b1 b2 b3 :=
    GuestFrameInvariant.callEntry_GuestFrameInvariant state callee inv (by
      change 7 ≤ state.clock - 1
      omega)
  have entryClock : 8 ≤ entry.clock := by change 8 ≤ state.clock - 1; omega
  obtain ⟨bodyPost, bodyEvents, bodyRun, fundingPost, pcPost, clockPost⟩ :=
    opAdd_dispatch_body_run_direct (coeff := coeff) entry frame sp cap base pc funding
      a0 a1 a2 a3 b0 b1 b2 b3 entryInv opcode entryClock
  have installed : state.code.lookup (ofString "op_dispatch") =
      some ([(ofString "op", .one)], sourceFunctionBody Guest.guestFn_op_dispatch, .one) := by
    rw [inv.code]
    exact originalRuntimeCode_dispatch_lookup
  have lookup := pan_single_word_lookup state.code.lookup (ofString "op_dispatch") (ofString "op")
    (sourceFunctionBody Guest.guestFn_op_dispatch) 1 installed
  let armPost := opAddDispatchArmPost entry bodyPost
  have call := evaluateHOLFiniteState_call_return_caller_locals state handler
    (ofString "op_dispatch") [argument] [.val (.word 1)]
    (sourceFunctionBody Guest.guestFn_op_dispatch) callee .one (.val (.word 0))
    armPost arguments lookup (by have h := inv.clock; omega) bodyRun.sound
    (by simp [shapeOfHOLExact, shapeEqHOL])
  refine ⟨entry, armPost, call, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · change HasGasFunding bodyPost frame (funding.charge 3)
    exact fundingPost
  · change bodyPost.memory (frame + 0) = .word (pc + 1)
    exact pcPost
  · have hclock : armPost.clock = entry.clock - 7 := clockPost
    rw [hclock]
    change entry.clock - 7 = state.clock - 8
    change state.clock - 1 - 7 = state.clock - 8
    omega
  · exact funding.charge_potential 3 budget enough
  · exact funding.charge_used_growth 3 budget enough

#print axioms opAdd_dispatch_call_progress
end InitECandidate.Runtime
