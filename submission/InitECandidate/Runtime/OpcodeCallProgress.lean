import InitECandidate.Runtime.OriginalOpcodeProgress
import InitECandidate.Runtime.OriginalOpcodeCode
import InitECandidate.Runtime.PanNoArgsLookup
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual dispatch-style JUMPDEST call spends three clocks including its
entry, preserves the caller frame, and consumes one unit of regular gas. -/
theorem original_jumpdest_call_progress (state : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame pc : BitVec 64) (funding : GasFunding) (code : state.code = originalRuntimeCode)
    (clock : 3 ≤ state.clock)
    (hFrame : state.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (pcDomain : state.memaddrs (frame + 0)) (pcMemory : state.memory (frame + 0) = .word pc)
    (leftDomain : state.memaddrs (frame + 64)) (usedDomain : state.memaddrs (frame + 184))
    (memory : HasGasFunding state frame funding) (enough : (1 : BitVec 64) ≤ funding.left)
    (budget : funding.potential ≤ 200000000) :
    ∃ post, evaluateHOLFiniteState state (.call (some (none,none)) (ofString "op_jumpdest") []) = (none,post) ∧
      HasGasFunding post frame (funding.charge 1) ∧
      post.clock = state.clock - 3 ∧ post.memory (frame + 0) = .word (pc + 1) ∧
      post.code = state.code ∧ post.globals = state.globals ∧ post.memaddrs = state.memaddrs ∧
      post.locals = state.locals ∧ (funding.charge 1).potential = funding.potential ∧
      (funding.charge 1).used.toNat = funding.used.toNat + 1 := by
  let entry := callEntryStateHOLFinite state HolFiniteMapExact.empty
  have entryClock : 2 ≤ entry.clock := by change 2 ≤ state.clock - 1; omega
  obtain ⟨bodyPost,bodyRun,related,bodyClock,pcValue,bodyCode,globals,domain,potential,growth⟩ :=
    original_jumpdest_progress entry frame pc funding code entryClock hFrame pcDomain pcMemory
      leftDomain usedDomain memory enough budget
  have installed : state.code.lookup (ofString "op_jumpdest") =
      some ([],sourceFunctionBody Guest.guestFn_op_jumpdest,.one) := by
    rw [code]; exact originalRuntimeCode_opJumpdest_lookup
  have lookup := pan_no_args_lookup state.code.lookup (ofString "op_jumpdest")
    (sourceFunctionBody Guest.guestFn_op_jumpdest) installed
  have call := evaluateHOLFiniteState_call_return_caller_locals state none (ofString "op_jumpdest") [] []
    (sourceFunctionBody Guest.guestFn_op_jumpdest) HolFiniteMapExact.empty .one (.val (.word 0)) bodyPost
    (by simp [evalListHOLFinite,evalListHOLExact]) lookup (by omega) bodyRun
    (by simp [shapeOfHOLExact,shapeEqHOL])
  have finalClock : bodyPost.clock = state.clock - 3 := by
    rw [bodyClock]
    change state.clock - 1 - 2 = state.clock - 3
    omega
  exact ⟨{bodyPost with locals := state.locals},call,related,finalClock,pcValue,bodyCode,globals,domain,rfl,potential,growth⟩

/-- The zero-gas STOP call spends two clocks including entry, preserves caller
locals and funding, and clears the frame active flag. -/
theorem original_stop_call_progress (state : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame pc : BitVec 64) (funding : GasFunding) (code : state.code = originalRuntimeCode)
    (clock : 2 ≤ state.clock)
    (hFrame : state.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (pcDomain : state.memaddrs (frame + 0)) (pcMemory : state.memory (frame + 0) = .word pc)
    (activeDomain : state.memaddrs (frame + 104)) (memory : HasGasFunding state frame funding) :
    ∃ post, evaluateHOLFiniteState state (.call (some (none,none)) (ofString "op_stop") []) = (none,post) ∧
      post.memory (frame + 104) = .word 0 ∧ HasGasFunding post frame funding ∧
      post.clock = state.clock - 2 ∧ post.memory (frame + 0) = .word (pc + 1) ∧
      post.code = state.code ∧ post.globals = state.globals ∧ post.memaddrs = state.memaddrs ∧
      post.locals = state.locals := by
  let entry := callEntryStateHOLFinite state HolFiniteMapExact.empty
  have entryClock : entry.clock ≠ 0 := by change state.clock - 1 ≠ 0; omega
  obtain ⟨bodyPost,bodyRun,inactive,related,bodyClock,pcValue,bodyCode,globals,domain⟩ :=
    original_stop_progress entry frame pc funding code entryClock hFrame pcDomain pcMemory activeDomain memory
  have installed : state.code.lookup (ofString "op_stop") =
      some ([],sourceFunctionBody Guest.guestFn_op_stop,.one) := by
    rw [code]; exact originalRuntimeCode_opStop_lookup
  have lookup := pan_no_args_lookup state.code.lookup (ofString "op_stop")
    (sourceFunctionBody Guest.guestFn_op_stop) installed
  have call := evaluateHOLFiniteState_call_return_caller_locals state none (ofString "op_stop") [] []
    (sourceFunctionBody Guest.guestFn_op_stop) HolFiniteMapExact.empty .one (.val (.word 0)) bodyPost
    (by simp [evalListHOLFinite,evalListHOLExact]) lookup (by omega) bodyRun
    (by simp [shapeOfHOLExact,shapeEqHOL])
  have finalClock : bodyPost.clock = state.clock - 2 := by
    rw [bodyClock]
    change state.clock - 1 - 1 = state.clock - 2
    omega
  exact ⟨{bodyPost with locals := state.locals},call,inactive,related,finalClock,pcValue,bodyCode,globals,domain,rfl⟩

#print axioms original_jumpdest_call_progress
#print axioms original_stop_call_progress
end InitECandidate.Runtime
