import InitECandidate.Runtime.DispatchProgress
import InitECandidate.Runtime.OriginalDispatchCode
import InitECandidate.Runtime.PanSingleWordLookup
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Actual run_frames-style dispatcher call on its successful opcode path.
The handler is arbitrary and caller locals are restored. -/
theorem original_dispatch_jumpdest_call_progress (state : PanSemStateFiniteExact 64 Guest.HostMemory)
    (argument : ExpHOL 64) (handler : Option (MlS × MlS × ProgHOL 64))
    (arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) [argument] = some [.val (.word 91)])
    (frame pc : BitVec 64) (funding : GasFunding) (code : state.code = originalRuntimeCode)
    (clock : 4 ≤ state.clock)
    (hFrame : state.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (pcDomain : state.memaddrs (frame + 0)) (pcMemory : state.memory (frame + 0) = .word pc)
    (leftDomain : state.memaddrs (frame + 64)) (usedDomain : state.memaddrs (frame + 184))
    (memory : HasGasFunding state frame funding) (enough : (1 : BitVec 64) ≤ funding.left)
    (budget : funding.potential ≤ 200000000) :
    ∃ post, evaluateHOLFiniteState state (.call (some (none,handler)) (ofString "op_dispatch") [argument]) = (none,post) ∧
      HasGasFunding post frame (funding.charge 1) ∧
      post.clock = state.clock - 4 ∧ post.memory (frame + 0) = .word (pc + 1) ∧
      post.code = state.code ∧ post.globals = state.globals ∧ post.memaddrs = state.memaddrs ∧
      post.locals = state.locals ∧ (funding.charge 1).potential = funding.potential ∧
      (funding.charge 1).used.toNat = funding.used.toNat + 1 := by
  let callee : HolFiniteMapExact MlS (ValueHOL 64) :=
    HolFiniteMapExact.empty.update (ofString "op",.val (.word 91))
  let entry := callEntryStateHOLFinite state callee
  have opcode : entry.locals.lookup (ofString "op") = some (.val (.word 91)) := by
    simp [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE]
  have entryClock : 3 ≤ entry.clock := by change 3 ≤ state.clock - 1; omega
  obtain ⟨bodyPost,bodyRun,related,bodyClock,pcValue,bodyCode,globals,domain,locals,potential,growth⟩ :=
    original_dispatch_jumpdest_progress entry frame pc funding code opcode entryClock hFrame pcDomain pcMemory
      leftDomain usedDomain memory enough budget
  have installed : state.code.lookup (ofString "op_dispatch") =
      some ([(ofString "op",.one)],sourceFunctionBody Guest.guestFn_op_dispatch,.one) := by
    rw [code]; exact originalRuntimeCode_dispatch_lookup
  have lookup := pan_single_word_lookup state.code.lookup (ofString "op_dispatch") (ofString "op")
    (sourceFunctionBody Guest.guestFn_op_dispatch) 91 installed
  have call := evaluateHOLFiniteState_call_return_caller_locals state handler (ofString "op_dispatch") [argument] [.val (.word 91)]
    (sourceFunctionBody Guest.guestFn_op_dispatch) callee .one (.val (.word 0)) bodyPost
    arguments lookup (by omega) bodyRun (by simp [shapeOfHOLExact,shapeEqHOL])
  have finalClock : bodyPost.clock = state.clock - 4 := by
    rw [bodyClock]
    change state.clock - 1 - 3 = state.clock - 4
    omega
  exact ⟨{bodyPost with locals := state.locals},call,related,finalClock,pcValue,bodyCode,globals,domain,rfl,potential,growth⟩

#print axioms original_dispatch_jumpdest_call_progress

/-- Actual run_frames-style dispatcher call on its successful opcode path.
The handler is arbitrary and caller locals are restored. -/
theorem original_dispatch_stop_call_progress (state : PanSemStateFiniteExact 64 Guest.HostMemory)
    (argument : ExpHOL 64) (handler : Option (MlS × MlS × ProgHOL 64))
    (arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) [argument] = some [.val (.word 0)])
    (frame pc : BitVec 64) (funding : GasFunding) (code : state.code = originalRuntimeCode)
    (clock : 3 ≤ state.clock)
    (hFrame : state.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (pcDomain : state.memaddrs (frame + 0)) (pcMemory : state.memory (frame + 0) = .word pc)
    (activeDomain : state.memaddrs (frame + 104)) (memory : HasGasFunding state frame funding) :
    ∃ post, evaluateHOLFiniteState state (.call (some (none,handler)) (ofString "op_dispatch") [argument]) = (none,post) ∧
      post.memory (frame + 104) = .word 0 ∧ HasGasFunding post frame funding ∧
      post.clock = state.clock - 3 ∧ post.memory (frame + 0) = .word (pc + 1) ∧
      post.code = state.code ∧ post.globals = state.globals ∧ post.memaddrs = state.memaddrs ∧
      post.locals = state.locals ∧
      (∀ address, address ≠ frame + 0 → address ≠ frame + 104 → post.memory address = state.memory address) := by
  let callee : HolFiniteMapExact MlS (ValueHOL 64) :=
    HolFiniteMapExact.empty.update (ofString "op",.val (.word 0))
  let entry := callEntryStateHOLFinite state callee
  have opcode : entry.locals.lookup (ofString "op") = some (.val (.word 0)) := by
    simp [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE]
  have entryClock : 2 ≤ entry.clock := by change 2 ≤ state.clock - 1; omega
  obtain ⟨bodyPost,bodyRun,inactive,related,bodyClock,pcValue,bodyCode,globals,domain,locals,footprint⟩ :=
    original_dispatch_stop_progress entry frame pc funding code opcode entryClock hFrame pcDomain pcMemory activeDomain memory
  have installed : state.code.lookup (ofString "op_dispatch") =
      some ([(ofString "op",.one)],sourceFunctionBody Guest.guestFn_op_dispatch,.one) := by
    rw [code]; exact originalRuntimeCode_dispatch_lookup
  have lookup := pan_single_word_lookup state.code.lookup (ofString "op_dispatch") (ofString "op")
    (sourceFunctionBody Guest.guestFn_op_dispatch) 0 installed
  have call := evaluateHOLFiniteState_call_return_caller_locals state handler (ofString "op_dispatch") [argument] [.val (.word 0)]
    (sourceFunctionBody Guest.guestFn_op_dispatch) callee .one (.val (.word 0)) bodyPost
    arguments lookup (by omega) bodyRun (by simp [shapeOfHOLExact,shapeEqHOL])
  have finalClock : bodyPost.clock = state.clock - 3 := by
    rw [bodyClock]
    change state.clock - 1 - 2 = state.clock - 3
    omega
  exact ⟨{bodyPost with locals := state.locals},call,inactive,related,finalClock,pcValue,bodyCode,globals,domain,rfl,footprint⟩

#print axioms original_dispatch_stop_call_progress
end InitECandidate.Runtime
