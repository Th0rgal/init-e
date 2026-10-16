import InitECandidate.Runtime.OpcodeCallProgress
import InitECandidate.Runtime.DispatchJumpdestPath
import InitECandidate.Runtime.DispatchStopPath
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Actual dispatcher branch, including selection and the terminal return. -/
theorem original_dispatch_jumpdest_progress (state : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame pc : BitVec 64) (funding : GasFunding) (code : state.code = originalRuntimeCode)
    (opcode : state.locals.lookup (ofString "op") = some (.val (.word 91)))
    (clock : 3 ≤ state.clock)
    (hFrame : state.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (pcDomain : state.memaddrs (frame + 0)) (pcMemory : state.memory (frame + 0) = .word pc)
    (leftDomain : state.memaddrs (frame + 64)) (usedDomain : state.memaddrs (frame + 184))
    (memory : HasGasFunding state frame funding) (enough : (1 : BitVec 64) ≤ funding.left)
    (budget : funding.potential ≤ 200000000) :
    ∃ post, evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_op_dispatch) = (some (.returned (.val (.word 0))),post) ∧
      HasGasFunding post frame (funding.charge 1) ∧
      post.clock = state.clock - 3 ∧ post.memory (frame + 0) = .word (pc + 1) ∧
      post.code = state.code ∧ post.globals = state.globals ∧ post.memaddrs = state.memaddrs ∧
      post.locals = HolFiniteMapExact.empty ∧ (funding.charge 1).potential = funding.potential ∧
      (funding.charge 1).used.toNat = funding.used.toNat + 1 := by
  obtain ⟨stepPost,stepRun,related,clockValue,pcValue,codeValue,globals,domain,locals,potential,growth⟩ :=
    original_jumpdest_call_progress state frame pc funding code clock hFrame pcDomain pcMemory leftDomain usedDomain memory enough budget
  have run := evaluate_dispatch_jumpdest_path state stepPost opcode stepRun
  exact ⟨emptyLocalsHOLFinite stepPost,run,related,clockValue,pcValue,codeValue,globals,domain,rfl,potential,growth⟩

#print axioms original_dispatch_jumpdest_progress

/-- Actual dispatcher branch, including selection and the terminal return. -/
theorem original_dispatch_stop_progress (state : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame pc : BitVec 64) (funding : GasFunding) (code : state.code = originalRuntimeCode)
    (opcode : state.locals.lookup (ofString "op") = some (.val (.word 0)))
    (clock : 2 ≤ state.clock)
    (hFrame : state.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (pcDomain : state.memaddrs (frame + 0)) (pcMemory : state.memory (frame + 0) = .word pc)
    (activeDomain : state.memaddrs (frame + 104)) (memory : HasGasFunding state frame funding) :
    ∃ post, evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_op_dispatch) = (some (.returned (.val (.word 0))),post) ∧
      post.memory (frame + 104) = .word 0 ∧ HasGasFunding post frame funding ∧
      post.clock = state.clock - 2 ∧ post.memory (frame + 0) = .word (pc + 1) ∧
      post.code = state.code ∧ post.globals = state.globals ∧ post.memaddrs = state.memaddrs ∧
      post.locals = HolFiniteMapExact.empty := by
  obtain ⟨stepPost,stepRun,inactive,related,clockValue,pcValue,codeValue,globals,domain,locals⟩ :=
    original_stop_call_progress state frame pc funding code clock hFrame pcDomain pcMemory activeDomain memory
  have run := evaluate_dispatch_stop_path state stepPost opcode stepRun
  exact ⟨emptyLocalsHOLFinite stepPost,run,inactive,related,clockValue,pcValue,codeValue,globals,domain,rfl⟩

#print axioms original_dispatch_stop_progress
end InitECandidate.Runtime
