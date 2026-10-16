import InitECandidate.Runtime.OriginalRuntimeCode
import InitECandidate.Runtime.Jumpdest
import InitECandidate.Runtime.StopOpcode
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Full charged-opcode progress specialized to the actual immutable source
code: JUMPDEST spends one gas and exactly two source body clocks. -/
theorem original_jumpdest_progress (state : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame pc : BitVec 64) (funding : GasFunding) (code : state.code = originalRuntimeCode)
    (clock : 2 ≤ state.clock)
    (hFrame : state.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (pcDomain : state.memaddrs (frame + 0)) (pcMemory : state.memory (frame + 0) = .word pc)
    (leftDomain : state.memaddrs (frame + 64)) (usedDomain : state.memaddrs (frame + 184))
    (memory : HasGasFunding state frame funding) (enough : (1 : BitVec 64) ≤ funding.left)
    (budget : funding.potential ≤ 200000000) :
    ∃ post, evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_op_jumpdest) =
        (some (.returned (.val (.word 0))),post) ∧
      HasGasFunding post frame (funding.charge 1) ∧
      post.clock = state.clock - 2 ∧ post.memory (frame + 0) = .word (pc + 1) ∧
      post.code = state.code ∧ post.globals = state.globals ∧ post.memaddrs = state.memaddrs ∧
      (funding.charge 1).potential = funding.potential ∧
      (funding.charge 1).used.toNat = funding.used.toNat + 1 := by
  have charge : state.code.lookup (ofString "charge_gas") =
      some ([(ofString "amount",.one)],sourceFunctionBody Guest.guestFn_charge_gas,.one) := by
    rw [code]; exact originalRuntimeCode_chargeGas_lookup
  have pcAdd : state.code.lookup (ofString "pc_add") =
      some ([(ofString "n",.one)],sourceFunctionBody Guest.guestFn_pc_add,.one) := by
    rw [code]; exact originalRuntimeCode_pcAdd_lookup
  exact ⟨jumpdestPost state frame pc funding,
    evaluate_source_jumpdest state frame pc funding charge pcAdd clock hFrame pcDomain pcMemory
      leftDomain usedDomain memory enough,
    jumpdestPost_funding state frame pc funding memory,jumpdestPost_clock state frame pc funding,
    pcAddCallPost_pc _ frame pc 1,rfl,rfl,rfl,funding.charge_potential 1 budget enough,
    jumpdest_used_progress funding budget enough⟩

/-- The zero-gas STOP case provides frame termination rather than used-counter
progress, at exactly one body clock and with funding untouched. -/
theorem original_stop_progress (state : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame pc : BitVec 64) (funding : GasFunding) (code : state.code = originalRuntimeCode)
    (clock : state.clock ≠ 0)
    (hFrame : state.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (pcDomain : state.memaddrs (frame + 0)) (pcMemory : state.memory (frame + 0) = .word pc)
    (activeDomain : state.memaddrs (frame + 104)) (memory : HasGasFunding state frame funding) :
    ∃ post, evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_op_stop) =
        (some (.returned (.val (.word 0))),post) ∧
      post.memory (frame + 104) = .word 0 ∧ HasGasFunding post frame funding ∧
      post.clock = state.clock - 1 ∧ post.memory (frame + 0) = .word (pc + 1) ∧
      post.code = state.code ∧ post.globals = state.globals ∧ post.memaddrs = state.memaddrs := by
  have pcAdd : state.code.lookup (ofString "pc_add") =
      some ([(ofString "n",.one)],sourceFunctionBody Guest.guestFn_pc_add,.one) := by
    rw [code]; exact originalRuntimeCode_pcAdd_lookup
  exact ⟨stopOpcodePost state frame pc,
    evaluate_source_stop state frame pc pcAdd clock hFrame pcDomain pcMemory activeDomain,
    stopOpcodePost_inactive state frame pc,stopOpcodePost_funding state frame pc funding memory,
    stopOpcodePost_clock state frame pc,pcAddCallPost_pc _ frame pc 1,rfl,rfl,rfl⟩

#print axioms original_jumpdest_progress
#print axioms original_stop_progress
end InitECandidate.Runtime
