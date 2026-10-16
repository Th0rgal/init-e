import InitECandidate.Runtime.PcAddCall
import InitECandidate.Runtime.ChargeGasCallFootprint
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem source_jumpdest_body : sourceFunctionBody Guest.guestFn_op_jumpdest =
    .seq (.call (some (none,none)) (ofString "charge_gas") [.const 1])
      (.seq (.call (some (none,none)) (ofString "pc_add") [.const 1]) (.return (.const 0))) := by cbv

noncomputable def jumpdestPost (state : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame pc : BitVec 64) (funding : GasFunding) :=
  emptyLocalsHOLFinite (pcAddCallPost (chargeGasCallPost state frame funding 1) frame pc 1)

/-- Full original JUMPDEST execution: both helper calls and the final return. -/
theorem evaluate_source_jumpdest (state : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame pc : BitVec 64) (funding : GasFunding)
    (charge : state.code.lookup (ofString "charge_gas") =
      some ([(ofString "amount",.one)],sourceFunctionBody Guest.guestFn_charge_gas,.one))
    (pcAdd : state.code.lookup (ofString "pc_add") =
      some ([(ofString "n",.one)],sourceFunctionBody Guest.guestFn_pc_add,.one))
    (clock : 2 ≤ state.clock)
    (hFrame : state.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (pcDomain : state.memaddrs (frame + 0)) (pcMemory : state.memory (frame + 0) = .word pc)
    (leftDomain : state.memaddrs (frame + 64)) (usedDomain : state.memaddrs (frame + 184))
    (memory : HasGasFunding state frame funding) (enough : (1 : BitVec 64) ≤ funding.left) :
    evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_op_jumpdest) =
      (some (.returned (.val (.word 0))),jumpdestPost state frame pc funding) := by
  classical
  rw [source_jumpdest_body]
  have arguments (s : PanSemStateFiniteExact 64 Guest.HostMemory) :
      evalListHOLFinite s (h := fun address => Classical.propDecidable (s.memaddrs address)) [.const 1] =
        some [.val (.word 1)] := by simp [evalListHOLFinite,evalListHOLExact,evalHOLExact]
  have charged := evaluate_chargeGas_call state (.const 1) frame 1 funding (arguments state) charge
    (by omega) hFrame leftDomain usedDomain memory enough
  have pcClock : (chargeGasCallPost state frame funding 1).clock ≠ 0 := by
    change state.clock - 1 ≠ 0
    omega
  have advanced := evaluate_pcAdd_call (chargeGasCallPost state frame funding 1) (.const 1) frame pc 1
    (arguments _) pcAdd pcClock hFrame pcDomain (chargeGasCallPost_pc state frame pc 1 funding pcMemory)
  have returned : evaluateHOLFiniteState (pcAddCallPost (chargeGasCallPost state frame funding 1) frame pc 1)
      (.return (.const 0)) = (some (.returned (.val (.word 0))),jumpdestPost state frame pc funding) := by
    simp [evaluateHOLFiniteState_return,evalHOLExact,shapeOfHOLExact,jumpdestPost]
  exact evaluate_seq_none charged (evaluate_seq_none advanced returned)

theorem jumpdestPost_funding (state : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame pc : BitVec 64) (funding : GasFunding) (memory : HasGasFunding state frame funding) :
    HasGasFunding (jumpdestPost state frame pc funding) frame (funding.charge 1) :=
  pcAddCallPost_funding _ frame pc 1 _ (chargeGasCallPost_funding state frame 1 funding memory)

theorem jumpdestPost_clock (state : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame pc : BitVec 64) (funding : GasFunding) :
    (jumpdestPost state frame pc funding).clock = state.clock - 2 := by
  simp [jumpdestPost,pcAddCallPost,chargeGasCallPost,sourceWriteWord,emptyLocalsHOLFinite,Nat.sub_sub]

theorem jumpdest_used_progress (funding : GasFunding) (budget : funding.potential ≤ 200000000)
    (enough : (1 : BitVec 64) ≤ funding.left) :
    (funding.charge 1).used.toNat = funding.used.toNat + 1 := by
  exact funding.charge_used_growth 1 budget enough

#print axioms evaluate_source_jumpdest
#print axioms jumpdestPost_funding
#print axioms jumpdestPost_clock
#print axioms jumpdest_used_progress
end InitECandidate.Runtime
