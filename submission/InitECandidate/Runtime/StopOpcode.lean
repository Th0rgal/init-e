import InitECandidate.Runtime.PcAddCall
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem source_stop_body : sourceFunctionBody Guest.guestFn_op_stop =
    .seq (.store (fundingAddress 104) (.const 0))
      (.seq (.call (some (none,none)) (ofString "pc_add") [.const 1]) (.return (.const 0))) := by cbv

noncomputable def stopOpcodePost {F : Type} (state : PanSemStateFiniteExact 64 F)
    (frame pc : BitVec 64) :=
  emptyLocalsHOLFinite (pcAddCallPost (sourceWriteWord state (frame + 104) 0) frame pc 1)

/-- Full original STOP execution takes one body clock and ends the frame,
providing the progress alternative for this opcode which charges no gas. -/
theorem evaluate_source_stop {F : Type} (state : PanSemStateFiniteExact 64 F)
    (frame pc : BitVec 64)
    (pcAdd : state.code.lookup (ofString "pc_add") =
      some ([(ofString "n",.one)],sourceFunctionBody Guest.guestFn_pc_add,.one))
    (clock : state.clock ≠ 0)
    (hFrame : state.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (pcDomain : state.memaddrs (frame + 0)) (pcMemory : state.memory (frame + 0) = .word pc)
    (activeDomain : state.memaddrs (frame + 104)) :
    evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_op_stop) =
      (some (.returned (.val (.word 0))),stopOpcodePost state frame pc) := by
  classical
  rw [source_stop_body]
  let cleared := sourceWriteWord state (frame + 104) 0
  have stored : evaluateHOLFiniteState state (.store (fundingAddress 104) (.const 0)) =
      (none,cleared) := evaluate_store_word state (frame + 104) 0 _ _
        (eval_fundingAddress state frame 104 hFrame) (by rfl) activeDomain
  have arguments : evalListHOLFinite cleared
      (h := fun address => Classical.propDecidable (cleared.memaddrs address)) [.const 1] =
        some [.val (.word 1)] := by simp [evalListHOLFinite,evalListHOLExact,evalHOLExact]
  have preserved : cleared.memory (frame + 0) = .word pc := by
    simpa [cleared,sourceWriteWord] using pcMemory
  have advanced := evaluate_pcAdd_call cleared (.const 1) frame pc 1 arguments pcAdd clock hFrame pcDomain preserved
  have returned : evaluateHOLFiniteState (pcAddCallPost cleared frame pc 1) (.return (.const 0)) =
      (some (.returned (.val (.word 0))),stopOpcodePost state frame pc) := by
    simp [evaluateHOLFiniteState_return,evalHOLExact,shapeOfHOLExact,stopOpcodePost,cleared]
  exact evaluate_seq_none stored (evaluate_seq_none advanced returned)

theorem stopOpcodePost_inactive {F : Type} (state : PanSemStateFiniteExact 64 F) (frame pc : BitVec 64) :
    (stopOpcodePost state frame pc).memory (frame + 104) = .word 0 := by
  simp [stopOpcodePost,pcAddCallPost,sourceWriteWord,emptyLocalsHOLFinite]

theorem stopOpcodePost_clock {F : Type} (state : PanSemStateFiniteExact 64 F) (frame pc : BitVec 64) :
    (stopOpcodePost state frame pc).clock = state.clock - 1 := rfl

theorem stopOpcodePost_funding {F : Type} (state : PanSemStateFiniteExact 64 F)
    (frame pc : BitVec 64) (funding : GasFunding) (memory : HasGasFunding state frame funding) :
    HasGasFunding (stopOpcodePost state frame pc) frame funding := by
  have preserved : HasGasFunding (sourceWriteWord state (frame + 104) 0) frame funding := by
    simpa [HasGasFunding,sourceWriteWord] using memory
  exact pcAddCallPost_funding _ frame pc 1 funding preserved

#print axioms evaluate_source_stop
#print axioms stopOpcodePost_inactive
#print axioms stopOpcodePost_clock
#print axioms stopOpcodePost_funding
end InitECandidate.Runtime
