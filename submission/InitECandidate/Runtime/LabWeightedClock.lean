import InitECandidate.Runtime.LabWeightedComposition
import Flapjack.Compiler.Backend.LabProps.ClockSupport
namespace InitECandidate.Runtime.LabToTarget
open Flapjack Flapjack.Compiler.Backend
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem

private theorem shifted_control_successor {F : Type}
    (s : LabSem.State 64 LabToTarget.Config F) (k pc : Nat) (positive : s.clock ≠ 0) :
    updPc pc (decClock { s with clock := s.clock + k }) =
      { updPc pc (decClock s) with clock := (updPc pc (decClock s)).clock + k } := by
  simp only [updPc, decClock]
  congr 1
  omega

/-- A finite successful instruction prefix can be run with any extra label
clock, without changing its visited instructions or local native work. This
lifts prefixes only; it does not claim that a timeout execution is unchanged. -/
theorem WeightedInstructionTrace.add_clock {F : Type} {code : LabProgHOL 64}
    {start final : LabSem.State 64 LabToTarget.Config F} {work : Nat}
    (trace : WeightedInstructionTrace code start final work) (k : Nat) :
    WeightedInstructionTrace code { start with clock := start.clock + k }
      { final with clock := final.clock + k } work := by
  induction trace with
  | nil state => exact .nil _
  | step state final instruction bytes n length clock fetch success rest ih =>
    have sameClock := (asmInstConsts instruction state).2.2.1
    have shifted : incPc (decClock (asmInst instruction
        { state with clock := state.clock + k })) =
        { incPc (decClock (asmInst instruction state)) with
          clock := (incPc (decClock (asmInst instruction state))).clock + k } := by
      rw [LabProps.asmInstWithClock]
      simp only [incPc, decClock, sameClock]
      congr 1
      omega
    apply WeightedInstructionTrace.step _ _ instruction bytes n length
    · show state.clock + k ≠ 0; omega
    · exact fetch
    · simpa only [LabProps.asmInstWithClock] using success
    · rw [shifted]; exact ih
  | jump state final label pc word bytes n length clock fetch destination rest ih =>
    apply WeightedInstructionTrace.jump _ _ label pc word bytes n length
    · show state.clock + k ≠ 0; omega
    · exact fetch
    · exact destination
    · rw [shifted_control_successor state k pc clock]; exact ih
  | jumpReg state final register n1 n2 pc bytes n length clock fetch value destination rest ih =>
    apply WeightedInstructionTrace.jumpReg _ _ register n1 n2 pc bytes n length
    · show state.clock + k ≠ 0; omega
    · exact fetch
    · exact value
    · exact destination
    · rw [shifted_control_successor state k pc clock]; exact ih
  | branchTaken state final comparison register operand label pc word bytes n length
      clock fetch chosen destination rest ih =>
    apply WeightedInstructionTrace.branchTaken _ _ comparison register operand label pc word
      bytes n length
    · show state.clock + k ≠ 0; omega
    · exact fetch
    · simpa only [LabProps.regImmWithClock] using chosen
    · exact destination
    · rw [shifted_control_successor state k pc clock]; exact ih
  | branchFallthrough state final comparison register operand label word bytes n length
      clock fetch chosen rest ih =>
    apply WeightedInstructionTrace.branchFallthrough _ _ comparison register operand label word
      bytes n length
    · show state.clock + k ≠ 0; omega
    · exact fetch
    · simpa only [LabProps.regImmWithClock] using chosen
    · change WeightedInstructionTrace code (updPc (state.pc + 1)
        (decClock { state with clock := state.clock + k })) _ _
      rw [shifted_control_successor state k (state.pc + 1) clock]
      exact ih
  | locValue state final register label pc word bytes n length clock fetch destination rest ih =>
    apply WeightedInstructionTrace.locValue _ _ register label pc word bytes n length
    · show state.clock + k ≠ 0; omega
    · exact fetch
    · exact destination
    · change WeightedInstructionTrace code (updPc (state.pc + 1)
        (decClock { updReg register (labToLoc label) state with
          clock := (updReg register (labToLoc label) state).clock + k })) _ _
      rw [shifted_control_successor (updReg register (labToLoc label) state) k
        (state.pc + 1) (by exact clock)]
      exact ih

#print axioms WeightedInstructionTrace.add_clock
end InitECandidate.Runtime.LabToTarget
