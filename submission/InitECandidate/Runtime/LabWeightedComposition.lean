import InitECandidate.Runtime.LabWeightedMixedTrace
namespace InitECandidate.Runtime.LabToTarget
open Flapjack Flapjack.Compiler.Backend
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem

/-- Reached instruction blocks compose by addition of their actual local
expansion work. No new terminal allowance or per-block maximum is introduced. -/
theorem weightedInstructionTrace_append {F : Type} {code : LabProgHOL 64}
    {start middle final : LabSem.State 64 LabToTarget.Config F} {left right : Nat}
    (first : WeightedInstructionTrace code start middle left)
    (second : WeightedInstructionTrace code middle final right) :
    WeightedInstructionTrace code start final (left + right) := by
  induction first generalizing final right with
  | nil state => simpa using second
  | step state endpoint instruction bytes n length clock fetch success rest ih =>
    have joined := WeightedInstructionTrace.step state final instruction bytes n _ clock fetch
      success (ih second)
    simpa only [Nat.add_right_comm] using joined
  | jump state endpoint label pc word bytes n length clock fetch destination rest ih =>
    have joined := WeightedInstructionTrace.jump state final label pc word bytes n _ clock fetch
      destination (ih second)
    simpa only [Nat.add_right_comm] using joined
  | jumpReg state endpoint register n1 n2 pc bytes n length clock fetch value destination rest ih =>
    have joined := WeightedInstructionTrace.jumpReg state final register n1 n2 pc bytes n _ clock
      fetch value destination (ih second)
    simpa only [Nat.add_right_comm] using joined
  | branchTaken state endpoint comparison register operand label pc word bytes n length
      clock fetch chosen destination rest ih =>
    have joined := WeightedInstructionTrace.branchTaken state final comparison register operand
      label pc word bytes n _ clock fetch chosen destination (ih second)
    simpa only [Nat.add_right_comm] using joined
  | branchFallthrough state endpoint comparison register operand label word bytes n length
      clock fetch chosen rest ih =>
    have joined := WeightedInstructionTrace.branchFallthrough state final comparison register
      operand label word bytes n _ clock fetch chosen (ih second)
    simpa only [Nat.add_right_comm] using joined
  | locValue state endpoint register label pc word bytes n length clock fetch destination rest ih =>
    have joined := WeightedInstructionTrace.locValue state final register label pc word bytes n _
      clock fetch destination (ih second)
    simpa only [Nat.add_right_comm] using joined

/-- External/shared operations keep their existing per-event costs when
blocks compose; the terminal allowance belongs only at the final exit. -/
theorem weightedMixedTrace_append {F : Type} {code : LabProgHOL 64}
    {start middle final : LabSem.State 64 LabToTarget.Config F} {left right : Nat}
    (first : WeightedMixedTrace code start middle left)
    (second : WeightedMixedTrace code middle final right) :
    WeightedMixedTrace code start final (left + right) := by
  induction first generalizing final right with
  | nil state => simpa using second
  | ordinary start middle endpoint length restLength segment rest ih =>
    have joined := WeightedMixedTrace.ordinary start middle final length _ segment (ih second)
    simpa only [Nat.add_assoc] using joined
  | ffi state endpoint name word bytes n len ptr len2 ptr2 conf bytes2 n1 n2 pc newFfi newBytes
      length clock fetch hlen hptr hlen2 hptr2 read1 read2 link destination call rest ih =>
    have joined := WeightedMixedTrace.ffi state final name word bytes n len ptr len2 ptr2
      conf bytes2 n1 n2 pc newFfi newBytes _ clock fetch hlen hptr hlen2 hptr2 read1 read2
      link destination call (ih second)
    simpa only [Nat.add_right_comm] using joined
  | shared state endpoint operator register base offset bytes n ffi returned next length
      clock fetch operation rest ih =>
    have joined := WeightedMixedTrace.shared state final operator register base offset bytes n
      ffi returned next _ clock fetch operation (ih second)
    simpa only [Nat.add_right_comm] using joined

#print axioms weightedMixedTrace_append
#print axioms weightedInstructionTrace_append
end InitECandidate.Runtime.LabToTarget
