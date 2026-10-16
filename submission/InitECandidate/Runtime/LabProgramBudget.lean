import InitECandidate.Runtime.LabLineBudget
import Flapjack.Compiler.Backend.LabToTarget.EncodingValidity

namespace InitECandidate.Runtime.LabToTarget
open Flapjack Flapjack.RiscV.L3
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.AsmSem
open Flapjack.Compiler.Encoders.AsmProps Flapjack.Compiler.Backend.Semantics.TargetProps
open Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.LabToTarget Flapjack.Compiler.Encoders.RiscV.Target

/-- Fixed per-label-step ceiling, including any line padding. -/
def labStepCeiling (code : LabProgHOL 64) : Nat := 16 * ((progToBytes code).length + 1)

theorem related_position_bound {F : Type}
    {s1 : LabSem.State 64 Config F} {mc : MachineConfig 64 riscv_state RiscVProjection}
    {code : LabProgHOL 64} {labs : Spt (Spt Nat)} {p : BitVec 64}
    {asm : AsmState 64} {machine : riscv_state}
    (related : stateRel (mc, code, labs, p) s1 asm machine) (index : Nat) :
    posVal index 0 code ≤ (progToBytes code).length := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, valid, -, -, -, -, -, -⟩ := related
  simpa only [Nat.zero_add] using posVal_bound index 0 code mc.target.config labs
    (mc.ffiNames.take (holThe (mmioPcsMinIndex mc.ffiNames))) 0 valid

/-- The actual position delta ties a fetched line's byte-count witness to the
fixed program, so the line ceiling can be used repeatedly in recursion. -/
theorem related_line_count_bound {F : Type}
    {s1 : LabSem.State 64 Config F} {mc : MachineConfig 64 riscv_state RiscVProjection}
    {code : LabProgHOL 64} {labs : Spt (Spt Nat)} {p : BitVec 64}
    {asm : AsmState 64} {machine : riscv_state}
    (related : stateRel (mc, code, labs, p) s1 asm machine)
    (encoded : List (BitVec 8)) (count : Nat)
    (position : posVal (s1.pc + 1) 0 code = posVal s1.pc 0 code + encoded.length)
    (bound : count ≤ 16 * (encoded.length + 1)) : count ≤ labStepCeiling code := by
  have total := related_position_bound related (s1.pc + 1)
  have lengthBound : encoded.length ≤ (progToBytes code).length := by omega
  exact bound.trans (Nat.mul_le_mul_left 16 (Nat.add_le_add_right lengthBound 1))

theorem fetched_inst_uniform_bound {F : Type}
    (s1 : LabSem.State 64 Config F) (i : HolInst 64)
    (mc : MachineConfig 64 riscv_state RiscVProjection) (code2 : LabProgHOL 64)
    (labs : Spt (Spt Nat)) (p : BitVec 64) (t1 : AsmState 64) (ms1 : riscv_state)
    (bytes : List (BitVec 8)) (n : Nat)
    (target : mc.target = riscvTarget)
    (hfetch : asmFetch s1 = some (.asm (.asmi (.inst i)) bytes n))
    (hf : ¬ (asmInst i s1).failed)
    (hec : encoderCorrect mc.target)
    (hrel : stateRel (mc, code2, labs, p) s1 t1 ms1) :
    ∃ count ms2 asm2, count ≤ labStepCeiling code2 ∧ count ≠ 0 ∧
      (∀ clock, evaluateTargetHOL mc s1.ffi (clock + count) ms1 =
        evaluateTargetHOL (shiftInterfer count mc) s1.ffi clock ms2) ∧
      stateRel (shiftInterfer count mc, code2, labs, p)
        (incPc (decClock (asmInst i s1))) asm2 ms2 := by
  obtain ⟨encoded, count, ms2, position, bound, positive, run, related⟩ :=
    fetched_inst_bounded s1 i mc code2 labs p t1 ms1 bytes n target hfetch hf hec hrel
  exact ⟨count, ms2, _, related_line_count_bound hrel encoded count position bound,
    positive, run, related⟩

end InitECandidate.Runtime.LabToTarget
#print axioms InitECandidate.Runtime.LabToTarget.related_line_count_bound

#print axioms InitECandidate.Runtime.LabToTarget.fetched_inst_uniform_bound
