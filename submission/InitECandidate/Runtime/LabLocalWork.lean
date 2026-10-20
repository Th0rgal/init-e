import InitECandidate.Runtime.LabProgramBudget

namespace InitECandidate.Runtime.LabToTarget
open Flapjack Flapjack.RiscV.L3
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.AsmSem
open Flapjack.Compiler.Encoders.AsmProps Flapjack.Compiler.Backend.Semantics.TargetProps
open Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.LabToTarget Flapjack.Compiler.Encoders.RiscV.Target

/-- Charge only the expansion of the visited label instruction, including padding.
Unvisited instructions elsewhere in the program contribute nothing. -/
def labLineWork (code : LabProgHOL 64) (pc : Nat) : Nat :=
  16 * ((posVal (pc + 1) 0 code - posVal pc 0 code) + 1)

 theorem line_count_local_bound (code : LabProgHOL 64) (pc : Nat)
    (encoded : List (BitVec 8)) (count : Nat)
    (position : posVal (pc + 1) 0 code = posVal pc 0 code + encoded.length)
    (bound : count ≤ 16 * (encoded.length + 1)) :
    count ≤ labLineWork code pc := by
  have delta : posVal (pc + 1) 0 code - posVal pc 0 code = encoded.length := by omega
  simpa only [labLineWork, delta] using bound

theorem fetched_inst_local_bound {F : Type}
    (s1 : LabSem.State 64 Config F) (i : HolInst 64)
    (mc : MachineConfig 64 riscv_state RiscVProjection) (code2 : LabProgHOL 64)
    (labs : Spt (Spt Nat)) (p : BitVec 64) (t1 : AsmState 64) (ms1 : riscv_state)
    (bytes : List (BitVec 8)) (n : Nat)
    (target : mc.target = riscvTarget)
    (hfetch : asmFetch s1 = some (.asm (.asmi (.inst i)) bytes n))
    (hf : ¬ (asmInst i s1).failed)
    (hec : encoderCorrect mc.target)
    (hrel : stateRel (mc, code2, labs, p) s1 t1 ms1) :
    ∃ count ms2 asm2, count ≤ labLineWork code2 s1.pc ∧ count ≠ 0 ∧
      (∀ clock, evaluateTargetHOL mc s1.ffi (clock + count) ms1 =
        evaluateTargetHOL (shiftInterfer count mc) s1.ffi clock ms2) ∧
      (∀ clock, findNextInterference mc s1.ffi (clock + count) ms1 =
        findNextInterference (shiftInterfer count mc) s1.ffi clock ms2) ∧
      stateRel (shiftInterfer count mc, code2, labs, p)
        (incPc (decClock (asmInst i s1))) asm2 ms2 := by
  obtain ⟨encoded, count, ms2, position, bound, positive, run, search, related⟩ :=
    fetched_inst_bounded s1 i mc code2 labs p t1 ms1 bytes n target hfetch hf hec hrel
  exact ⟨count, ms2, _, line_count_local_bound code2 s1.pc encoded count position bound,
    positive, run, search, related⟩

end InitECandidate.Runtime.LabToTarget
#print axioms InitECandidate.Runtime.LabToTarget.fetched_inst_local_bound
