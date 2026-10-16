import Flapjack.Compiler.Backend.LabToTarget.InstLemma
import InitECandidate.Runtime.NopBudget
import Flapjack.Compiler.Backend.LabToTarget.CompileCorrect.Step

namespace InitECandidate.Runtime.LabToTarget
open Flapjack Flapjack.RiscV.L3
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.AsmSem
open Flapjack.Compiler.Encoders.AsmProps Flapjack.Compiler.Backend.Semantics.TargetProps
open Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.LabToTarget Flapjack.Compiler.Encoders.RiscV.Target

theorem line_memory_bounded {F σ : Type}
    {mc : MachineConfig 64 riscv_state RiscVProjection} {code2 : LabProgHOL 64} {labs : Spt (Spt Nat)}
    {p : BitVec 64} {s1 : LabSem.State 64 Config F} {t1 : AsmState 64} {ms1 : riscv_state}
    (io : HolFfiState σ) (target : mc.target = riscvTarget) (hrel : stateRel (mc, code2, labs, p) s1 t1 ms1)
    (hec : encoderCorrect mc.target) (instr : HolAsm 64) (bytes' : List (BitVec 8))
    (hmem : bytesInMemHOL (p + BitVec.ofNat 64 (posVal s1.pc 0 code2)) bytes' t1.mem
      t1.memDomain (fun a => s1.memDomain a = true))
    (henc : encWithNop mc.target.config.encode instr bytes')
    (hok : asmOkExact instr mc.target.config = true)
    (hdis : ffiEntryPcsDisjoint mc t1 bytes'.length)
    (hnf : ¬ (asmUpd instr (t1.pc + BitVec.ofNat 64 bytes'.length) t1).failed)
    (hb2 : bytesInMemoryHOL t1.pc bytes'
      (asmUpd instr (t1.pc + BitVec.ofNat 64 bytes'.length) t1).mem t1.memDomain)
    (hcall : ∀ x, instr ≠ .call x) :
    ∃ l ms2, l ≤ 16 * (bytes'.length + 1) ∧ ∀ k,
      evaluateTargetHOL mc io (k + l) ms1 = evaluateTargetHOL (shiftInterfer l mc) io k ms2 ∧
      findNextInterference mc io (k + l) ms1 =
        findNextInterference (shiftInterfer l mc) io k ms2 ∧
      targetStateRel mc.target (asmUpd instr (t1.pc + BitVec.ofNat 64 bytes'.length) t1)
        ms2 ∧
      l ≠ 0 := by
  obtain ⟨c1, -, c3, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    c27, -, -, -, -, -, -, -, -, -, -, -, -, -, htpc, -, c43, c44, c45, -⟩ := hrel
  have hb := bytesInMem_impliesMemory _ _ _ _ _ hmem
  rw [← htpc] at hb
  apply NopBudget.padded_step_bounded mc t1 ms1 io instr _ bytes' target
  refine ⟨hec, c3, hdis, c27, hb2, ?_, rfl, c1, hcall⟩
  exact ⟨hb, henc, c43, c44, c45, rfl, hnf, hok⟩

/-- Simulate a whole NOP-padded line `bytes'` encoding the non-`Call`
instruction `instr` (`asm_step_IMP_evaluate_step_nop`), when the instruction
leaves memory unchanged outside the source memory domain. -/
theorem line_bounded {F σ : Type}
    {mc : MachineConfig 64 riscv_state RiscVProjection} {code2 : LabProgHOL 64} {labs : Spt (Spt Nat)}
    {p : BitVec 64} {s1 : LabSem.State 64 Config F} {t1 : AsmState 64} {ms1 : riscv_state}
    (io : HolFfiState σ) (target : mc.target = riscvTarget) (hrel : stateRel (mc, code2, labs, p) s1 t1 ms1)
    (hec : encoderCorrect mc.target) (instr : HolAsm 64) (bytes' : List (BitVec 8))
    (hmem : bytesInMemHOL (p + BitVec.ofNat 64 (posVal s1.pc 0 code2)) bytes' t1.mem
      t1.memDomain (fun a => s1.memDomain a = true))
    (henc : encWithNop mc.target.config.encode instr bytes')
    (hok : asmOkExact instr mc.target.config = true)
    (hdis : ffiEntryPcsDisjoint mc t1 bytes'.length)
    (hnf : ¬ (asmUpd instr (t1.pc + BitVec.ofNat 64 bytes'.length) t1).failed)
    (hmemeq : ∀ a, ¬ s1.memDomain a = true →
      (asmUpd instr (t1.pc + BitVec.ofNat 64 bytes'.length) t1).mem a = t1.mem a)
    (hcall : ∀ x, instr ≠ .call x) :
    ∃ l ms2, l ≤ 16 * (bytes'.length + 1) ∧ ∀ k,
      evaluateTargetHOL mc io (k + l) ms1 = evaluateTargetHOL (shiftInterfer l mc) io k ms2 ∧
      findNextInterference mc io (k + l) ms1 =
        findNextInterference (shiftInterfer l mc) io k ms2 ∧
      targetStateRel mc.target (asmUpd instr (t1.pc + BitVec.ofNat 64 bytes'.length) t1)
        ms2 ∧
      l ≠ 0 := by
  obtain ⟨c1, -, c3, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    c27, -, -, -, -, -, -, -, -, -, -, -, -, -, htpc, -, c43, c44, c45, -⟩ := hrel
  have hb := bytesInMem_impliesMemory _ _ _ _ _ hmem
  rw [← htpc] at hb
  have hb2 := bytesInMem_impliesMemory_change _ t1.mem
    (asmUpd instr (t1.pc + BitVec.ofNat 64 bytes'.length) t1).mem _ bytes' _
    (fun a ha => (hmemeq a ha).symm) hmem
  rw [← htpc] at hb2
  apply NopBudget.padded_step_bounded mc t1 ms1 io instr _ bytes' target
  refine ⟨hec, c3, hdis, c27, hb2, ?_, rfl, c1, hcall⟩
  exact ⟨hb, henc, c43, c44, c45, rfl, hnf, hok⟩


/-- A fetched ordinary label instruction obtains all line guards from the
compiler relation, then executes in a bounded native prefix. -/
theorem fetched_inst_bounded {F : Type}
    (s1 : LabSem.State 64 Config F) (i : HolInst 64)
    (mc : MachineConfig 64 riscv_state RiscVProjection) (code2 : LabProgHOL 64)
    (labs : Spt (Spt Nat)) (p : BitVec 64) (t1 : AsmState 64) (ms1 : riscv_state)
    (bytes : List (BitVec 8)) (n : Nat)
    (target : mc.target = riscvTarget)
    (hfetch : asmFetch s1 = some (.asm (.asmi (.inst i)) bytes n))
    (hf : ¬ (asmInst i s1).failed)
    (hec : encoderCorrect mc.target)
    (hrel : stateRel (mc, code2, labs, p) s1 t1 ms1) :
    ∃ (encoded : List (BitVec 8)), ∃ count ms2, count ≤ 16 * (encoded.length + 1) ∧ count ≠ 0 ∧
      (∀ clock, evaluateTargetHOL mc s1.ffi (clock + count) ms1 =
        evaluateTargetHOL (shiftInterfer count mc) s1.ffi clock ms2) ∧
      stateRel (shiftInterfer count mc, code2, labs, p)
        (incPc (decClock (asmInst i s1)))
        (Flapjack.Compiler.Encoders.AsmSem.updPc (t1.pc + BitVec.ofNat 64 encoded.length) (Flapjack.Compiler.Encoders.AsmSem.instUpd i t1)) ms2 := by
  obtain ⟨encoded, length, hok, hmem, hpos, hdis⟩ :=
    fetchedAsmLine hrel hfetch (by intro op re a h; cases h)
  simp only [lineOk, cbwToAsmHOL] at hok
  obtain ⟨htf, hout, hpost⟩ := instLemma i s1 mc code2 labs p t1 ms1 encoded ms1
    ⟨hf, hrel, hpos⟩
  obtain ⟨count, ms2, bound, run⟩ := line_bounded s1.ffi target hrel hec (.inst i) encoded
    hmem hok.1 hok.2.2 hdis (by simpa [asmUpd, Flapjack.Compiler.Encoders.AsmSem.updPc] using htf)
    (fun a ha => by simpa [asmUpd, Flapjack.Compiler.Encoders.AsmSem.updPc] using hout a ha) (by intro x h; cases h)
  have related := (instLemma i s1 mc code2 labs p t1 ms1 encoded ms2 ⟨hf, hrel, hpos⟩).2.2
    (run 0).2.2.1
  exact ⟨encoded, count, ms2, bound, (run 0).2.2.2, fun clock => (run clock).1,
    stateRel_shiftInterfer _ _ _ _ _ _ _ count related⟩

end InitECandidate.Runtime.LabToTarget
#print axioms InitECandidate.Runtime.LabToTarget.line_bounded
#print axioms InitECandidate.Runtime.LabToTarget.line_memory_bounded

#print axioms InitECandidate.Runtime.LabToTarget.fetched_inst_bounded
