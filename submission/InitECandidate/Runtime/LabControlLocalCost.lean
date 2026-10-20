import Flapjack.Compiler.Backend.LabToTarget.CompileCorrect.Control
import Flapjack.Compiler.Backend.LabToTarget.CompileCorrect.Asm
import Flapjack.Compiler.Backend.LabToTarget.InstLemma
import InitECandidate.Runtime.LabInstructionLocalCost
import Flapjack.Compiler.Backend.LabToTarget.CompileCorrect.Step

namespace InitECandidate.Runtime.LabToTarget.LocalCost
open Flapjack Flapjack.RiscV.L3
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.AsmSem
open Flapjack.Compiler.Encoders.AsmProps Flapjack.Compiler.Backend.Semantics.TargetProps
open Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.LabToTarget Flapjack.Compiler.Encoders.RiscV.Target

theorem leading_line_bounded {F σ : Type}
    {mc : MachineConfig 64 riscv_state RiscVProjection} {code2 : LabProgHOL 64} {labs : Spt (Spt Nat)}
    {p : BitVec 64} {s1 : LabSem.State 64 Config F} {t1 : AsmState 64} {ms1 : riscv_state}
    (io : HolFfiState σ) (target : mc.target = riscvTarget) (hrel : stateRel (mc, code2, labs, p) s1 t1 ms1)
    (hec : encoderCorrect mc.target) (instr : HolAsm 64) (bytes' : List (BitVec 8))
    (hmem : bytesInMemHOL (p + BitVec.ofNat 64 (posVal s1.pc 0 code2)) bytes' t1.mem
      t1.memDomain (fun a => s1.memDomain a = true))
    (henc : encWithNop mc.target.config.encode instr bytes')
    (hok : asmOkExact instr mc.target.config = true)
    (hdis : ffiEntryPcsDisjoint mc t1 bytes'.length)
    (hnf : ¬ (asmUpd instr (t1.pc + BitVec.ofNat 64 (mc.target.config.encode instr).length)
      t1).failed) :
    ∃ l ms2, l ≤ asmLocalCost instr ∧ ∀ k,
      evaluateTargetHOL mc io (k + l) ms1 = evaluateTargetHOL (shiftInterfer l mc) io k ms2 ∧
      findNextInterference mc io (k + l) ms1 =
        findNextInterference (shiftInterfer l mc) io k ms2 ∧
      targetStateRel mc.target
        (asmUpd instr (t1.pc + BitVec.ofNat 64 (mc.target.config.encode instr).length) t1)
        ms2 ∧
      l ≠ 0 := by
  obtain ⟨c1, -, c3, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    c27, -, -, -, -, -, -, -, -, -, -, -, ht1f, -, htpc, -, c43, c44, c45, -⟩ := hrel
  obtain ⟨count, rfl⟩ := (encWithNop_iff _ _ _).mp henc
  have hlen : (mc.target.config.encode instr).length ≤
      (mc.target.config.encode instr ++
        (List.replicate count (mc.target.config.encode (.inst .skip))).flatten).length := by
    simp
  apply NopLocalBudget.local_step mc target t1 ms1 io instr
  refine ⟨hec, c3, ffiEntryPcsDisjoint_shorter mc t1 _ _ ⟨hdis, hlen⟩, c27, ?_, c1⟩
  refine ⟨?_, linkGuard_flip _ _ c43, c44, c45, rfl, hnf, hok⟩
  rw [htpc]
  exact bytesInMem_encWithNop _ _ _ _ _ _ _ henc hmem


theorem fetched_jumpReg_bounded {F : Type}
    (s1 : LabSem.State 64 Config F) (r n1 n2 pc : Nat)
    (mc : MachineConfig 64 riscv_state RiscVProjection) (code2 : LabProgHOL 64)
    (labs : Spt (Spt Nat)) (p : BitVec 64) (t1 : AsmState 64) (ms1 : riscv_state)
    (bytes : List (BitVec 8)) (n : Nat)
    (target : mc.target = riscvTarget)
    (hfetch : asmFetch s1 = some (.asm (.asmi (.jumpReg r)) bytes n))
    (hr : s1.regs r = .loc n1 n2) (hpc : locToPc n1 n2 s1.code = some pc)
    (hec : encoderCorrect mc.target)
    (hrel : stateRel (mc, code2, labs, p) s1 t1 ms1) :
    ∃ count ms2, count ≤ 1 ∧ count ≠ 0 ∧
      (∀ clock, evaluateTargetHOL mc s1.ffi (clock + count) ms1 =
        evaluateTargetHOL (shiftInterfer count mc) s1.ffi clock ms2) ∧
      (∀ clock, findNextInterference mc s1.ffi (clock + count) ms1 =
        findNextInterference (shiftInterfer count mc) s1.ffi clock ms2) ∧
      stateRel (shiftInterfer count mc, code2, labs, p) (LabSem.updPc pc (decClock s1))
        (Flapjack.Compiler.Encoders.AsmSem.updPc (p + BitVec.ofNat 64 (posVal pc 0 code2)) t1) ms2 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    c28, c29, c30, c31, -, -, -, -, -, -, -, ht1f, -, -, -, -, -, c45, -⟩ := id hrel
  have hreg : t1.regs r = p + BitVec.ofNat 64 (posVal pc 0 code2) := by
    have := c30 r
    rw [hr] at this
    simp only [wordLocVal, c28 n1 n2 pc hpc, Option.some.injEq] at this
    exact this.symm
  obtain ⟨bytes', len', hok, hmem, hpos, hdis⟩ :=
    fetchedAsmLine hrel hfetch (by intro op re a h; cases h)
  simp only [lineOk, cbwToAsmHOL] at hok
  have hal := stateRel_aligned_target hrel hec pc
  obtain ⟨l, ms2, bound, hl⟩ := leading_line_bounded s1.ffi target hrel hec _ bytes' hmem hok.1 hok.2.2 hdis
    (by simp [asmUpd, Flapjack.Compiler.Encoders.AsmSem.updPc, Flapjack.Compiler.Encoders.AsmSem.assertState, Flapjack.Compiler.Encoders.AsmSem.readReg, hreg, c45, hal, ht1f])
  have htrel := (hl 0).2.2.1
  simp only [asmUpd, Flapjack.Compiler.Encoders.AsmSem.updPc, Flapjack.Compiler.Encoders.AsmSem.assertState, Flapjack.Compiler.Encoders.AsmSem.readReg, hreg, c45, hal,
    Bool.not_true, Bool.false_or, ht1f] at htrel
  have hrel' := stateRel_shiftInterfer _ _ _ _ _ _ _ l
    (stateRel_frame hrel s1.regs s1.fpRegs s1.memory pc (s1.clock - 1) t1.regs t1.fpRegs
      t1.mem _ htrel c30 c29 (fun x hx => (c31 x hx).2.2) (fun _ _ => rfl) rfl)
  exact ⟨l, ms2, bound, (hl 0).2.2.2, fun clock => (hl clock).1, fun clock => (hl clock).2.1, hrel'⟩

theorem fetched_jump_bounded {F : Type}
    (s1 : LabSem.State 64 Config F) (jt : Lab) (pc : Nat) (w : BitVec 64)
    (mc : MachineConfig 64 riscv_state RiscVProjection) (code2 : LabProgHOL 64)
    (labs : Spt (Spt Nat)) (p : BitVec 64) (t1 : AsmState 64) (ms1 : riscv_state)
    (bytes : List (BitVec 8)) (n : Nat)
    (target : mc.target = riscvTarget)
    (hfetch : asmFetch s1 = some (.labAsm (.jump jt) w bytes n))
    (hpc : getPcValue jt s1 = some pc)
    (hec : encoderCorrect mc.target)
    (hrel : stateRel (mc, code2, labs, p) s1 t1 ms1) :
    ∃ count ms2, count ≤ 2 ∧ count ≠ 0 ∧
      (∀ clock, evaluateTargetHOL mc s1.ffi (clock + count) ms1 =
        evaluateTargetHOL (shiftInterfer count mc) s1.ffi clock ms2) ∧
      (∀ clock, findNextInterference mc s1.ffi (clock + count) ms1 =
        findNextInterference (shiftInterfer count mc) s1.ffi clock ms2) ∧
      stateRel (shiftInterfer count mc, code2, labs, p) (LabSem.updPc pc (decClock s1))
        (Flapjack.Compiler.Encoders.AsmSem.updPc (p + BitVec.ofNat 64 (posVal pc 0 code2)) t1) ms2 := by
  obtain ⟨hfind, -⟩ := findPos_of_getPcValue hrel jt pc hpc
  obtain ⟨w', bytes', len', hok, hmem, hpos, hdis⟩ := fetchedLabAsmLine hrel hfetch
  have hv := lineOk_labelTarget _ _ _ _ _ _ _ _ (Or.inl ⟨jt, rfl⟩) hok
  simp only [getLabel, labInst, hfind] at hv
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, c29, c30, c31, -, -, -, -, -, -, -, ht1f, -, htpc, -⟩ := id hrel
  obtain ⟨l, ms2, bound, hl⟩ := leading_line_bounded s1.ffi target hrel hec _ bytes' hmem hv.1 hv.2.2 hdis
    (by simp [asmUpd, jumpToOffset, Flapjack.Compiler.Encoders.AsmSem.updPc, ht1f])
  have htrel := (hl 0).2.2.1
  have hnewpc : t1.pc + (BitVec.ofNat 64 (posVal pc 0 code2) -
      BitVec.ofNat 64 (posVal s1.pc 0 code2)) = p + BitVec.ofNat 64 (posVal pc 0 code2) := by
    rw [htpc]; ring
  simp only [asmUpd, jumpToOffset, Flapjack.Compiler.Encoders.AsmSem.updPc, hnewpc] at htrel
  have hrel' := stateRel_shiftInterfer _ _ _ _ _ _ _ l
    (stateRel_frame hrel s1.regs s1.fpRegs s1.memory pc (s1.clock - 1) t1.regs t1.fpRegs
      t1.mem _ htrel c30 c29 (fun x hx => (c31 x hx).2.2) (fun _ _ => rfl) rfl)
  exact ⟨l, ms2, bound, (hl 0).2.2.2, fun clock => (hl clock).1, fun clock => (hl clock).2.1, hrel'⟩

theorem fetched_locValue_bounded {F : Type}
    (s1 : LabSem.State 64 Config F) (reg : Nat) (lab : Lab) (pc : Nat) (w : BitVec 64)
    (mc : MachineConfig 64 riscv_state RiscVProjection) (code2 : LabProgHOL 64)
    (labs : Spt (Spt Nat)) (p : BitVec 64) (t1 : AsmState 64) (ms1 : riscv_state)
    (bytes : List (BitVec 8)) (n : Nat)
    (target : mc.target = riscvTarget)
    (hfetch : asmFetch s1 = some (.labAsm (.locValue reg lab) w bytes n))
    (hpc : getPcValue lab s1 = some pc)
    (hec : encoderCorrect mc.target)
    (hrel : stateRel (mc, code2, labs, p) s1 t1 ms1) :
    ∃ (encoded : List (BitVec 8)), ∃ count ms2 asm2,
      posVal (s1.pc + 1) 0 code2 = posVal s1.pc 0 code2 + encoded.length ∧
      count ≤ 2 + encoded.length / 4 ∧ count ≠ 0 ∧
      (∀ clock, evaluateTargetHOL mc s1.ffi (clock + count) ms1 =
        evaluateTargetHOL (shiftInterfer count mc) s1.ffi clock ms2) ∧
      (∀ clock, findNextInterference mc s1.ffi (clock + count) ms1 =
        findNextInterference (shiftInterfer count mc) s1.ffi clock ms2) ∧
      stateRel (shiftInterfer count mc, code2, labs, p)
        (incPc (decClock (LabSem.updReg reg (labToLoc lab) s1))) asm2 ms2 := by
  rcases lab with ⟨l1, l2⟩
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    c28, c29, c30, c31, -, -, -, -, -, -, -, ht1f, -, htpc, -⟩ := id hrel
  have hlook := c28 l1 l2 pc hpc
  have hfind := labLookup_implies_findPos l1 l2 labs _ hlook
  obtain ⟨w', bytes', len', hok, hmem, hpos, hdis⟩ := fetchedLabAsmLine hrel hfetch
  have hv := lineOk_labelTarget _ _ _ _ _ _ _ _ (Or.inr (Or.inr ⟨reg, .lab l1 l2, rfl⟩)) hok
  simp only [getLabel, labInst, hfind] at hv
  obtain ⟨l, ms2, bound, hl⟩ := line_bounded s1.ffi target hrel hec _ bytes' hmem hv.1 hv.2.2 hdis
    (by simp [asmUpd, Flapjack.Compiler.Encoders.AsmSem.updPc, Flapjack.Compiler.Encoders.AsmSem.updReg, ht1f])
    (fun _ _ => by simp [asmUpd, Flapjack.Compiler.Encoders.AsmSem.updPc, Flapjack.Compiler.Encoders.AsmSem.updReg]) (by intro x h; cases h)
  have htrel := (hl 0).2.2.1
  have hnewpc : t1.pc + BitVec.ofNat 64 bytes'.length =
      p + BitVec.ofNat 64 (posVal (s1.pc + 1) 0 code2) := by
    rw [htpc, hpos, BitVec.ofNat_add, BitVec.add_assoc]
  have hval : t1.pc + (BitVec.ofNat 64 (posVal pc 0 code2) -
      BitVec.ofNat 64 (posVal s1.pc 0 code2)) = p + BitVec.ofNat 64 (posVal pc 0 code2) := by
    rw [htpc]; ring
  simp only [asmUpd, Flapjack.Compiler.Encoders.AsmSem.updPc, Flapjack.Compiler.Encoders.AsmSem.updReg, hnewpc, hval] at htrel
  have hregs : ∀ r, wordLocVal p labs
      ((fun key => if key = reg then labToLoc (.lab l1 l2) else s1.regs key) r) =
      some ((fun r' => if r' = reg then p + BitVec.ofNat 64 (posVal pc 0 code2)
        else t1.regs r') r) := by
    intro r
    by_cases hr : r = reg
    · simp [hr, labToLoc, wordLocVal, hlook]
    · simp only [hr, ↓reduceIte]; exact c30 r
  have hrel' := stateRel_shiftInterfer _ _ _ _ _ _ _ l
    (stateRel_frame hrel _ s1.fpRegs s1.memory (s1.pc + 1) (s1.clock - 1) _ t1.fpRegs
      t1.mem _ htrel hregs c29 (fun x hx => (c31 x hx).2.2) (fun _ _ => rfl) rfl)
  exact ⟨bytes', l, ms2, _, hpos, (by simp only [asmLocalCost] at bound; omega), (hl 0).2.2.2, fun clock => (hl clock).1, fun clock => (hl clock).2.1, hrel'⟩

theorem fetched_branch_fallthrough_bounded {F : Type}
    (s1 : LabSem.State 64 Config F) (cmp : HolCmp) (rr : Nat) (ri : HolRegImm 64)
    (jt : Lab) (w : BitVec 64)
    (mc : MachineConfig 64 riscv_state RiscVProjection) (code2 : LabProgHOL 64)
    (labs : Spt (Spt Nat)) (p : BitVec 64) (t1 : AsmState 64) (ms1 : riscv_state)
    (bytes : List (BitVec 8)) (n : Nat)
    (target : mc.target = riscvTarget)
    (hfetch : asmFetch s1 = some (.labAsm (.jumpCmp cmp rr ri jt) w bytes n))
    (hec : encoderCorrect mc.target)
    (hrel : stateRel (mc, code2, labs, p) s1 t1 ms1)
    (hc : wordSemWordCmp cmp (s1.regs rr) (LabSem.regImm ri s1) = some false) :
    ∃ (encoded : List (BitVec 8)), ∃ count ms2,
      posVal (s1.pc + 1) 0 code2 = posVal s1.pc 0 code2 + encoded.length ∧
      count ≤ 3 + encoded.length / 4 ∧ count ≠ 0 ∧
      (∀ clock, evaluateTargetHOL mc s1.ffi (clock + count) ms1 =
        evaluateTargetHOL (shiftInterfer count mc) s1.ffi clock ms2) ∧
      (∀ clock, findNextInterference mc s1.ffi (clock + count) ms1 =
        findNextInterference (shiftInterfer count mc) s1.ffi clock ms2) ∧
      stateRel (shiftInterfer count mc, code2, labs, p) (incPc (decClock s1))
        (Flapjack.Compiler.Encoders.AsmSem.updPc
          (p + BitVec.ofNat 64 (posVal (s1.pc + 1) 0 code2)) t1) ms2 := by
  obtain ⟨w', bytes', len', hok, hmem, hpos, hdis⟩ := fetchedLabAsmLine hrel hfetch
  have hv := lineOk_labelTarget _ _ _ _ _ _ _ _ (Or.inr (Or.inl ⟨cmp, rr, ri, jt, rfl⟩)) hok
  simp only [getLabel, labInst] at hv
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, c29, c30, c31, -, -, -, -, -, -, -, ht1f, -, htpc, -⟩ := id hrel
  have htc := wordCmp_lemma mc code2 labs p s1 t1 ms1 cmp rr ri false ⟨hrel, hc⟩
  obtain ⟨l, ms2, bound, hl⟩ := line_bounded s1.ffi target hrel hec _ bytes' hmem hv.1 hv.2.2 hdis
    (by simp [asmUpd, ← htc, Flapjack.Compiler.Encoders.AsmSem.updPc, ht1f]) (fun _ _ => by simp [asmUpd, ← htc, Flapjack.Compiler.Encoders.AsmSem.updPc])
    (by intro x h; cases h)
  have htrel := (hl 0).2.2.1
  have hnewpc : t1.pc + BitVec.ofNat 64 bytes'.length =
      p + BitVec.ofNat 64 (posVal (s1.pc + 1) 0 code2) := by
    rw [htpc, hpos, BitVec.ofNat_add, BitVec.add_assoc]
  simp only [asmUpd, ← htc, Bool.false_eq_true, ↓reduceIte, Flapjack.Compiler.Encoders.AsmSem.updPc, hnewpc] at htrel
  have hrel' := stateRel_shiftInterfer _ _ _ _ _ _ _ l
    (stateRel_frame hrel s1.regs s1.fpRegs s1.memory (s1.pc + 1) (s1.clock - 1) t1.regs
      t1.fpRegs t1.mem _ htrel c30 c29 (fun x hx => (c31 x hx).2.2) (fun _ _ => rfl) rfl)
  exact ⟨bytes', l, ms2, hpos, (by simp only [asmLocalCost] at bound; omega), (hl 0).2.2.2, fun clock => (hl clock).1, fun clock => (hl clock).2.1, hrel'⟩

theorem fetched_branch_taken_bounded {F : Type}
    (s1 : LabSem.State 64 Config F) (cmp : HolCmp) (rr : Nat) (ri : HolRegImm 64)
    (jt : Lab) (w : BitVec 64)
    (mc : MachineConfig 64 riscv_state RiscVProjection) (code2 : LabProgHOL 64)
    (labs : Spt (Spt Nat)) (p : BitVec 64) (t1 : AsmState 64) (ms1 : riscv_state)
    (bytes : List (BitVec 8)) (n : Nat)
    (target : mc.target = riscvTarget)
    (hfetch : asmFetch s1 = some (.labAsm (.jumpCmp cmp rr ri jt) w bytes n))
    (hec : encoderCorrect mc.target)
    (hrel : stateRel (mc, code2, labs, p) s1 t1 ms1)
    (hc : wordSemWordCmp cmp (s1.regs rr) (LabSem.regImm ri s1) = some true)
    (pc : Nat) (hpc : getPcValue jt s1 = some pc) :
    ∃ count ms2, count ≤ 3 ∧ count ≠ 0 ∧
      (∀ clock, evaluateTargetHOL mc s1.ffi (clock + count) ms1 =
        evaluateTargetHOL (shiftInterfer count mc) s1.ffi clock ms2) ∧
      (∀ clock, findNextInterference mc s1.ffi (clock + count) ms1 =
        findNextInterference (shiftInterfer count mc) s1.ffi clock ms2) ∧
      stateRel (shiftInterfer count mc, code2, labs, p) (LabSem.updPc pc (decClock s1))
        (Flapjack.Compiler.Encoders.AsmSem.updPc (p + BitVec.ofNat 64 (posVal pc 0 code2)) t1) ms2 := by
  obtain ⟨w', bytes', len', hok, hmem, hpos, hdis⟩ := fetchedLabAsmLine hrel hfetch
  have hv := lineOk_labelTarget _ _ _ _ _ _ _ _ (Or.inr (Or.inl ⟨cmp, rr, ri, jt, rfl⟩)) hok
  simp only [getLabel, labInst] at hv
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, c29, c30, c31, -, -, -, -, -, -, -, ht1f, -, htpc, -⟩ := id hrel
  have htc := wordCmp_lemma mc code2 labs p s1 t1 ms1 cmp rr ri true ⟨hrel, hc⟩
  obtain ⟨hfind, -⟩ := findPos_of_getPcValue hrel jt pc hpc
  simp only [hfind] at hv
  obtain ⟨l, ms2, bound, hl⟩ := leading_line_bounded s1.ffi target hrel hec _ bytes' hmem hv.1 hv.2.2 hdis
    (by simp [asmUpd, ← htc, jumpToOffset, Flapjack.Compiler.Encoders.AsmSem.updPc, ht1f])
  have htrel := (hl 0).2.2.1
  have hnewpc : t1.pc + (BitVec.ofNat 64 (posVal pc 0 code2) -
      BitVec.ofNat 64 (posVal s1.pc 0 code2)) =
      p + BitVec.ofNat 64 (posVal pc 0 code2) := by
    rw [htpc]; ring
  simp only [asmUpd, ← htc, ↓reduceIte, jumpToOffset, Flapjack.Compiler.Encoders.AsmSem.updPc, hnewpc] at htrel
  have hrel' := stateRel_shiftInterfer _ _ _ _ _ _ _ l
    (stateRel_frame hrel s1.regs s1.fpRegs s1.memory pc (s1.clock - 1) t1.regs t1.fpRegs
      t1.mem _ htrel c30 c29 (fun x hx => (c31 x hx).2.2) (fun _ _ => rfl) rfl)
  exact ⟨l, ms2, bound, (hl 0).2.2.2, fun clock => (hl clock).1, fun clock => (hl clock).2.1, hrel'⟩


end InitECandidate.Runtime.LabToTarget.LocalCost
#print axioms InitECandidate.Runtime.LabToTarget.LocalCost.fetched_jumpReg_bounded
#print axioms InitECandidate.Runtime.LabToTarget.LocalCost.fetched_jump_bounded
#print axioms InitECandidate.Runtime.LabToTarget.LocalCost.fetched_locValue_bounded
#print axioms InitECandidate.Runtime.LabToTarget.LocalCost.fetched_branch_fallthrough_bounded
#print axioms InitECandidate.Runtime.LabToTarget.LocalCost.fetched_branch_taken_bounded
