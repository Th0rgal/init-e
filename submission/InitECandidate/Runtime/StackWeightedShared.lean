import InitECandidate.Runtime.StackWeightedTerminal
import Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenCorrect.ShMem
namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.StackToLab.Proofs.CodeInstalled
open Flapjack.Compiler.Backend.StackToLab.Proofs.StateRel
open Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenHelpers
open Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenCorrect
open Flapjack.Compiler.Backend.StackToLab.Proofs

/-- Exact one-operation simulation, retaining returned state effects and the
clock-zero case. It asserts no runtime bound or execution trace. -/
inductive SharedStep {F : Type} (start : LabSem.State 64 LabToTarget.Config F)
    (op : HolMemop) (reg base : Nat) (offset : BitVec 64) :
    Option (StackSemResult 64) → StackSemStateFiniteExact 64 LabToTarget.Config F → Prop
  | returned (post) (ffi : HolFfiState F) (bytes : List (BitVec 8))
      (next : LabSem.State 64 LabToTarget.Config F) (clock : start.clock ≠ 0)
      (operation : shareMemOp op reg (.addr base offset) start = some (.ret ffi bytes, next))
      (related : stateRel post {next with ioRegs := holShiftSeq 1 next.ioRegs, ioFpRegs := holShiftSeq 1 next.ioFpRegs})
      (pc : next.pc = start.pc + 1) (code : next.code = start.code) :
      SharedStep start op reg base offset none post
  | terminal (post) (event : HolFinalEvent) (clock : start.clock ≠ 0)
      (operation : shareMemOp op reg (.addr base offset) start = some (.final event, start))
      (ffi : post.ffi = start.ffi) : SharedStep start op reg base offset (some (.finalFFI event)) post
  | timeout (post) (clock : start.clock = 0) : SharedStep start op reg base offset (some .timeOut) post

variable {F : Type}

theorem sharedLoadStep {s1 : StackSemStateFiniteExact 64 LabToTarget.Config F}
    {t1 : Flapjack.Compiler.Backend.LabSem.State 64 LabToTarget.Config F} {op : HolMemop} {reg a : Nat}
    {w addr : BitVec 64} {k : Nat} {r : Option (StackSemResult 64)}
    {s2 : StackSemStateFiniteExact 64 LabToTarget.Config F}
    (rel : stateRel s1 t1)
    (cnz : t1.clock ≠ 0) (haddr : addrValue (.addr a w) t1 = some addr)
    (hop : ∀ c, shareMemOp op reg (.addr a w) { t1 with clock := c } =
      shareMemLoad reg (.addr a w) { t1 with clock := c } k)
    (hdom : (if k = 0 then addr.toNat % (64 / 8) == 0 && t1.sharedMemDomain addr
      else t1.sharedMemDomain (riscvByteAlignHOL addr)) = true)
    (ev : (match callFFIHOL (StackSemStateOps.decClock s1).ffi (.sharedMem .mappedRead)
        [BitVec.ofNat 8 k] (panWordToBytesHOL addr false) with
      | .final outcome => (some (.finalFFI outcome), StackSemStateOps.decClock s1)
      | .ret newFfi newBytes => (none, { StackSemStateOps.decClock s1 with
          regs := (StackSemStateOps.decClock s1).regs.updateEq
            (reg, .word (panWordOfBytesHOL false 0 newBytes))
          ffi := newFfi })) = (r, s2)) :
    SharedStep t1 op reg a w r s2 := by
  have ffiEq := relFfi rel
  have lab : ∀ c, shareMemLoad reg (.addr a w) { t1 with clock := c } k =
      match callFFIHOL t1.ffi (.sharedMem .mappedRead) [BitVec.ofNat 8 k]
          (sharedMemoryWordBytes addr) with
      | .final outcome => some (.final outcome, { t1 with clock := c })
      | .ret f bytes => some (.ret f bytes, { t1 with
          clock := c - 1
          ffi := f
          regs := fun r => if r = reg then .word (wordOfBytesHOL8 false 0 bytes) else t1.regs r
          pc := t1.pc + 1 }) := by
    intro c
    simp only [shareMemLoad]
    rw [show addrValue (.addr a w) { t1 with clock := c } = some addr from haddr]
    simp only [hdom, if_true]
    cases callFFIHOL t1.ffi (.sharedMem .mappedRead) [BitVec.ofNat 8 k]
      (sharedMemoryWordBytes addr) <;> rfl
  rw [panWordToBytes_eq_shared,
    show (StackSemStateOps.decClock s1).ffi = t1.ffi from ffiEq.symm] at ev
  split at ev
  · rename_i outcome hffi
    simp only [Prod.mk.injEq] at ev
    obtain ⟨rfl, rfl⟩ := ev
    refine SharedStep.terminal _ outcome cnz ?_ ?_
    · have operation := hop t1.clock
      rw [lab, hffi] at operation
      exact operation
    · exact ffiEq.symm
  · rename_i ffi' bytes hffi
    simp only [Prod.mk.injEq] at ev
    obtain ⟨rfl, rfl⟩ := ev
    let next : LabSem.State 64 LabToTarget.Config F := {t1 with
      clock := t1.clock - 1, ffi := ffi',
      regs := fun r => if r = reg then .word (wordOfBytesHOL8 false 0 bytes) else t1.regs r,
      pc := t1.pc + 1}
    refine SharedStep.returned _ ffi' bytes next cnz ?_ ?_ rfl rfl
    · have operation := hop t1.clock
      rw [lab, hffi] at operation
      exact operation
    · have h := stateRelShMemRet rel ffi' (t1.pc + 1)
        (some (reg, .word (wordOfBytesHOL8 false 0 bytes)))
      simpa [next, panWordOfBytes_eq_wordOfBytesHOL8, StackSemStateOps.decClock] using h

variable {F : Type}

theorem sharedStoreStep {s1 : StackSemStateFiniteExact 64 LabToTarget.Config F}
    {t1 : Flapjack.Compiler.Backend.LabSem.State 64 LabToTarget.Config F} {op : HolMemop} {reg a : Nat}
    {w addr v : BitVec 64} {k : Nat} {r : Option (StackSemResult 64)}
    {s2 : StackSemStateFiniteExact 64 LabToTarget.Config F}
    {payload : List (BitVec 8)}
    (rel : stateRel s1 t1)
    (cnz : t1.clock ≠ 0) (haddr : addrValue (.addr a w) t1 = some addr)
    (hv : t1.regs reg = .word v)
    (hop : ∀ c, shareMemOp op reg (.addr a w) { t1 with clock := c } =
      shareMemStore reg (.addr a w) { t1 with clock := c } k)
    (hdom : (if k = 0 then addr.toNat % (64 / 8) == 0 && t1.sharedMemDomain addr
      else t1.sharedMemDomain (riscvByteAlignHOL addr)) = true)
    (hpay : payload = (if k = 0 then sharedMemoryWordBytes v
      else (sharedMemoryWordBytes v).take k) ++ sharedMemoryWordBytes addr)
    (ev : (match callFFIHOL (StackSemStateOps.decClock s1).ffi (.sharedMem .mappedWrite)
        [BitVec.ofNat 8 k] payload with
      | .final outcome => (some (.finalFFI outcome), StackSemStateOps.decClock s1)
      | .ret newFfi _ => (none, { StackSemStateOps.decClock s1 with ffi := newFfi })) =
        (r, s2)) :
    SharedStep t1 op reg a w r s2 := by
  have ffiEq := relFfi rel
  have lab : ∀ c, shareMemStore reg (.addr a w) { t1 with clock := c } k =
      match callFFIHOL t1.ffi (.sharedMem .mappedWrite) [BitVec.ofNat 8 k] payload with
      | .final outcome => some (.final outcome, { t1 with clock := c })
      | .ret f bytes => some (.ret f bytes, { t1 with
          clock := c - 1
          ffi := f
          pc := t1.pc + 1 }) := by
    intro c
    simp only [shareMemStore]
    rw [show ({ t1 with clock := c } : Flapjack.Compiler.Backend.LabSem.State 64 LabToTarget.Config F).regs reg
      = .word v from hv]
    simp only
    rw [show addrValue (.addr a w) { t1 with clock := c } = some addr from haddr]
    simp only [hdom, if_true, ← hpay]
    cases callFFIHOL t1.ffi (.sharedMem .mappedWrite) [BitVec.ofNat 8 k] payload <;> rfl
  rw [show (StackSemStateOps.decClock s1).ffi = t1.ffi from ffiEq.symm] at ev
  split at ev
  · rename_i outcome hffi
    simp only [Prod.mk.injEq] at ev
    obtain ⟨rfl, rfl⟩ := ev
    refine SharedStep.terminal _ outcome cnz ?_ ?_
    · have operation := hop t1.clock
      rw [lab, hffi] at operation
      exact operation
    · exact ffiEq.symm
  · rename_i ffi' bytes hffi
    simp only [Prod.mk.injEq] at ev
    obtain ⟨rfl, rfl⟩ := ev
    let next : LabSem.State 64 LabToTarget.Config F :=
      {t1 with clock := t1.clock - 1, ffi := ffi', pc := t1.pc + 1}
    refine SharedStep.returned _ ffi' bytes next cnz ?_ ?_ rfl rfl
    · have operation := hop t1.clock
      rw [lab, hffi] at operation
      exact operation
    · have h := stateRelShMemRet rel ffi' (t1.pc + 1) none
      simpa [next, StackSemStateOps.decClock] using h

/-- All eight shared-memory operators are matched to their actual LabSem
operation using the original source/target relation and domain alignment. -/
theorem sharedStep_of_source {F : Type}
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (start : LabSem.State 64 LabToTarget.Config F) (op : HolMemop) (reg a : Nat) (w : BitVec 64)
    (r : Option (StackSemResult 64)) (post : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (run : StackSemEvaluate.evaluate (.shMemOp op reg (.addr a w), source) = (r, post))
    (nerr : r ≠ some .error) (rel : stateRel source start) :
    SharedStep start op reg a w r post := by
  rw [StackSemEvaluate.evaluate_shMemOp] at run
  have clk := relClock rel
  have ffiEq := relFfi rel
  split at run
  · rename_i addr hexp
    have haddr : addrValue (.addr a w) start = some addr := InstCorrect.addrOfWordExp rel hexp
    split_ifs at run with h0
    · simp only [Prod.mk.injEq] at run
      obtain ⟨rfl, rfl⟩ := run
      exact SharedStep.timeout _ (by omega)
    · have cnz : start.clock ≠ 0 := by omega
      have good : goodDimindex 64 := by
        obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
          _, g⟩ := rel
        exact g
      have pos : 0 < 64 / 8 := by decide
      have err : ∀ {x : StackSemStateFiniteExact 64 LabToTarget.Config F},
          (some StackSemResult.error, x) = (r, post) → False := fun e => by
        simp only [Prod.mk.injEq] at e; exact nerr e.1.symm
      cases op
      case load =>
        simp only [StackSemShMem.shMemOp, StackSemShMem.shMemLoad] at run
        split_ifs at run with dom
        · exact sharedLoadStep (k := 0) rel cnz haddr (fun c => rfl)
            (by simp only [StackSemStateOps.decClock] at dom; simp [relShMdomain rel, dom, relShAligned rel dom]) run
        · exact (err run).elim
      case load8 =>
        simp only [StackSemShMem.shMemOp, StackSemShMem.shMemLoadByte] at run
        split_ifs at run with dom
        · exact sharedLoadStep (k := 1) rel cnz haddr (fun c => rfl)
            (by simp only [StackSemStateOps.decClock] at dom; simp [relShMdomain rel, dom]) run
        · exact (err run).elim
      case load16 =>
        simp only [StackSemShMem.shMemOp, StackSemShMem.shMemLoad16] at run
        split_ifs at run with dom
        · exact sharedLoadStep (k := 2) rel cnz haddr (fun c => rfl)
            (by simp only [StackSemStateOps.decClock] at dom; simp [relShMdomain rel, dom]) run
        · exact (err run).elim
      case load32 =>
        simp only [StackSemShMem.shMemOp, StackSemShMem.shMemLoad32] at run
        split_ifs at run with dom
        · exact sharedLoadStep (k := 4) rel cnz haddr (fun c => rfl)
            (by simp only [StackSemStateOps.decClock] at dom; simp [relShMdomain rel, dom]) run
        · exact (err run).elim
      case store =>
        simp only [StackSemShMem.shMemOp, StackSemShMem.shMemStore] at run
        split at run
        · rename_i v hv
          split_ifs at run with dom
          · exact sharedStoreStep (k := 0) rel cnz haddr (InstCorrect.regOfLookup rel hv)
              (fun c => rfl) (by simp only [StackSemStateOps.decClock] at dom; simp [relShMdomain rel, dom, relShAligned rel dom])
              (by simp [panWordToBytes_eq_shared]) run
          · exact (err run).elim
        · exact (err run).elim
      case store8 =>
        simp only [StackSemShMem.shMemOp, StackSemShMem.shMemStoreByte] at run
        split at run
        · rename_i v hv
          split_ifs at run with dom
          · exact sharedStoreStep (k := 1) rel cnz haddr (InstCorrect.regOfLookup rel hv)
              (fun c => rfl) (by simp only [StackSemStateOps.decClock] at dom; simp [relShMdomain rel, dom])
              (by simp [panWordToBytes_eq_shared, sharedBytesTakeOne v pos]) run
          · exact (err run).elim
        · exact (err run).elim
      case store16 =>
        simp only [StackSemShMem.shMemOp, StackSemShMem.shMemStore16] at run
        split at run
        · rename_i v hv
          split_ifs at run with dom
          · exact sharedStoreStep (k := 2) rel cnz haddr (InstCorrect.regOfLookup rel hv)
              (fun c => rfl) (by simp only [StackSemStateOps.decClock] at dom; simp [relShMdomain rel, dom])
              (by simp [panWordToBytes_eq_shared]) run
          · exact (err run).elim
        · exact (err run).elim
      case store32 =>
        simp only [StackSemShMem.shMemOp, StackSemShMem.shMemStore32] at run
        split at run
        · rename_i v hv
          split_ifs at run with dom
          · exact sharedStoreStep (k := 4) rel cnz haddr (InstCorrect.regOfLookup rel hv)
              (fun c => rfl) (by simp only [StackSemStateOps.decClock] at dom; simp [relShMdomain rel, dom])
              (by simp [panWordToBytes_eq_shared]) run
          · exact (err run).elim
        · exact (err run).elim
  · simp only [Prod.mk.injEq] at run
    exact absurd run.1.symm nerr

/-- A returning shared-memory operation is one actual host dispatch. Its
native cost is one, including input/output operations and all access widths. -/
theorem normalWeightedFlatten_shared {F : Type}
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (op : HolMemop) (reg base : Nat) (offset : BitVec 64) :
    NormalWeightedFlatten (.shMemOp op reg (.addr base offset)) source (fun _ _ => 1) := by
  intro flag post sectionId labelId continues breaks start encoded hyps
  rcases hyps with ⟨evaluated, nonerror, related, args, installed, labels⟩
  have step := sharedStep_of_source source start op reg base offset none post evaluated nonerror related
  cases step with
  | returned =>
    rename_i ffi bytes next clock operation pc code finalRelated
    have fetch : asmFetchAux start.pc start.code = some (.asm (.shareMem op reg (.addr base offset)) [] 0) :=
      fetchSingle rfl (by simpa [Flapjack.Compiler.Backend.StackToLab.flattenHOL, appListAppendList] using installed)
    let final := {next with ioRegs := holShiftSeq 1 next.ioRegs, ioFpRegs := holShiftSeq 1 next.ioFpRegs}
    have trace := LabToTarget.WeightedMixedTrace.shared (code := encoded) start final op reg base offset [] 0
      ffi bytes next 0 clock fetch operation (.nil final)
    refine ⟨final, 0, 1, finalRelated, ?_, code, Nat.le_refl _, ?_⟩
    · simp [final, pc, Flapjack.Compiler.Backend.StackToLab.flattenHOL, appListAppendList, isLabelHOL]
    · simpa only [Nat.add_zero, Nat.zero_add] using trace

/-- A final shared-memory response needs no preceding native instructions;
the terminal extraction accounts for the actual final dispatch once. -/
theorem terminalWeightedFlatten_shared {F : Type}
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (op : HolMemop) (reg base : Nat) (offset : BitVec 64) (event : HolFinalEvent) :
    TerminalWeightedFlatten (.shMemOp op reg (.addr base offset)) source (.finalFFI event)
      (.ffiOutcome event) (fun _ _ => 0) := by
  intro flag post sectionId labelId continues breaks start encoded hyps
  rcases hyps with ⟨evaluated, nonerror, related, args, installed, labels⟩
  have step := sharedStep_of_source source start op reg base offset (some (.finalFFI event)) post
    evaluated nonerror related
  cases step with
  | terminal =>
    rename_i clock operation ffi
    have fetch : asmFetchAux start.pc start.code = some (.asm (.shareMem op reg (.addr base offset)) [] 0) :=
      fetchSingle rfl (by simpa [Flapjack.Compiler.Backend.StackToLab.flattenHOL, appListAppendList] using installed)
    refine ⟨start, 0, 0, ffi.symm, rfl, Nat.le_refl _, ?_, ?_⟩
    · simpa only [Nat.add_zero] using LabToTarget.WeightedMixedTrace.nil (code := encoded) start
    · exact LabToTarget.Terminal.shared start op reg base offset [] 0 event clock fetch operation

#print axioms normalWeightedFlatten_shared
#print axioms terminalWeightedFlatten_shared
#print axioms sharedStep_of_source
end InitECandidate.Runtime.StackToLab
