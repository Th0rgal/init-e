import InitECandidate.Runtime.LabLineBudget
import Flapjack.Compiler.Backend.LabToTarget.CompileCorrect.CallFfi

namespace InitECandidate.Runtime.LabToTarget
open Flapjack Flapjack.RiscV.L3
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.AsmSem
open Flapjack.Compiler.Encoders.AsmProps Flapjack.Compiler.Backend.Semantics.TargetProps
open Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.LabToTarget Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Basis.Pure.MlString

/-- A fetched FFI line reaches its real entry point in bounded time. The
next evaluator step dispatches exactly the source's two bytearrays. -/
theorem fetched_ffi_entry_bounded {F : Type}
    (s1 : LabSem.State 64 Config F) (name : MlString) (w : BitVec 64)
    (mc : MachineConfig 64 riscv_state RiscVProjection) (code2 : LabProgHOL 64)
    (labs : Spt (Spt Nat)) (p : BitVec 64) (t1 : AsmState 64) (ms1 : riscv_state)
    (bytes : List (BitVec 8)) (n : Nat)
    (len start len2 start2 : BitVec 64) (conf bytes2 : List (BitVec 8))
    (target : mc.target = riscvTarget)
    (hfetch : asmFetch s1 = some (.labAsm (.callFFI name) w bytes n))
    (hlen : s1.regs s1.lenReg = .word len) (hptr : s1.regs s1.ptrReg = .word start)
    (hlen2 : s1.regs s1.len2Reg = .word len2) (hptr2 : s1.regs s1.ptr2Reg = .word start2)
    (hrd1 : readBytearrayWordHOL start len.toNat
      (memLoadByteAuxExact s1.memory s1.memDomain s1.be) = some conf)
    (hrd2 : readBytearrayWordHOL start2 len2.toNat
      (memLoadByteAuxExact s1.memory s1.memDomain s1.be) = some bytes2)
    (hec : encoderCorrect mc.target)
    (hrel : stateRel (mc, code2, labs, p) s1 t1 ms1) :
    ∃ count ms2, count ≤ 16 ∧ count ≠ 0 ∧
      (∀ clock, evaluateTargetHOL mc s1.ffi (clock + count) ms1 =
        evaluateTargetHOL (shiftInterfer count mc) s1.ffi clock ms2) ∧
      (∀ clock, evaluateTargetHOL (shiftInterfer count mc) s1.ffi (clock + 1) ms2 =
        match callFFIHOL s1.ffi (.extCall name) conf bytes2 with
        | .final e => (.halt (.ffiOutcome e), ms2, s1.ffi)
        | .ret newFfi newBytes =>
          evaluateTargetHOL { shiftInterfer count mc with ffiInterfer := holShiftSeq 1 mc.ffiInterfer }
            newFfi clock (mc.ffiInterfer 0 (getFfiIndex mc.ffiNames (.extCall name), newBytes, ms2))) := by
  obtain ⟨c1, c2, c3, -, -, c6, c7, c8, c9, c10, c11, c12, c13, -, c15, c16, -, -, -, -, -, c22,
    -, c24, -, -, -, c28, -, c30, c31, -, -, -, -, -, -, -, ht1f, c40, htpc, -, -, c44, -, -, -,
    -, -, c50, -, c52, -⟩ := id hrel
  -- the target line is a jump to the FFI entry of `name`
  obtain ⟨w', bytes', len', hok, hmem, hpos, hdis⟩ := fetchedLabAsmLine hrel hfetch
  simp only [lineOk] at hok
  obtain ⟨l, ms2, bound, hl⟩ := leading_line_bounded s1.ffi target hrel hec _ bytes' hmem hok.1 hok.2.2 hdis
    (by simp [asmUpd, jumpToOffset, Flapjack.Compiler.Encoders.AsmSem.updPc, ht1f])
  have hts := (hl 0).2.2.1
  obtain ⟨-, hgpc, hgmem, hgreg, -⟩ := hts
  -- the FFI name is an external call below the MMIO boundary
  obtain ⟨i, hi, hiinfo⟩ := c15
  obtain ⟨y, hy⟩ := hasIoName_findIndex s1.code name (imp_hasIoName s1 name w bytes n hfetch)
  have hmemNames : HolFfiName.extCall name ∈ mc.ffiNames := by
    have hm1 := Misc.findIndex_isMem _ _ _ _ hy
    simp only [Misc.listSubset, List.all_eq_true, decide_eq_true_eq] at c22
    exact c22 _ (List.mem_filter.mpr ⟨hm1, rfl⟩)
  have : Nonempty HolFfiName := ⟨.extCall name⟩
  have hidx : getFfiIndex mc.ffiNames (.extCall name) < i :=
    ffiName_not_mapped _ i _ ⟨hi, ⟨name, rfl⟩, hmemNames⟩
  have hidxt : getFfiIndex (mc.ffiNames.take (holThe (mmioPcsMinIndex mc.ffiNames)))
      (.extCall name) = getFfiIndex mc.ffiNames (.extCall name) := by
    rw [hi]; exact getFfiIndex_take _ _ _ hmemNames hidx
  obtain ⟨-, hnp, hnh, hnc, hfi⟩ := c24 _ i ⟨hmemNames, hi, hidx⟩
  have he := el_getFfiIndex_mem _ _ hmemNames
  have hlk : mc.mmioInfo.lookup (getFfiIndex mc.ffiNames (.extCall name)) = none := by
    have := hiinfo (getFfiIndex mc.ffiNames (.extCall name))
    rwa [if_neg (by omega)] at this
  have hm := (sptAListLookup_eq_lookup _ mc.mmioInfo).trans hlk
  -- the target PC after the jump is that FFI entry
  have hjpc : t1.pc + (0 - BitVec.ofNat 64 (posVal s1.pc 0 code2 +
      (3 + getFfiIndex (mc.ffiNames.take (holThe (mmioPcsMinIndex mc.ffiNames)))
        (.extCall name)) * ffiOffset)) =
      p - BitVec.ofNat 64 ((3 + getFfiIndex mc.ffiNames (.extCall name)) * ffiOffset) := by
    rw [htpc, hidxt, BitVec.ofNat_add]; ring
  have hpc2 : mc.target.getPc ms2 =
      p - BitVec.ofNat 64 ((3 + getFfiIndex mc.ffiNames (.extCall name)) * ffiOffset) := by
    rw [hgpc]; simp only [asmUpd, jumpToOffset, Flapjack.Compiler.Encoders.AsmSem.updPc]; exact hjpc
  rw [← hpc2] at hnp hnh hnc hfi
  have hn : ¬ (mc.progAddresses (mc.target.getPc ms2) ∧
      mc.target.getPc ms2 ∉ mc.ffiEntryPcs) := fun h => hnp h.1
  -- the target reads the same two bytearrays
  have hreg : ∀ r, asmRegOkExact r mc.target.config = true →
      mc.target.getReg ms2 r = t1.regs r := by
    intro r hr
    simp only [asmRegOkExact, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hr
    exact hgreg r hr
  classical
  have hfun : (fun a => if mc.progAddresses a then some (mc.target.getByte ms2 a) else none) =
      (fun a => if mc.progAddresses a then some (t1.mem a) else none) := by
    funext a
    by_cases ha : mc.progAddresses a
    · rw [if_pos ha, if_pos ha, hgmem a (c3 ▸ ha)]; rfl
    · rw [if_neg ha, if_neg ha]
  have hrd : readFfiBytearraysHOL mc ms2 = (some conf, some bytes2) := by
    simp only [readFfiBytearraysHOL, readFfiBytearrayHOL, hfun]
    rw [c7, c9, c11, c13, hreg _ c6, hreg _ c8, hreg _ c10, hreg _ c12,
      wordLocVal_word_target (c30 _) hptr, wordLocVal_word_target (c30 _) hlen,
      wordLocVal_word_target (c30 _) hptr2, wordLocVal_word_target (c30 _) hlen2,
      readBytearray_stateRel mc code2 labs p s1 t1 ms1 _ _ _ ⟨hrel, hrd1⟩,
      readBytearray_stateRel mc code2 labs p s1 t1 ms1 _ _ _ ⟨hrel, hrd2⟩]
  have hstep : ∀ c, evaluateTargetHOL (shiftInterfer l mc) s1.ffi (c + 1) ms2 =
      match callFFIHOL s1.ffi (.extCall name) conf bytes2 with
      | .final e => (.halt (.ffiOutcome e), ms2, s1.ffi)
      | .ret newFfi newBytes =>
          evaluateTargetHOL { shiftInterfer l mc with ffiInterfer := holShiftSeq 1 mc.ffiInterfer }
            newFfi c (mc.ffiInterfer 0 (getFfiIndex mc.ffiNames (.extCall name), newBytes, ms2)) :=
    fun c => evaluateTarget_extCall (shiftInterfer l mc) s1.ffi c ms2 _ name conf bytes2
      hn hnh hnc hfi he hm hrd
  exact ⟨l, ms2, bound, (hl 0).2.2.2, fun clock => (hl clock).1, hstep⟩

theorem fetched_ffi_final_bounded {F : Type}
    (s1 : LabSem.State 64 Config F) (name : MlString) (w : BitVec 64)
    (mc : MachineConfig 64 riscv_state RiscVProjection) (code2 : LabProgHOL 64)
    (labs : Spt (Spt Nat)) (p : BitVec 64) (t1 : AsmState 64) (ms1 : riscv_state)
    (bytes : List (BitVec 8)) (n : Nat)
    (len start len2 start2 : BitVec 64) (conf bytes2 : List (BitVec 8))
    (target : mc.target = riscvTarget)
    (hfetch : asmFetch s1 = some (.labAsm (.callFFI name) w bytes n))
    (hlen : s1.regs s1.lenReg = .word len) (hptr : s1.regs s1.ptrReg = .word start)
    (hlen2 : s1.regs s1.len2Reg = .word len2) (hptr2 : s1.regs s1.ptr2Reg = .word start2)
    (hrd1 : readBytearrayWordHOL start len.toNat
      (memLoadByteAuxExact s1.memory s1.memDomain s1.be) = some conf)
    (hrd2 : readBytearrayWordHOL start2 len2.toNat
      (memLoadByteAuxExact s1.memory s1.memDomain s1.be) = some bytes2)
    (hec : encoderCorrect mc.target)
    (hrel : stateRel (mc, code2, labs, p) s1 t1 ms1)
    (event : HolFinalEvent)
    (final : callFFIHOL s1.ffi (.extCall name) conf bytes2 = .final event) :
    ∃ count ms2, count ≤ 17 ∧ evaluateTargetHOL mc s1.ffi count ms1 =
      (.halt (.ffiOutcome event), ms2, s1.ffi) := by
  obtain ⟨nativeCount, ms2, bound, positive, run, dispatch⟩ := fetched_ffi_entry_bounded s1 name w
    mc code2 labs p t1 ms1 bytes n len start len2 start2 conf bytes2 target hfetch
    hlen hptr hlen2 hptr2 hrd1 hrd2 hec hrel
  refine ⟨1 + nativeCount, ms2, by omega, ?_⟩
  rw [run 1]
  simpa only [Nat.zero_add, final] using dispatch 0

noncomputable def ffiReturnedSource {F : Type} (s1 : LabSem.State 64 Config F)
    (name : MlString) (start2 : BitVec 64) (newBytes : List (BitVec 8))
    (newPc : Nat) (newFfi : HolFfiState F) : LabSem.State 64 Config F :=
  { s1 with memory := writeBytearrayExact start2 newBytes s1.memory s1.memDomain s1.be
            ffi := newFfi
            ioRegs := holShiftSeq 1 s1.ioRegs
            ioFpRegs := holShiftSeq 1 s1.ioFpRegs
            regs := fun r => getRegValue (s1.ioRegs 0 (.extCall name) r) (s1.regs r) WordLocW.word
            fpRegs := fun r => s1.ioFpRegs 0 r
            pc := newPc
            clock := s1.clock - 1 }

theorem fetched_ffi_return_bounded {F : Type}
    (s1 : LabSem.State 64 Config F) (name : MlString) (w : BitVec 64)
    (mc : MachineConfig 64 riscv_state RiscVProjection) (code2 : LabProgHOL 64)
    (labs : Spt (Spt Nat)) (p : BitVec 64) (t1 : AsmState 64) (ms1 : riscv_state)
    (bytes : List (BitVec 8)) (n : Nat)
    (len start len2 start2 : BitVec 64) (conf bytes2 : List (BitVec 8))
    (target : mc.target = riscvTarget)
    (hfetch : asmFetch s1 = some (.labAsm (.callFFI name) w bytes n))
    (hlen : s1.regs s1.lenReg = .word len) (hptr : s1.regs s1.ptrReg = .word start)
    (hlen2 : s1.regs s1.len2Reg = .word len2) (hptr2 : s1.regs s1.ptr2Reg = .word start2)
    (hrd1 : readBytearrayWordHOL start len.toNat
      (memLoadByteAuxExact s1.memory s1.memDomain s1.be) = some conf)
    (hrd2 : readBytearrayWordHOL start2 len2.toNat
      (memLoadByteAuxExact s1.memory s1.memDomain s1.be) = some bytes2)
    (hec : encoderCorrect mc.target)
    (hrel : stateRel (mc, code2, labs, p) s1 t1 ms1)
    (n1 n2 newPc : Nat) (newFfi : HolFfiState F) (newBytes : List (BitVec 8))
    (ht : oracleTie mc ms1 s1)
    (hlink : s1.regs s1.linkReg = .loc n1 n2)
    (hloc : locToPc n1 n2 s1.code = some newPc)
    (hcall : callFFIHOL s1.ffi (.extCall name) conf bytes2 = .ret newFfi newBytes) :
    ∃ count entry asm2, count + 1 ≤ 17 ∧
      (∀ clock, evaluateTargetHOL mc s1.ffi (clock + (count + 1)) ms1 =
        evaluateTargetHOL { shiftInterfer count mc with ffiInterfer := holShiftSeq 1 mc.ffiInterfer }
          newFfi clock (mc.ffiInterfer 0 (getFfiIndex mc.ffiNames (.extCall name), newBytes, entry))) ∧
      stateRel ({ shiftInterfer count mc with ffiInterfer := holShiftSeq 1 mc.ffiInterfer }, code2, labs, p)
        (ffiReturnedSource s1 name start2 newBytes newPc newFfi) asm2
        (mc.ffiInterfer 0 (getFfiIndex mc.ffiNames (.extCall name), newBytes, entry)) ∧
      oracleTie { shiftInterfer count mc with ffiInterfer := holShiftSeq 1 mc.ffiInterfer }
        (mc.ffiInterfer 0 (getFfiIndex mc.ffiNames (.extCall name), newBytes, entry))
        (ffiReturnedSource s1 name start2 newBytes newPc newFfi) := by
  obtain ⟨c1, c2, c3, -, -, c6, c7, c8, c9, c10, c11, c12, c13, -, c15, c16, -, -, -, -, -, c22,
    -, c24, -, -, -, c28, -, c30, c31, -, -, -, -, -, -, -, ht1f, c40, htpc, -, -, c44, -, -, -,
    -, -, c50, -, c52, -⟩ := id hrel
  -- the target line is a jump to the FFI entry of `name`
  obtain ⟨w', bytes', len', hok, hmem, hpos, hdis⟩ := fetchedLabAsmLine hrel hfetch
  simp only [lineOk] at hok
  obtain ⟨l, ms2, bound, hl⟩ := leading_line_bounded s1.ffi target hrel hec _ bytes' hmem hok.1 hok.2.2 hdis
    (by simp [asmUpd, jumpToOffset, Flapjack.Compiler.Encoders.AsmSem.updPc, ht1f])
  have hts := (hl 0).2.2.1
  obtain ⟨-, hgpc, hgmem, hgreg, -⟩ := hts
  -- the FFI name is an external call below the MMIO boundary
  obtain ⟨i, hi, hiinfo⟩ := c15
  obtain ⟨y, hy⟩ := hasIoName_findIndex s1.code name (imp_hasIoName s1 name w bytes n hfetch)
  have hmemNames : HolFfiName.extCall name ∈ mc.ffiNames := by
    have hm1 := Misc.findIndex_isMem _ _ _ _ hy
    simp only [Misc.listSubset, List.all_eq_true, decide_eq_true_eq] at c22
    exact c22 _ (List.mem_filter.mpr ⟨hm1, rfl⟩)
  have : Nonempty HolFfiName := ⟨.extCall name⟩
  have hidx : getFfiIndex mc.ffiNames (.extCall name) < i :=
    ffiName_not_mapped _ i _ ⟨hi, ⟨name, rfl⟩, hmemNames⟩
  have hidxt : getFfiIndex (mc.ffiNames.take (holThe (mmioPcsMinIndex mc.ffiNames)))
      (.extCall name) = getFfiIndex mc.ffiNames (.extCall name) := by
    rw [hi]; exact getFfiIndex_take _ _ _ hmemNames hidx
  obtain ⟨-, hnp, hnh, hnc, hfi⟩ := c24 _ i ⟨hmemNames, hi, hidx⟩
  have he := el_getFfiIndex_mem _ _ hmemNames
  have hlk : mc.mmioInfo.lookup (getFfiIndex mc.ffiNames (.extCall name)) = none := by
    have := hiinfo (getFfiIndex mc.ffiNames (.extCall name))
    rwa [if_neg (by omega)] at this
  have hm := (sptAListLookup_eq_lookup _ mc.mmioInfo).trans hlk
  -- the target PC after the jump is that FFI entry
  have hjpc : t1.pc + (0 - BitVec.ofNat 64 (posVal s1.pc 0 code2 +
      (3 + getFfiIndex (mc.ffiNames.take (holThe (mmioPcsMinIndex mc.ffiNames)))
        (.extCall name)) * ffiOffset)) =
      p - BitVec.ofNat 64 ((3 + getFfiIndex mc.ffiNames (.extCall name)) * ffiOffset) := by
    rw [htpc, hidxt, BitVec.ofNat_add]; ring
  have hpc2 : mc.target.getPc ms2 =
      p - BitVec.ofNat 64 ((3 + getFfiIndex mc.ffiNames (.extCall name)) * ffiOffset) := by
    rw [hgpc]; simp only [asmUpd, jumpToOffset, Flapjack.Compiler.Encoders.AsmSem.updPc]; exact hjpc
  rw [← hpc2] at hnp hnh hnc hfi
  have hn : ¬ (mc.progAddresses (mc.target.getPc ms2) ∧
      mc.target.getPc ms2 ∉ mc.ffiEntryPcs) := fun h => hnp h.1
  -- the target reads the same two bytearrays
  have hreg : ∀ r, asmRegOkExact r mc.target.config = true →
      mc.target.getReg ms2 r = t1.regs r := by
    intro r hr
    simp only [asmRegOkExact, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hr
    exact hgreg r hr
  classical
  have hfun : (fun a => if mc.progAddresses a then some (mc.target.getByte ms2 a) else none) =
      (fun a => if mc.progAddresses a then some (t1.mem a) else none) := by
    funext a
    by_cases ha : mc.progAddresses a
    · rw [if_pos ha, if_pos ha, hgmem a (c3 ▸ ha)]; rfl
    · rw [if_neg ha, if_neg ha]
  have hrd : readFfiBytearraysHOL mc ms2 = (some conf, some bytes2) := by
    simp only [readFfiBytearraysHOL, readFfiBytearrayHOL, hfun]
    rw [c7, c9, c11, c13, hreg _ c6, hreg _ c8, hreg _ c10, hreg _ c12,
      wordLocVal_word_target (c30 _) hptr, wordLocVal_word_target (c30 _) hlen,
      wordLocVal_word_target (c30 _) hptr2, wordLocVal_word_target (c30 _) hlen2,
      readBytearray_stateRel mc code2 labs p s1 t1 ms1 _ _ _ ⟨hrel, hrd1⟩,
      readBytearray_stateRel mc code2 labs p s1 t1 ms1 _ _ _ ⟨hrel, hrd2⟩]
  have hstep : ∀ c, evaluateTargetHOL (shiftInterfer l mc) s1.ffi (c + 1) ms2 =
      match callFFIHOL s1.ffi (.extCall name) conf bytes2 with
      | .final e => (.halt (.ffiOutcome e), ms2, s1.ffi)
      | .ret newFfi newBytes =>
          evaluateTargetHOL { shiftInterfer l mc with ffiInterfer := holShiftSeq 1 mc.ffiInterfer }
            newFfi c (mc.ffiInterfer 0 (getFfiIndex mc.ffiNames (.extCall name), newBytes, ms2)) :=
    fun c => evaluateTarget_extCall (shiftInterfer l mc) s1.ffi c ms2 _ name conf bytes2
      hn hnh hnc hfi he hm hrd
  have hlenb : newBytes.length = len2.toNat :=
    (StackRemove.callFFILengthHOL _ _ _ _ _ _ hcall).trans (readBytearrayWordHOL_length _ _ _ _ hrd2)
  have hrd2' : readBytearrayWordHOL start2 newBytes.length
      (memLoadByteAuxExact s1.memory s1.memDomain s1.be) = some bytes2 := by
    rw [hlenb]; exact hrd2
  have hstart2 : t1.regs s1.ptr2Reg = start2 := wordLocVal_word_target (c30 _) hptr2
  have hlinkv : t1.regs s1.linkReg = p + BitVec.ofNat 64 (posVal newPc 0 code2) := by
    have := c30 s1.linkReg
    rw [hlink] at this
    simp only [wordLocVal, c28 n1 n2 newPc hloc, Option.some.injEq] at this
    exact this.symm
  -- the returned registers are the external-call oracle's
  obtain ⟨hres1, hres2⟩ := oracleTie_extCallResidues mc ms1 ms2 s1 l _ name conf bytes2 newBytes
    newFfi t1 ⟨ht, fun k => (hl k).2.1, hn, hnh, hnc, hfi, he, hlk, hrd, hcall⟩
  have hts2 : targetStateRel mc.target
      { t1 with
        pc := p - BitVec.ofNat 64 ((3 + getFfiIndex mc.ffiNames (.extCall name)) * ffiOffset) }
      ms2 := by
    have := (hl 0).2.2.1
    simp only [asmUpd, jumpToOffset, Flapjack.Compiler.Encoders.AsmSem.updPc, hjpc] at this
    exact this
  have htrel := c16 ms2 0 _ newBytes t1 conf bytes2 s1.ffi newFfi i
    ⟨hi, hidx, hrd, .refl, by rw [he]; exact hcall, c3, hts2,
      by rw [hlinkv]; exact stateRel_aligned_target hrel hec newPc⟩
  dsimp only at htrel
  rw [← hres1, ← hres2, hstart2, hlinkv] at htrel
  -- the complete relation after the call
  have hdom : ∀ a, s1.memDomain (riscvByteAlignHOL a) = true → s1.memDomain a = true :=
    fun a h => (c31 a (by rwa [← riscvByteAlignHOL_eq c2])).2.1
  have hbe : s1.be = mc.target.config.bigEndian := c40.trans c44
  have hrel'0 := stateRel_ffiReturn hrel newFfi ⟨_, _, _, _, hcall⟩
    (fun r => getRegValue (s1.ioRegs 0 (.extCall name) r) (s1.regs r) WordLocW.word)
    (fun r => s1.ioFpRegs 0 r)
    (writeBytearrayExact start2 newBytes s1.memory s1.memDomain s1.be)
    (holShiftSeq 1 s1.ioRegs) (holShiftSeq 1 s1.ioFpRegs) newPc (s1.clock - 1)
    _ _ _ _ htrel
    (fun r => by
      cases hio : s1.ioRegs 0 (.extCall name) r with
      | none => simpa [getRegValue] using c30 r
      | some v => simp [getRegValue, wordLocVal])
    (fun _ => rfl)
    (fun a ha => by
      obtain ⟨h1, h2, h3⟩ := c31 a ha
      have := callFFI_bytearray_lemma mc p labs s1 t1 a newBytes start2 bytes2
        ⟨ha, c2, h1, h2, hbe, hrd2', by rw [← hbe]; exact h3⟩
      simpa only [← hbe] using this)
    (fun a ha => asmWriteBytearray_outside s1.memory s1.memDomain s1.be t1.mem hdom newBytes
      start2 bytes2 hrd2' a ha)
    rfl
  have hrel' := stateRel_shiftInterfer _ _ _ _ _ _ _ l hrel'0
  -- the oracle tie after the FFI interference
  have ht2 := oracleTie_shiftInterfer mc ms1 ms2 s1 l ⟨ht, fun k => (hl k).2.1⟩
  have hnext := nextInterferenceExtCall (shiftInterfer l mc) s1.ffi ms2 _ name conf bytes2
    newBytes newFfi ⟨hn, hnh, hnc, hfi, he, hm, hrd, hcall⟩
  have ht3 : oracleTie { shiftInterfer l mc with ffiInterfer := holShiftSeq 1 mc.ffiInterfer }
      (mc.ffiInterfer 0 (getFfiIndex mc.ffiNames (.extCall name), newBytes, ms2))
      { s1 with
        memory := writeBytearrayExact start2 newBytes s1.memory s1.memDomain s1.be
        ffi := newFfi
        ioRegs := holShiftSeq 1 s1.ioRegs
        ioFpRegs := holShiftSeq 1 s1.ioFpRegs
        regs := fun r => getRegValue (s1.ioRegs 0 (.extCall name) r) (s1.regs r) WordLocW.word
        fpRegs := fun r => s1.ioFpRegs 0 r
        pc := newPc
        clock := s1.clock - 1 } :=
    oracleTie_ffiNext (shiftInterfer l mc) ms2 s1 _ _ newBytes ms2 _ _ newFfi
      ⟨ht2, hnext, rfl, rfl, rfl, rfl, rfl⟩
  refine ⟨l, ms2, _, by omega, ?_, hrel', ht3⟩
  intro clock
  rw [show clock + (l + 1) = (clock + 1) + l by omega, (hl _).1, hstep, hcall]

end InitECandidate.Runtime.LabToTarget
#print axioms InitECandidate.Runtime.LabToTarget.fetched_ffi_entry_bounded

#print axioms InitECandidate.Runtime.LabToTarget.fetched_ffi_final_bounded

#print axioms InitECandidate.Runtime.LabToTarget.fetched_ffi_return_bounded
