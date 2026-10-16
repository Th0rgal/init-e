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

end InitECandidate.Runtime.LabToTarget
#print axioms InitECandidate.Runtime.LabToTarget.fetched_ffi_entry_bounded

#print axioms InitECandidate.Runtime.LabToTarget.fetched_ffi_final_bounded
