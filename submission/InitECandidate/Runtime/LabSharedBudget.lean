import Flapjack.Compiler.Backend.LabToTarget.CompileCorrect.ShareMem

namespace InitECandidate.Runtime.LabToTarget
open Flapjack Flapjack.Compiler.Encoders Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Encoders.AsmSem Flapjack.Compiler.Encoders.AsmProps
open Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend.Semantics.TargetProps
open Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.LabToTarget

/-- Exact one-clock shared-memory dispatch derived from the compiler state
relation and the real source operation. Both terminal and returning calls
retain their full native and source state effects. -/
theorem shared_native_core {width : Nat} [NeZero width] {S Q F : Type}
    (s1 : LabSem.State width Config F) (m : HolMemop) (r base : Nat) (off : BitVec width)
    (bytes : List (BitVec 8)) (n : Nat)
    (mc : MachineConfig width S Q) (code2 : LabProgHOL width) (labs : Spt (Spt Nat))
    (p : BitVec width) (t1 : AsmState width) (ms1 : S)
    (hfetch : asmFetch s1 = some (.asm (.shareMem m r (.addr base off)) bytes n))
    (hrel : stateRel (mc, code2, labs, p) s1 t1 ms1)
    (x : HolFfiResult F) (next : LabSem.State width Config F)
    (hso : shareMemOp m r (.addr base off) s1 = some (x, next)) :
    ∃ index : Nat,

      (∀ c, evaluateTargetHOL mc s1.ffi (c + 1) ms1 =
        match x with
        | .final e => (.halt (.ffiOutcome e), ms1, s1.ffi)
        | .ret f bs => evaluateTargetHOL { mc with ffiInterfer := holShiftSeq 1 mc.ffiInterfer }
            f c (mc.ffiInterfer 0 (index, bs, ms1))) ∧
      (∀ e, x = .final e → next = s1) ∧
      (∀ f bs, x = .ret f bs →
        nextInterference mc s1.ffi ms1 = some
          (.ffiApp index bs ms1 (mc.ffiInterfer 0 (index, bs, ms1)),
            { mc with ffiInterfer := holShiftSeq 1 mc.ffiInterfer }, f) ∧
        callFFIRelHOL s1.ffi f ∧
        ∃ tregs regs, targetStateRel mc.target
            { t1 with regs := tregs, pc := p + BitVec.ofNat width (posVal (s1.pc + 1) 0 code2) }
            (mc.ffiInterfer 0 (index, bs, ms1)) ∧
          (∀ y, wordLocVal p labs (regs y) = some (tregs y)) ∧
          next = { s1 with ffi := f, regs := regs, pc := s1.pc + 1, clock := s1.clock - 1 }) := by
  obtain ⟨c1, c2, c3, -, -, -, -, -, -, -, -, -, -, -, c15, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, c30, -, -, c33, -, -, -, -, -, -, -, c41, -, -, -, -, -, c47, -, c49, c50, c51, c52,
    -⟩ := id hrel
  obtain ⟨bytes', hf2, henc, hbm, -, hpos, hok⟩ :=
    imp_bytesInMemory_shareMem mc labs _ s1 code2 p t1 m r (.addr base off) bytes n
      ⟨hfetch, c49, c47, c33⟩
  obtain ⟨i, hi, -⟩ := c15
  obtain ⟨index, hle, hfi, hinfo⟩ := c51.1 s1.pc m r (.addr base off) bytes' bytes'.length i
    ⟨hf2, hi⟩
  have hpc : mc.target.getPc ms1 = p + BitVec.ofNat width (posVal s1.pc 0 code2) :=
    c1.2.1.trans c41
  rw [← hpc] at hfi
  have hlt : index < mc.ffiNames.length := by
    have := (Misc.findIndexLessLength _ _ _ _ hfi).2
    rw [c52]; omega
  have hn : ¬ (mc.progAddresses (mc.target.getPc ms1) ∧
      mc.target.getPc ms1 ∉ mc.ffiEntryPcs) :=
    fun h => h.2 (Misc.findIndex_isMem _ _ _ _ hfi)
  obtain ⟨hcc, hhalt⟩ := ffiEntryPcs_not_ccache_or_halt _ mc index
    ⟨hfi, (c50.2 index i ⟨hi, hlt, hle⟩).1, (c50.2 index i ⟨hi, hlt, hle⟩).2⟩
  have hentry : holEl index mc.ffiEntryPcs = t1.pc := by
    have := (findIndex_holEl _ _ 0 index hfi).2
    rw [Nat.sub_zero] at this
    rw [this, c1.2.1]
  have hts0 : targetStateRel mc.target { t1 with pc := holEl index mc.ffiEntryPcs } ms1 := by
    rw [hentry]; exact c1
  -- registers read by the target instruction
  simp only [asmOkExact, asmInstOkExact, asmRegOkExact, Bool.and_eq_true, decide_eq_true_eq,
    Bool.not_eq_true'] at hok
  have hgr : ∀ x, x < mc.target.config.regCount →
      mc.target.config.avoidRegs.contains x = false → mc.target.getReg ms1 x = t1.regs x :=
    fun x h1 h2 => c1.2.2.2.1 x ⟨h1, h2⟩
  have htreg : ∀ x w, s1.regs x = .word w → t1.regs x = w := by
    intro x w hx
    have := c30 x; rw [hx] at this; simpa [wordLocVal] using this.symm
  -- the encoded instruction is in target memory at the entry PC
  have henc' : bytesInMemoryHOL (mc.target.getPc ms1)
      (mc.target.config.encode (.inst (.mem m r (.addr base off)))) (mc.target.getByte ms1)
      mc.progAddresses := by
    obtain ⟨cnt, hcnt⟩ := (encWithNop_iff _ _ _).mp henc
    rw [hcnt, bytesInMemory_append] at hbm
    rw [hpc, c3]
    refine bytesInMemory_changeMem _ _ t1.mem _ _ ⟨hbm.1, fun k hk => ?_⟩
    exact (c1.2.2.1 _ (bytesInMemoryInDomain _ _ _ _ k ⟨hbm.1, hk⟩)).symm
  have hshared : ∀ v, s1.sharedMemDomain (holByteAlign v) = true →
      mc.sharedAddresses v := by
    intro v hv
    rw [c51.2.2.2]; exact c51.2.2.1 v hv
  have hshared0 : ∀ v, s1.sharedMemDomain v = true → mc.sharedAddresses v := by
    intro v hv; rw [c51.2.2.2]; exact hv
  have hwidth : 4 ≤ width / 8 := by rcases c2 with h | h <;> simp [h]
  refine ⟨index, ?_⟩

  have hgb : ∀ wb, s1.regs base = .word wb → mc.target.getReg ms1 base = wb :=
    fun wb hb => (hgr base hok.1.2.1 hok.1.2.2).trans (htreg base wb hb)
  rcases shareMemOp_load_or_store (width := width) m with
    ⟨size, hsz, hgi, hop, hvalid⟩ | ⟨size, hsz, hgi, hop, hvalid⟩
  all_goals
    rw [hgi] at hinfo
    obtain ⟨he, hlk⟩ := hinfo
    have hm := (sptAListLookup_eq_lookup index mc.mmioInfo).trans hlk
    have hsize0 : BitVec.ofNat 8 size = 0 ↔ size = 0 := by
      rcases hsz with rfl | rfl | rfl | rfl <;> decide
    have hv := (hvalid (mc.target.getPc ms1) r (.addr base off)
      (p + BitVec.ofNat width (posVal s1.pc 0 code2 + bytes'.length)) mc.target ms1
      mc.progAddresses).2 henc'
    rw [hop] at hso
  · -- loads
    simp only [shareMemLoad, addrValue] at hso
    cases hb : s1.regs base with
    | loc _ _ => simp [hb] at hso
    | word wb =>
    simp only [hb] at hso
    by_cases hcond : (if size = 0 then
        ((wb + off).toNat % (width / 8) == 0 && s1.sharedMemDomain (wb + off))
      else s1.sharedMemDomain (riscvByteAlignHOL (wb + off))) = true
    swap
    · rw [if_neg hcond] at hso; cases hso
    rw [if_pos hcond] at hso
    have hal : BitVec.ofNat 8 size = 0 →
        (mc.target.getReg ms1 base + off).toNat % (width / 8) = 0 := by
      intro h0
      rw [hsize0] at h0
      rw [if_pos h0] at hcond
      simp only [Bool.and_eq_true, beq_iff_eq] at hcond
      rw [hgb wb hb]; exact hcond.1
    have hsh : mc.sharedAddresses (mc.target.getReg ms1 base + off) := by
      rw [hgb wb hb]
      by_cases h0 : size = 0
      · rw [if_pos h0] at hcond
        simp only [Bool.and_eq_true] at hcond
        exact hshared0 _ hcond.2
      · rw [if_neg h0, riscvByteAlignHOL_eq c2] at hcond
        exact hshared _ hcond
    have hstep := fun c => evaluateTarget_mappedRead mc s1.ffi c ms1 index _ base r off _
      hn hhalt hcc hfi he hm hal hsh hv
    have hcallT : HolByte.wordToBytes (mc.target.getReg ms1 base + off) false =
        sharedMemoryWordBytes (wb + off) := by
      rw [hgb wb hb, sharedMemoryWordBytes_eq]
    rw [hcallT] at hstep
    cases hcall : callFFIHOL s1.ffi (.sharedMem .mappedRead) [BitVec.ofNat 8 size]
        (sharedMemoryWordBytes (wb + off)) with
    | final e =>
      rw [hcall] at hso hstep
      simp only [Option.some.injEq, Prod.mk.injEq] at hso
      obtain ⟨rfl, rfl⟩ := hso
      exact ⟨hstep, fun _ _ => rfl, fun _ _ h => by cases h⟩
    | ret f bs =>
      rw [hcall] at hso hstep
      simp only [Option.some.injEq, Prod.mk.injEq] at hso
      obtain ⟨rfl, rfl⟩ := hso
      refine ⟨hstep, (fun _ h => by cases h), fun f' bs' h => ?_⟩
      cases h
      obtain ⟨op, hop', hmatch⟩ := c50.1 ms1 0 index bs t1 (BitVec.ofNat 8 size) base off r _
        (mc.target.getReg ms1 base + off) s1.ffi f i
        ⟨hi, hle, hlt, .refl, hlk, c3, rfl, hts0⟩
      rw [he] at hop'
      cases hop'
      have htrel := hmatch ⟨by split; exact hal ‹_›; trivial, hsh, hv, by
        rw [hcallT]; exact hcall⟩
      refine ⟨nextInterferenceSharedMem mc s1.ffi ms1 index base r _ off _ .mappedRead bs f
          ⟨hn, hhalt, hcc, hfi, he, hm, hal, hsh, fun _ => ⟨hv, by rw [he, hcallT]; exact hcall⟩,
            fun h => by cases h⟩,
        ⟨_, _, _, _, hcall⟩, fun n => if n = r then HolByte.wordOfBytes false 0 bs else t1.regs n,
        _, ?_, ?_, rfl⟩
      · rw [hpos]; exact htrel
      · intro y
        by_cases hy : y = r
        · simp [hy, wordLocVal, wordOfBytesHOL8_eq]
        · simpa [hy] using c30 y
  · -- stores
    simp only [shareMemStore, addrValue] at hso
    cases hw : s1.regs r with
    | loc _ _ => simp [hw] at hso
    | word w =>
    cases hb : s1.regs base with
    | loc _ _ => simp [hw, hb] at hso
    | word wb =>
    simp only [hw, hb] at hso
    by_cases hcond : (if size = 0 then
        ((wb + off).toNat % (width / 8) == 0 && s1.sharedMemDomain (wb + off))
      else s1.sharedMemDomain (riscvByteAlignHOL (wb + off))) = true
    swap
    · rw [if_neg hcond] at hso; cases hso
    rw [if_pos hcond] at hso
    have hal : BitVec.ofNat 8 size = 0 →
        (mc.target.getReg ms1 base + off).toNat % (width / 8) = 0 := by
      intro h0
      rw [hsize0] at h0
      rw [if_pos h0] at hcond
      simp only [Bool.and_eq_true, beq_iff_eq] at hcond
      rw [hgb wb hb]; exact hcond.1
    have hsh : mc.sharedAddresses (mc.target.getReg ms1 base + off) := by
      rw [hgb wb hb]
      by_cases h0 : size = 0
      · rw [if_pos h0] at hcond
        simp only [Bool.and_eq_true] at hcond
        exact hshared0 _ hcond.2
      · rw [if_neg h0, riscvByteAlignHOL_eq c2] at hcond
        exact hshared _ hcond
    have hstep := fun c => evaluateTarget_mappedWrite mc s1.ffi c ms1 index _ base r off _
      hn hhalt hcc hfi he hm hal hsh hv
    have hgw : mc.target.getReg ms1 r = w :=
      (hgr r hok.1.1.1 hok.1.1.2).trans (htreg r w hw)
    have hcallT : ((if BitVec.ofNat 8 size = 0 then
          HolByte.wordToBytes (mc.target.getReg ms1 r) false
        else HolByte.wordToBytesAux (BitVec.ofNat 8 size).toNat (mc.target.getReg ms1 r) false) ++
        HolByte.wordToBytes (mc.target.getReg ms1 base + off) false) =
        ((if size = 0 then sharedMemoryWordBytes w
          else (sharedMemoryWordBytes w).take size) ++ sharedMemoryWordBytes (wb + off)) := by
      rw [hgb wb hb, hgw, sharedMemoryWordBytes_eq, sharedMemoryWordBytes_eq]
      rcases hsz with rfl | rfl | rfl | rfl
      · rfl
      all_goals
        simp only [BitVec.ofNat_eq_ofNat, show ¬ ((1 : Nat) = 0) from by decide,
          show ¬ ((2 : Nat) = 0) from by decide, show ¬ ((4 : Nat) = 0) from by decide,
          ↓reduceIte]
        rw [take_wordToBytes _ _ (by omega)]
        rfl
    rw [hcallT] at hstep
    cases hcall : callFFIHOL s1.ffi (.sharedMem .mappedWrite) [BitVec.ofNat 8 size]
        ((if size = 0 then sharedMemoryWordBytes w
          else (sharedMemoryWordBytes w).take size) ++ sharedMemoryWordBytes (wb + off)) with
    | final e =>
      rw [hcall] at hso hstep
      simp only [Option.some.injEq, Prod.mk.injEq] at hso
      obtain ⟨rfl, rfl⟩ := hso
      exact ⟨hstep, fun _ _ => rfl, fun _ _ h => by cases h⟩
    | ret f bs =>
      rw [hcall] at hso hstep
      simp only [Option.some.injEq, Prod.mk.injEq] at hso
      obtain ⟨rfl, rfl⟩ := hso
      refine ⟨hstep, (fun _ h => by cases h), fun f' bs' h => ?_⟩
      cases h
      obtain ⟨op, hop', hmatch⟩ := c50.1 ms1 0 index bs t1 (BitVec.ofNat 8 size) base off r _
        (mc.target.getReg ms1 base + off) s1.ffi f i
        ⟨hi, hle, hlt, .refl, hlk, c3, rfl, hts0⟩
      rw [he] at hop'
      cases hop'
      have htrel := hmatch ⟨by split; exact hal ‹_›; trivial, hsh, hv, by
        rw [hcallT]; exact hcall⟩
      refine ⟨nextInterferenceSharedMem mc s1.ffi ms1 index base r _ off _ .mappedWrite bs f
          ⟨hn, hhalt, hcc, hfi, he, hm, hal, hsh, (fun h => by cases h),
            fun _ => ⟨hv, by rw [he, hcallT]; exact hcall⟩⟩,
        ⟨_, _, _, _, hcall⟩, t1.regs, s1.regs, ?_, c30, rfl⟩
      rw [hpos]; exact htrel

/-- Shared-memory return advances exactly one FFI interference and restores
both the full compiler relation and the oracle tie. -/
theorem shared_return_native {width : Nat} [NeZero width] {S Q F : Type}
    (state : LabSem.State width Config F) (m : HolMemop) (r base : Nat) (off : BitVec width)
    (bytes : List (BitVec 8)) (n : Nat)
    (mc : MachineConfig width S Q) (code : LabProgHOL width) (labs : Spt (Spt Nat))
    (p : BitVec width) (asm : AsmState width) (machine : S)
    (fetch : asmFetch state = some (.asm (.shareMem m r (.addr base off)) bytes n))
    (related : stateRel (mc, code, labs, p) state asm machine) (tie : oracleTie mc machine state)
    (ffi : HolFfiState F) (returned : List (BitVec 8)) (next : LabSem.State width Config F)
    (operation : shareMemOp m r (.addr base off) state = some (.ret ffi returned, next)) :
    ∃ index asm2,
      (∀ clock, evaluateTargetHOL mc state.ffi (clock + 1) machine =
        evaluateTargetHOL { mc with ffiInterfer := holShiftSeq 1 mc.ffiInterfer } ffi clock
          (mc.ffiInterfer 0 (index, returned, machine))) ∧
      stateRel ({ mc with ffiInterfer := holShiftSeq 1 mc.ffiInterfer }, code, labs, p)
        { next with ioRegs := holShiftSeq 1 next.ioRegs, ioFpRegs := holShiftSeq 1 next.ioFpRegs }
        asm2 (mc.ffiInterfer 0 (index, returned, machine)) ∧
      oracleTie { mc with ffiInterfer := holShiftSeq 1 mc.ffiInterfer }
        (mc.ffiInterfer 0 (index, returned, machine))
        { next with ioRegs := holShiftSeq 1 next.ioRegs, ioFpRegs := holShiftSeq 1 next.ioFpRegs } ∧
      next.clock = state.clock - 1 ∧ next.code = state.code := by
  obtain ⟨index, run, finalCase, retCase⟩ := shared_native_core state m r base off bytes n
    mc code labs p asm machine fetch related (.ret ffi returned) next operation
  obtain ⟨interference, ffiRel, tregs, regs, targetRel, registers, nextEq⟩ := retCase ffi returned rfl
  subst next
  have rel := stateRel_shareMem related ffi ffiRel regs (holShiftSeq 1 state.ioRegs)
    (holShiftSeq 1 state.ioFpRegs) tregs _ targetRel registers rfl
  let returnedState : LabSem.State width Config F :=
    { state with ffi := ffi, regs := regs, pc := state.pc + 1, clock := state.clock - 1, ioRegs := holShiftSeq 1 state.ioRegs, ioFpRegs := holShiftSeq 1 state.ioFpRegs }
  have tied := oracleTie_ffiNext mc machine state returnedState index returned machine _ _ ffi
    ⟨tie, interference, rfl, rfl, rfl, rfl, rfl⟩
  exact ⟨index, _, run, rel, tied, rfl, rfl⟩

theorem shared_final_native {width : Nat} [NeZero width] {S Q F : Type}
    (state : LabSem.State width Config F) (m : HolMemop) (r base : Nat) (off : BitVec width)
    (bytes : List (BitVec 8)) (n : Nat)
    (mc : MachineConfig width S Q) (code : LabProgHOL width) (labs : Spt (Spt Nat))
    (p : BitVec width) (asm : AsmState width) (machine : S)
    (fetch : asmFetch state = some (.asm (.shareMem m r (.addr base off)) bytes n))
    (related : stateRel (mc, code, labs, p) state asm machine)
    (event : HolFinalEvent) (next : LabSem.State width Config F)
    (operation : shareMemOp m r (.addr base off) state = some (.final event, next)) :
    next = state ∧ evaluateTargetHOL mc state.ffi 1 machine = (.halt (.ffiOutcome event), machine, state.ffi) := by
  obtain ⟨index, run, finalCase, retCase⟩ := shared_native_core state m r base off bytes n
    mc code labs p asm machine fetch related (.final event) next operation
  exact ⟨finalCase event rfl, run 0⟩

end InitECandidate.Runtime.LabToTarget
#print axioms InitECandidate.Runtime.LabToTarget.shared_native_core

#print axioms InitECandidate.Runtime.LabToTarget.shared_return_native
#print axioms InitECandidate.Runtime.LabToTarget.shared_final_native
