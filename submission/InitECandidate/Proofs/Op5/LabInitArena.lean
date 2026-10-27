import InitECandidate.Proofs.Op5.InitPipelineArena
import Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInitSemantics

namespace InitE.Op5
open Flapjack Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackRemove.Proofs
open Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.StackToLab.Proofs
open Flapjack.Compiler.Backend.LabLang
open Flapjack.Compiler.Backend.StackToLab
open Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInitSemantics

/-- The Lab memory contract with an independent owned arena. -/
noncomputable def memoryAssumptionWithArena {width : Nat} [NeZero width] {C F : Type}
    (rnames : Spt Nat) (bitmaps : List (BitVec width)) (dataSp : Nat)
    (t : Flapjack.Compiler.Backend.LabSem.State width C F) (arena : BitVec width → Prop) : Prop :=
  ∃ ptr2 ptr3 ptr4 bitmapPtr : BitVec width,
    t.regs (StackNames.findNameSpt rnames 2) = .word ptr2 ∧
    t.regs (StackNames.findNameSpt rnames 3) = .word ptr3 ∧
    t.regs (StackNames.findNameSpt rnames 4) = .word ptr4 ∧
    t.memory ptr2 = .word bitmapPtr ∧
    t.memory (ptr2 + StackRemove.bytesInWord width) =
      .word (bitmapPtr + StackRemove.bytesInWord width * BitVec.ofNat width bitmaps.length) ∧
    t.memory (ptr2 + 2 * StackRemove.bytesInWord width) =
      .word (bitmapPtr + StackRemove.bytesInWord width * BitVec.ofNat width dataSp +
        StackRemove.bytesInWord width * BitVec.ofNat width bitmaps.length) ∧
    t.memory (ptr2 + 3 * StackRemove.bytesInWord width) = .word t.codeBuffer.position ∧
    t.memory (ptr2 + 4 * StackRemove.bytesInWord width) =
      .word (t.codeBuffer.position + BitVec.ofNat width t.codeBuffer.spaceLeft) ∧
    t.codeBuffer.buffer = [] ∧
    ptr2 ≤ ptr4 ∧ holByteAligned ptr2 = true ∧
    holByteAligned ptr4 = true ∧ holByteAligned bitmapPtr = true ∧
    1024 * StackRemove.bytesInWord width ≤ ptr4 - ptr2 ∧
    SetSep.star
      (SetSep.star
        (SetSep.star (Misc.wordList bitmapPtr (bitmaps.map WordLocW.word))
        (Misc.wordListExists
          (bitmapPtr + StackRemove.bytesInWord width * BitVec.ofNat width bitmaps.length) dataSp))
        (memoryHOL t.memory arena))
      (Misc.wordListExists ptr2
        ((-1 * ptr2 + ptr4).toNat / (StackRemove.bytesInWord width).toNat))
      (SetSep.fun2Set (t.memory, fun a => t.memDomain a = true))


def labAssumptionsWithArena {width : Nat} [NeZero width] {C F : Type}
    (stackConf : StackToLab.Config) (dataConf : DataToWord.Config) (maxHeap sp : Nat)
    (offset : BitVec width × BitVec width) (bitmaps : List (BitVec width))
    (code : List (Nat × HolProg width)) (t : Flapjack.Compiler.Backend.LabSem.State width C F)
    (saveRegs : Nat → Bool) (dataSp : Nat)
    (coracle : Nat → C × List (Nat × HolProg width) × List (BitVec width)) (arena : BitVec width → Prop) : Prop :=
  goodDimindex width ∧
  t.code = StackToLab.compile stackConf dataConf maxHeap sp offset code ∧
  t.compileOracle = (fun n => ((coracle n).1,
    StackToLab.compileNoStubs stackConf.regNames stackConf.jump offset sp (coracle n).2.1)) ∧
  ¬t.failed = true ∧
  memoryAssumptionWithArena stackConf.regNames bitmaps dataSp t arena ∧
  StackRemove.maxStackAlloc ≤ maxHeap ∧
  ¬saveRegs t.linkReg = true ∧ t.pc = 0 ∧
  (∀ k i n, saveRegs k = true → t.ioRegs n i k = none) ∧
  (∀ k n, saveRegs k = true → t.ccRegs n k = none) ∧
  (∀ x : BitVec width, t.memDomain x = true → x.toNat % (width / 8) = 0) ∧
  (∀ x : BitVec width, t.sharedMemDomain x = true → x.toNat % (width / 8) = 0) ∧
  GoodCode.goodCode sp code ∧
  (∀ n, GoodCode.goodCode sp (coracle n).2.1) ∧
  10 ≤ sp ∧
  (∀ r ∈ [2, 3, 4], saveRegs (StackNames.findNameSpt stackConf.regNames (r + sp - 2)) = true) ∧
  StackNames.findNameSpt stackConf.regNames 4 = t.len2Reg ∧
  StackNames.findNameSpt stackConf.regNames 3 = t.ptr2Reg ∧
  StackNames.findNameSpt stackConf.regNames 2 = t.lenReg ∧
  StackNames.findNameSpt stackConf.regNames 1 = t.ptrReg ∧
  StackNames.findNameSpt stackConf.regNames 0 = t.linkReg ∧
  Function.Bijective (StackNames.findNameSpt stackConf.regNames)


variable {width : Nat} [NeZero width] {C F : Type}
  (stackConf : StackToLab.Config) (dataConf : DataToWord.Config) (maxHeap sp : Nat)
  (offset : BitVec width × BitVec width) (bitmaps : List (BitVec width))
  (code : List (Nat × HolProg width)) (t : Flapjack.Compiler.Backend.LabSem.State width C F)
  (saveRegs : Nat → Bool) (dataSp : Nat)
  (coracle : Nat → C × List (Nat × HolProg width) × List (BitVec width))


theorem propagateThese_s2_withArena
    (arena : BitVec width → Prop)
    (gd : goodDimindex width)
    (hmem : memoryAssumptionWithArena stackConf.regNames bitmaps dataSp t arena)
    (hbij : Function.Bijective (StackNames.findNameSpt stackConf.regNames)) :
    propagateTheseWithArena
      (s2 stackConf dataConf maxHeap sp offset code t saveRegs coracle) bitmaps dataSp arena := by
  obtain ⟨ptr2, ptr3, ptr4, bp, r2, r3, r4, m0, m1, m2, m3, m4, cb, le, a2, a4, abp, big, sep⟩ :=
    hmem
  obtain ⟨-, -, -, -, -, hm, hd, hcb, -⟩ := s2_fields (stackConf := stackConf)
    (dataConf := dataConf) (maxHeap := maxHeap) (sp := sp) (offset := offset) (code := code)
    (t := t) (saveRegs := saveRegs) (coracle := coracle)
  refine ⟨gd, ptr2, ptr3, ptr4, bp, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, a2, a4, abp, ?_, ?_⟩
  · rw [s2_regs_lookup hbij (.inl rfl), r2]
  · rw [s2_regs_lookup hbij (.inr (.inl rfl)), r3]
  · rw [s2_regs_lookup hbij (.inr (.inr rfl)), r4]
  · rw [hm]; exact m0
  · rw [hm]; exact m1
  · rw [hm, m2, BitVec.add_assoc, BitVec.add_comm (StackRemove.bytesInWord width * _),
      ← BitVec.add_assoc]
  · rw [hm, hcb]; exact m3
  · rw [hm, hcb]; exact m4
  · rw [hcb]; exact cb
  · exact BitVec.le_def.mp le
  · exact BitVec.le_def.mp big
  · rw [hm, hd]; exact sep

theorem dischargeThese_s2_withArena
    (arena : BitVec width → Prop)
    (hA : labAssumptionsWithArena stackConf dataConf maxHeap sp offset bitmaps code t saveRegs dataSp coracle arena) :
    StackRemove.Proofs.InitMake.dischargeThese stackConf.jump offset
      (StackToLab.isGenGc dataConf.gcKind) maxHeap sp BvlToBvi.initGlobalsLocation
      (coracle1 coracle) (code1 dataConf code)
      (s2 stackConf dataConf maxHeap sp offset code t saveRegs coracle) := by
  obtain ⟨-, -, -, -, -, hmax, -, -, -, -, -, -, hgood, hgoodO, hsp, hsave, -, -, -, -, -,
    hbij⟩ := id hA
  obtain ⟨hcode, horacle, hus, hust, hua, -⟩ := s2_fields (stackConf := stackConf)
    (dataConf := dataConf) (maxHeap := maxHeap) (sp := sp) (offset := offset) (code := code)
    (t := t) (saveRegs := saveRegs) (coracle := coracle)
  refine ⟨?_, ?_, ?_, hcode, by omega, ?_, ?_, hus, hust, hua, hmax⟩
  · intro entry hmem
    refine ⟨StackAlloc.stack_alloc_reg_bound ⟨hsp, StackRawCall.stackRawcallRegBound.mpr
      hgood.2.2.2.1⟩ entry.2 (List.mem_map.mpr ⟨entry, hmem, rfl⟩), ?_⟩
    simp only [code1, StackAlloc.compile, StackAlloc.stubs, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false, List.mem_map] at hmem
    rcases hmem with rfl | ⟨⟨n0, p0⟩, hm, rfl⟩
    · simp [stackNumStubs, gcStubLocation]
    · simp only [StackRawCall.compile, List.mem_map, Prod.mk.injEq] at hm
      obtain ⟨⟨n1, p1⟩, hm1, rfl, -⟩ := hm
      have := (hgood.2.1 _ hm1).1
      simp only [StackAlloc.progComp]
      omega
  · intro n i p hm
    simp only [coracle1, Function.comp_apply, Prod.map, id, List.mem_map] at hm
    obtain ⟨⟨n0, p0⟩, hm0, he⟩ := hm
    simp only [StackAlloc.progComp, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    obtain ⟨-, hal, -, hrb, -⟩ := hgoodO n
    refine ⟨StackAlloc.ConventionSupport.comp_regBound hsp _ _ _
      (hrb p0 (List.mem_map.mpr ⟨_, hm0, rfl⟩)), ?_⟩
    have := (hal _ hm0).1
    omega
  · rw [horacle]
    funext n
    simp [coracle2, Prod.map]
  · rw [hcode, sptDomain_sptFromAList, code2_fst]
    simp
  · intro r hr
    have key : ∃ x, saveRegs x = true ∧
        r = holLinv (StackNames.findNameSpt stackConf.regNames) (fun _ => True) x := by
      refine ⟨StackNames.findNameSpt stackConf.regNames r, ?_,
        (holLinv_apply_of_injective hbij.1 r).symm⟩
      rcases hr with h | h | h <;> rw [h]
      · have := hsave 2 (by simp); rwa [show 2 + sp - 2 = sp by omega] at this
      · have := hsave 3 (by simp); rwa [show 3 + sp - 2 = sp + 1 by omega] at this
      · have := hsave 4 (by simp); rwa [show 4 + sp - 2 = sp + 2 by omega] at this
    simp only [s2, StackNames.makeInit, s3, MakeInit.makeInit]
    exact decide_true_of _ key

variable {stackConf dataConf maxHeap sp offset bitmaps code t saveRegs dataSp coracle}
variable {arena : BitVec width → Prop}

theorem labelsOk_tcode_withArena
    (hA : labAssumptionsWithArena stackConf dataConf maxHeap sp offset bitmaps code t saveRegs dataSp coracle arena) :
    CodeInstalled.labelsOk t.code := by
  rw [hA.2.1]
  exact CompileLabPres.stackToLabCompileLabPres
    ⟨goodCode_names hA.2.2.2.2.2.2.2.2.2.2.2.2.1, goodCode_labels hA.2.2.2.2.2.2.2.2.2.2.2.2.1,
      hA.2.2.2.2.2.2.2.2.2.2.2.2.1.1⟩

theorem tcode_eq_withArena
    (hA : labAssumptionsWithArena stackConf dataConf maxHeap sp offset bitmaps code t saveRegs dataSp coracle arena) :
    t.code = (StackNames.compileHOL stackConf.regNames
      (code2 stackConf dataConf maxHeap sp offset code)).map progToSectionHOL := hA.2.1

/-- Renamed `call_args` at the LabSem registers. -/
theorem callArgs_names_withArena
    (hA : labAssumptionsWithArena stackConf dataConf maxHeap sp offset bitmaps code t saveRegs dataSp coracle arena)
    {q : HolProg width} (hq : StackProps.callArgs q 1 2 3 4 0) :
    StackProps.callArgs (StackNames.progCompHOL stackConf.regNames q) t.ptrReg t.lenReg
      t.ptr2Reg t.len2Reg t.linkReg := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h4, h3, h2, h1, h0, -⟩ := hA
  have := StackNames.callArgs_progCompHOL stackConf.regNames q 1 2 3 4 0 hq
  rwa [h1, h2, h3, h4, h0] at this

theorem stateRel_s3_withArena
    (hA : labAssumptionsWithArena stackConf dataConf maxHeap sp offset bitmaps code t saveRegs dataSp coracle arena) :
    StateRel.stateRel (s3 stackConf dataConf maxHeap sp offset code t saveRegs coracle) t := by
  have hok := labelsOk_tcode_withArena hA
  have htc := tcode_eq_withArena hA
  obtain ⟨gd, -, horacle, hfailed, -, -, hlink, -, hio, hcc, hmd, hsmd, hgood, hgoodO, -, -,
    h4, h3, h2, h1, h0, hbij⟩ := id hA
  refine (MakeInit.stateRelMakeInit).mpr ⟨?_, hfailed, ?_, ?_, ?_, ?_, ?_, ?_, hlink, ?_, ?_,
    hio, hcc, hmd, hsmd, gd⟩
  · intro n prog hl
    rw [sptLookup_sptFromAList, FlattenCorrect.sptAListLookup_eq_holAlookup] at hl
    obtain ⟨pc, hinst, hloc⟩ := CodeInstalled.codeInstalledProgToSection _ n prog
      ⟨by rw [← htc]; exact hok, hl⟩
    refine ⟨?_, pc, by rw [htc]; exact hinst, by rw [htc]; exact hloc⟩
    have hm := CodeInstalled.holAlookup_mem _ _ _ hl
    simp only [StackNames.compileHOL, List.mem_map, StackNames.progCompEntryHOL,
      Prod.mk.injEq] at hm
    obtain ⟨⟨n', q⟩, hq, rfl, rfl⟩ := hm
    exact callArgs_names_withArena hA (code2_callArgs hgood q
      (List.mem_map.mpr ⟨_, hq, rfl⟩))
  · rw [horacle]
    funext n
    simp [coracle3, coracle2, coracle1, StackToLab.compileNoStubs, Prod.map, Function.comp_def]
  · intro k
    refine ⟨fun np hnp => ?_, ?_⟩
    · simp only [coracle3, coracle2, coracle1, Function.comp_apply, Prod.map, id,
        StackNames.compileHOL, List.mem_map] at hnp
      obtain ⟨x, ⟨y, ⟨⟨n0, p0⟩, he, rfl⟩, rfl⟩, rfl⟩ := hnp
      obtain ⟨-, hal, hca, -, hlab⟩ := hgoodO k
      have hc0 := hca p0 (List.mem_map.mpr ⟨_, he, rfl⟩)
      obtain ⟨hE, hD⟩ := hlab _ he
      have hap := StackAlloc.stack_alloc_lab_pres n0 (StackAlloc.nextLabHOL p0 2) p0 0
        ⟨hE, hD, Nat.le_refl _⟩
      simp only [StackNames.progCompEntryHOL, StackRemove.progComp, StackAlloc.progComp,
        ← StackNames.stackNamesLabPres, ← StackRemove.Proofs.LabPres.stackRemoveLabPres]
      exact ⟨callArgs_names_withArena hA (StackRemove.Proofs.CallArgs.callArgs_comp _ _ _ _
        (StackAlloc.ConventionSupport.comp_callArgs n0 _ p0 hc0)), hap.1, hap.2.1⟩
    · simpa [coracle3, coracle2, coracle1, StackNames.compileHOL, StackNames.progCompEntryHOL,
        StackRemove.progComp, StackAlloc.progComp, List.map_map, Function.comp_def] using
        (hgoodO k).1
  · rw [← h0, ← h2]; exact fun e => absurd (hbij.1 e) (by decide)
  · rw [← h0, ← h1]; exact fun e => absurd (hbij.1 e) (by decide)
  · rw [← h0, ← h4]; exact fun e => absurd (hbij.1 e) (by decide)
  · rw [← h0, ← h3]; exact fun e => absurd (hbij.1 e) (by decide)
  · intro x
    rw [sptDomain_sptFromAList, htc, CodeInstalled.mapProgToSectionFst]
  · exact (CodeInstalled.labelsOkImp _ hok).1

theorem locToPc_start_withArena
    (hA : labAssumptionsWithArena stackConf dataConf maxHeap sp offset bitmaps code t saveRegs dataSp coracle arena) :
    Flapjack.Compiler.Backend.LabSem.locToPc 0 0 t.code = some t.pc := by
  rw [hA.2.2.2.2.2.2.2.1, tcode_eq_withArena hA]
  simp only [code2, StackRemove.compileHOL, StackRemove.initStubs, StackNames.compileHOL,
    StackNames.progCompEntryHOL, List.cons_append, List.map_cons, CodeInstalled.progToSection_eq]
  rw [Flapjack.Compiler.Backend.LabSem.locToPc.eq_def]
  simp

/-- The stack_names and stack_to_lab stages: the LabSem semantics is the
semantics of `s2` from procedure 0. -/
theorem stageLab_withArena
    (hA : labAssumptionsWithArena stackConf dataConf maxHeap sp offset bitmaps code t saveRegs dataSp coracle arena) :
    StackSemEvaluate.semantics 0 (s2 stackConf dataConf maxHeap sp offset code t saveRegs coracle) ≠
        .fail →
      Flapjack.Compiler.Backend.LabSem.semantics t =
        StackSemEvaluate.semantics 0
          (s2 stackConf dataConf maxHeap sp offset code t saveRegs coracle) := by
  intro hne
  have hnames : StackSemEvaluate.semantics 0 (s3 stackConf dataConf maxHeap sp offset code t
      saveRegs coracle) =
      StackSemEvaluate.semantics 0
        (s2 stackConf dataConf maxHeap sp offset code t saveRegs coracle) :=
    StackNames.makeInitSemantics ⟨by simp [s3, MakeInit.makeInit], by simp [s3, MakeInit.makeInit],
      by simp [s3, MakeInit.makeInit], hA.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2,
      code2_nodup hA.2.2.2.2.2.2.2.2.2.2.2.2.1, rfl, rfl⟩
  rw [← hnames] at hne ⊢
  exact MakeInit.makeInitSemantics ⟨MakeInit.haltAssumLemma, stateRel_s3_withArena hA, locToPc_start_withArena hA, hne⟩

/-- Arena-aware Lab assumptions discharge both bundles required for actual
StackRemove initialization at the unchanged `s2` state. -/
theorem lab_init_withArena
    (arena : BitVec width → Prop)
    (hA : labAssumptionsWithArena stackConf dataConf maxHeap sp offset bitmaps code t
      saveRegs dataSp coracle arena) :
    ∃ s1, makeInitOptWithArena (StackToLab.isGenGc dataConf.gcKind) maxHeap bitmaps dataSp
        (coracle1 coracle) stackConf.jump offset sp (sptFromAList (code1 dataConf code))
        (s2 stackConf dataConf maxHeap sp offset code t saveRegs coracle) arena = some s1 ∧
      (StackSemEvaluate.semantics BvlToBvi.initGlobalsLocation s1 ≠ HolBehaviour.fail →
        StackSemEvaluate.semantics 0
          (s2 stackConf dataConf maxHeap sp offset code t saveRegs coracle) =
            StackSemEvaluate.semantics BvlToBvi.initGlobalsLocation s1) := by
  apply makeInitSemanticsWithArena
  refine ⟨dischargeThese_s2_withArena stackConf dataConf maxHeap sp offset bitmaps code t saveRegs dataSp coracle arena hA, ?_⟩
  obtain ⟨gd, _, _, _, hm, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hb⟩ := hA
  exact propagateThese_s2_withArena stackConf dataConf maxHeap sp offset bitmaps code t saveRegs dataSp coracle arena gd hm hb

/-- The unchanged compiled Lab entry has the non-failing observable semantics
of the arena-aware initialized StackRemove source. -/
theorem lab_init_semantics_withArena
    (hA : labAssumptionsWithArena stackConf dataConf maxHeap sp offset bitmaps code t
      saveRegs dataSp coracle arena) :
    ∃ s1, makeInitOptWithArena (StackToLab.isGenGc dataConf.gcKind) maxHeap bitmaps dataSp
        (coracle1 coracle) stackConf.jump offset sp (sptFromAList (code1 dataConf code))
        (s2 stackConf dataConf maxHeap sp offset code t saveRegs coracle) arena = some s1 ∧
      (StackSemEvaluate.semantics BvlToBvi.initGlobalsLocation s1 ≠ HolBehaviour.fail →
        LabSem.semantics t = StackSemEvaluate.semantics BvlToBvi.initGlobalsLocation s1) := by
  obtain ⟨s1, opt, sem⟩ := lab_init_withArena arena hA
  refine ⟨s1, opt, fun hn => ?_⟩
  have eqSem := sem hn
  exact (stageLab_withArena hA (by rw [eqSem]; exact hn)).trans eqSem

#print axioms stageLab_withArena
#print axioms lab_init_semantics_withArena

#print axioms lab_init_withArena

#print axioms dischargeThese_s2_withArena
#print axioms propagateThese_s2_withArena
end InitE.Op5
