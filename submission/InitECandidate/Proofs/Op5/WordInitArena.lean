import InitECandidate.Proofs.Op5.AssemblyInitArena
import Flapjack.Pancake.Proofs.PanToTarget.AssemblyInitMemory

namespace InitE.Op5
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInitSemantics
open Flapjack.Compiler.Backend.StackRemove Flapjack.Compiler.Backend.StackRemove.Proofs

section
variable {width : Nat} [NeZero width] {C F : Type}
  {stackConf : StackToLab.Config} {dataConf : DataToWord.Config} {maxHeap sp : Nat}
  {offset : BitVec width × BitVec width} {bitmaps : List (BitVec width)}
  {code : List (Nat × HolProg width)} {t : Flapjack.Compiler.Backend.LabSem.State width C F}
  {saveRegs : Nat → Bool} {dataSp : Nat}
  {coracle : Nat → C × List (Nat × HolProg width) × List (BitVec width)}
  {sst x t' : StackSemStateFiniteExact width C F}
  {arena : BitVec width → Prop}

/-- The stack state of a successful `full_make_init` is `stack_alloc$make_init` of its
`SOME` component, which satisfies `init_prop` (HOL lines 1567-1585, 1756-1797). -/
theorem fullMakeInitStateWithArena
    (hfmi : fullMakeInitWithArena stackConf dataConf maxHeap sp offset
      bitmaps code t saveRegs dataSp coracle arena = (sst, some x))
    (hev : StackSemEvaluate.evaluate (initCode (StackToLab.isGenGc dataConf.gcKind) maxHeap sp,
      s2 stackConf dataConf maxHeap sp offset code t saveRegs coracle) = (none, t')) :
    sst = StackAlloc.makeInit dataConf (sptFromAList code) coracle x ∧
      initPropWithArena (StackToLab.isGenGc dataConf.gcKind) maxHeap dataSp
        (InitLimits.getStackHeapLimit maxHeap
          (InitLimits.readPointers (s2 stackConf dataConf maxHeap sp offset code t saveRegs
            coracle))) x arena := by
  unfold fullMakeInitWithArena at hfmi
  simp only [Prod.mk.injEq] at hfmi
  obtain ⟨hs, hopt⟩ := hfmi
  refine ⟨?_, ?_⟩
  · rw [← hs]
    simp only [makeInitAnyWithArena]
    rw [hopt]
  · unfold makeInitOptWithArena at hopt
    rw [hev] at hopt
    simp only at hopt
    split at hopt
    · rename_i hp
      rw [← Option.some.inj hopt]
      exact hp
    · cases hopt

/-- The `init_code_pre` size facts of the lab state's initial `len`/`len2` registers,
from `memory_assumption` (HOL lines 1883-1906 and 2048-2060). -/
theorem initPointerBoundsWithArena
    (hA : labAssumptionsWithArena stackConf dataConf maxHeap sp offset bitmaps code t saveRegs dataSp
      coracle arena) :
    ∃ w2 w4 : BitVec width, t.regs t.lenReg = .word w2 ∧ t.regs t.len2Reg = .word w4 ∧
      w2.toNat ≤ w4.toNat ∧ (1024 * bytesInWord width).toNat ≤ (w4 - w2).toNat := by
  have hp := propagateThese_s2_withArena stackConf dataConf maxHeap sp offset bitmaps code t saveRegs dataSp coracle arena hA.1
    hA.2.2.2.2.1 hA.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h4, -, h2, -, -, hbij⟩ := id hA
  obtain ⟨-, ptr2, -, ptr4, -, r2, -, r4, -, -, -, -, -, -, le, -, -, -, big, -⟩ := hp
  rw [s2_regs_lookup hbij (.inl rfl), h2] at r2
  rw [s2_regs_lookup hbij (.inr (.inr rfl)), h4] at r4
  exact ⟨ptr2, ptr4, Option.some.inj r2, Option.some.inj r4, BitVec.le_def.mp le,
    BitVec.le_def.mp big⟩

open Classical in
/-- The memory domain of the word initial state (HOL lines 1916-2102, "memory domain
done" and the heap-length equation at 2034-2041): for the lab state's initial
`len`/`ptr2`/`len2` registers `w2`/`w3`/`w4` under the pointer bounds of the top
theorem's hypotheses, it is the `(w3 - w2) DIV (dimindex DIV 8)` heap words from `w2`. -/
theorem wordInitMdomainWithArena {k : Nat} {ac : AsmConfigExact width}
    {wcode : Spt (Nat × WordLangProgHOL (BitVec width))}
    {worac : Nat → (Nat × C) × List (Nat × Nat × WordLangProgHOL (BitVec width))}
    (w2 w3 w4 : BitVec width)
    (hA : labAssumptionsWithArena stackConf dataConf maxHeap sp offset bitmaps code t saveRegs dataSp
      coracle arena)
    (hfmi : fullMakeInitWithArena stackConf dataConf maxHeap sp offset
      bitmaps code t saveRegs dataSp coracle arena = (sst, some x))
    (h2 : t.regs t.lenReg = .word w2) (h3 : t.regs t.ptr2Reg = .word w3)
    (h4 : t.regs t.len2Reg = .word w4)
    (hlo : w2 + BitVec.ofNat width maxStackAlloc * bytesInWord width ≤ w3)
    (hhi : w3 ≤ w4 - BitVec.ofNat width maxStackAlloc * bytesInWord width)
    (hheap : (-1 * w2 + w3).toNat ≤ maxHeap * (bytesInWord width).toNat)
    (hheapLt : (bytesInWord width).toNat * maxHeap < 2 ^ width)
    (halign : holAligned (wordShiftAmount width + 1) (w3 + -1 * w2) = true) :
    ∀ a, (WordToStack.Native.Initialization.makeInit ac k sst wcode worac).mdomain a =
      decide (addresses w2 ((w3 + -1 * w2).toNat / (width / 8)) a ∨ arena a) := by
  obtain ⟨t', v2, v3, v4, hev, g2, g3, g4, -, -, -, tsp2, -, tsp1, -⟩ :=
    initCodeRunWithArena hA
  rw [h2] at g2; rw [h3] at g3; rw [h4] at g4
  cases g2; cases g3; cases g4
  obtain ⟨u2, u4, f2, f4, hle, hbig⟩ := initPointerBoundsWithArena hA
  rw [h2] at f2; rw [h4] at f4
  cases f2; cases f4
  obtain ⟨hx, -⟩ := fullMakeInitReduceWithArena hfmi hev
  obtain ⟨hs, -⟩ := fullMakeInitStateWithArena hfmi hev
  have hgood : goodDimindex width := hA.1
  intro a
  simp only [WordToStack.Native.Initialization.makeInit, hs, StackAlloc.makeInit, hx,
    initReduceWithArena, withArena, InitReduce.initReduce]
  rw [holFapply_of_lookup tsp2, holFapply_of_lookup (tsp1 ⟨hlo, hhi, hheap, hheapLt⟩),
    Compiler.Backend.DataToWord.Proofs.Gc.lsrLsl _ _ halign]
  rw [Bool.decide_or]
  congr 1
  congr 2
  simp only [wordSemTheWord]
  have hneg : -1 * w2 = -w2 := by
    rw [BitVec.neg_mul]; exact congrArg _ (BitVec.one_mul w2)
  have hsimp : w3 + -w2 + w2 + bytesInWord width * BitVec.ofNat width storeList.length - w2 =
      w3 + -w2 + bytesInWord width * BitVec.ofNat width storeList.length := by
    rw [BitVec.add_assoc (w3 + -w2), BitVec.add_comm w2, ← BitVec.add_assoc,
      BitVec.add_sub_cancel]
  rw [hneg, hsimp]
  have hsl : storeList.length = 48 := by decide
  rw [hsl]
  clear hs hx hev tsp2 tsp1 halign hheap hheapLt hsimp hneg h2 h3 h4 hfmi hA
  rw [BitVec.le_def] at hlo hhi
  rcases hgood with h | h <;> subst h <;>
    simp [bytesInWord, maxStackAlloc, BitVec.toNat_add, BitVec.toNat_sub,
      BitVec.toNat_neg] at hlo hhi hle hbig ⊢ <;> omega


theorem wordInitStoreWithArena {k : Nat} {ac : AsmConfigExact width}
    {wcode : Spt (Nat × WordLangProgHOL (BitVec width))}
    {worac : Nat → (Nat × C) × List (Nat × Nat × WordLangProgHOL (BitVec width))}
    (hA : labAssumptionsWithArena stackConf dataConf maxHeap sp offset bitmaps code t saveRegs dataSp
      coracle arena)
    (hfmi : fullMakeInitWithArena stackConf dataConf maxHeap sp offset
      bitmaps code t saveRegs dataSp coracle arena = (sst, some x)) :
    ∃ w2 : BitVec width, t.regs t.lenReg = .word w2 ∧
      (WordToStack.Native.Initialization.makeInit ac k sst wcode worac).store.lookup
          .currHeap = some (.word w2) ∧
      (WordToStack.Native.Initialization.makeInit ac k sst wcode worac).store.lookup
          .heapLength =
        some (.word (BitVec.ofNat width
          (InitLimits.getStackHeapLimit maxHeap
            (InitLimits.readPointers (s2 stackConf dataConf maxHeap sp offset code t saveRegs
              coracle))).2 * bytesInWord width)) := by
  obtain ⟨t', w2, -, -, hev, g2, -, -, -, -, -, tsp2, -, -⟩ := initCodeRunWithArena hA
  obtain ⟨hx, -⟩ := fullMakeInitReduceWithArena hfmi hev
  obtain ⟨hs, hprop⟩ := fullMakeInitStateWithArena hfmi hev
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hshl, -⟩ := hprop
  refine ⟨w2, g2, ?_, ?_⟩
  · simp only [WordToStack.Native.Initialization.makeInit, HolFiniteMapExact.lookup_eraseEq,
      hs, StackAlloc.makeInit]
    simp only [FDOMSUB_HOL, reduceCtorEq, if_false]
    rw [hx]
    simp [initReduceWithArena, withArena, InitReduce.initReduce, HolFiniteMapExact.lookup_updateListEq, storeList, storeInit,
      FUPDATE_LIST_HOL, FUPDATE_HOL, StackSemRegisterTransfers.storeOfSyntax,
      holFapply_of_lookup tsp2]
  · simp only [WordToStack.Native.Initialization.makeInit, HolFiniteMapExact.lookup_eraseEq,
      hs, StackAlloc.makeInit]
    simp only [FDOMSUB_HOL, reduceCtorEq, if_false]
    exact hshl.1

theorem wordInitMemoryWithArena {k : Nat} {ac : AsmConfigExact width}
    {wcode : Spt (Nat × WordLangProgHOL (BitVec width))}
    {worac : Nat → (Nat × C) × List (Nat × Nat × WordLangProgHOL (BitVec width))}
    (hA : labAssumptionsWithArena stackConf dataConf maxHeap sp offset bitmaps code t saveRegs dataSp
      coracle arena)
    (hfmi : fullMakeInitWithArena stackConf dataConf maxHeap sp offset
      bitmaps code t saveRegs dataSp coracle arena = (sst, some x)) :
    (WordToStack.Native.Initialization.makeInit ac k sst wcode worac).ffi = t.ffi ∧
      (WordToStack.Native.Initialization.makeInit ac k sst wcode worac).be = t.be ∧
      (WordToStack.Native.Initialization.makeInit ac k sst wcode worac).shMdomain =
        t.sharedMemDomain ∧
      ∀ a, (WordToStack.Native.Initialization.makeInit ac k sst wcode worac).mdomain a = true →
        (WordToStack.Native.Initialization.makeInit ac k sst wcode worac).memory a =
          t.memory a := by
  obtain ⟨t', -, -, -, hev, -, -, -, -, -, -, -, -, -, -, hffi, -, hsmd, hmem⟩ :=
    initCodeRunWithArena hA
  obtain ⟨hx, -⟩ := fullMakeInitReduceWithArena hfmi hev
  obtain ⟨hs, -⟩ := fullMakeInitStateWithArena hfmi hev
  obtain ⟨-, -, -, -, -, hm2, -, -, hf2⟩ := s2_fields (stackConf := stackConf)
    (dataConf := dataConf) (maxHeap := maxHeap) (sp := sp) (offset := offset) (code := code)
    (t := t) (saveRegs := saveRegs) (coracle := coracle)
  have hsh : (s2 stackConf dataConf maxHeap sp offset code t saveRegs coracle).shMdomain =
      t.sharedMemDomain := by
    simp [s2, s3, StackNames.makeInit, StackToLab.Proofs.MakeInit.makeInit]
  have hsbe : sst.be = t.be := by
    rw [hs, hx]
    change t'.be = t.be
    have hc := (StackProps.evaluateConsts _ _ _ _ hev).2.2.2.1
    exact hc.trans (by simp [s2, s3, StackNames.makeInit, StackToLab.Proofs.MakeInit.makeInit])
  refine ⟨?_, by simp only [WordToStack.Native.Initialization.makeInit]; exact hsbe, ?_, ?_⟩
  all_goals subst hx
  all_goals simp only [WordToStack.Native.Initialization.makeInit, hs, StackAlloc.makeInit,
    initReduceWithArena, withArena, InitReduce.initReduce]
  · rw [hffi, hf2]
  · rw [← hsmd, hsh]
  intro a ha
  have hin : SetSep.fun2Set ((s2 stackConf dataConf maxHeap sp offset code t saveRegs
      coracle).memory, fun a => (initReduceWithArena arena (StackToLab.isGenGc dataConf.gcKind)
        stackConf.jump offset sp (sptFromAList (code1 dataConf code)) bitmaps dataSp
        (coracle1 coracle) t').mdomain a = true) (a, t.memory a) :=
    ⟨a, by simpa [initReduceWithArena, withArena, InitReduce.initReduce] using ha, by rw [hm2]⟩
  rw [hmem] at hin
  obtain ⟨a', -, he⟩ := hin
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, he⟩ := he
  exact he.symm

end
#print axioms wordInitStoreWithArena
#print axioms wordInitMemoryWithArena
#print axioms wordInitMdomainWithArena
end InitE.Op5
