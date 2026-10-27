import InitECandidate.Proofs.Op5.FullInitArena
import Flapjack.Pancake.Proofs.PanToTarget.AssemblyInitCode

namespace InitE.Op5
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInitSemantics
open Flapjack.Compiler.Backend.StackRemove Flapjack.Compiler.Backend.StackRemove.Proofs

theorem initCodeRunWithArena {width : Nat} [NeZero width] {C F : Type}
    {stackConf : StackToLab.Config} {dataConf : DataToWord.Config} {maxHeap sp : Nat}
    {offset : BitVec width × BitVec width} {bitmaps : List (BitVec width)}
    {code : List (Nat × HolProg width)} {t : Flapjack.Compiler.Backend.LabSem.State width C F}
    {saveRegs : Nat → Bool} {dataSp : Nat}
    {coracle : Nat → C × List (Nat × HolProg width) × List (BitVec width)}
    {arena : BitVec width → Prop}
    (hA : labAssumptionsWithArena stackConf dataConf maxHeap sp offset bitmaps code t saveRegs dataSp
      coracle arena) :
    ∃ (t' : StackSemStateFiniteExact width C F) (w2 w3 w4 : BitVec width),
      StackSemEvaluate.evaluate (initCode (StackToLab.isGenGc dataConf.gcKind) maxHeap sp,
          s2 stackConf dataConf maxHeap sp offset code t saveRegs coracle) = (none, t') ∧
      t.regs t.lenReg = .word w2 ∧ t.regs t.ptr2Reg = .word w3 ∧
      t.regs t.len2Reg = .word w4 ∧
      holByteAligned w2 = true ∧ holByteAligned w4 = true ∧ w2 < w4 ∧
      t'.regs.lookup (sp + 2) = some (.word w2) ∧
      t'.regs.lookup sp = some (.word (w4 - bytesInWord width)) ∧
      (w2 + BitVec.ofNat width maxStackAlloc * bytesInWord width ≤ w3 ∧
        w3 ≤ w4 - BitVec.ofNat width maxStackAlloc * bytesInWord width ∧
        (-1 * w2 + w3).toNat ≤ maxHeap * (bytesInWord width).toNat ∧
        (bytesInWord width).toNat * maxHeap < 2 ^ width →
        t'.regs.lookup (sp + 1) =
          some (.word ((((w3 + -1 * w2) >>> (wordShiftAmount width + 1)) <<<
            (wordShiftAmount width + 1)) + w2 +
            bytesInWord width * BitVec.ofNat width storeList.length))) ∧
      stateRelHOL stackConf.jump offset sp
        (initReduceWithArena arena (StackToLab.isGenGc dataConf.gcKind) stackConf.jump offset sp
          (sptFromAList (code1 dataConf code)) bitmaps dataSp (coracle1 coracle) t') t' ∧
      t'.ffi = (s2 stackConf dataConf maxHeap sp offset code t saveRegs coracle).ffi ∧
      (s2 stackConf dataConf maxHeap sp offset code t saveRegs coracle).mdomain = t'.mdomain ∧
      (s2 stackConf dataConf maxHeap sp offset code t saveRegs coracle).shMdomain =
        t'.shMdomain ∧
      (let t0 := initReduceWithArena arena (StackToLab.isGenGc dataConf.gcKind) stackConf.jump
          offset sp (sptFromAList (code1 dataConf code)) bitmaps dataSp (coracle1 coracle) t'
       SetSep.fun2Set ((s2 stackConf dataConf maxHeap sp offset code t saveRegs coracle).memory,
           fun a => t0.mdomain a = true) =
         SetSep.fun2Set (t'.memory, fun a => t0.mdomain a = true)) := by
  have hd := dischargeThese_s2_withArena _ _ _ _ _ _ _ _ _ _ _ arena hA
  have hp := propagateThese_s2_withArena stackConf dataConf maxHeap sp offset bitmaps code t saveRegs dataSp coracle arena hA.1
    hA.2.2.2.2.1 hA.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h4, h3, h2, -, -, hbij⟩ := id hA
  obtain ⟨every, oracleBound, oracleEq, codeEq, k8, entry1, save, noStack, noStore, noAlloc,
    maxOk⟩ := hd
  obtain ⟨good, ptr2, ptr3, ptr4, bp, r2, r3, r4, m0, m1, m2, m3, m4, cbEmpty, le, al2, al4,
    albp, big, heap⟩ := hp
  have sub : -1 * ptr2 + ptr4 = ptr4 - ptr2 := by
    rw [BitVec.neg_mul]; simp [BitVec.sub_eq_add_neg, BitVec.add_comm]
  rw [sub] at heap
  have main := initCodeThmWithArena (StackToLab.isGenGc dataConf.gcKind) maxHeap sp
    bitmaps dataSp (s2 stackConf dataConf maxHeap sp offset code t saveRegs coracle) arena
    stackConf.jump offset (sptFromAList (code1 dataConf code)) (coracle1 coracle)
    ⟨⟨ptr2, ptr3, ptr4, bp, good, k8, entry1, save, noStack, noStore, noAlloc, r2, r3, r4,
      m0, m1, m2, m3, m4, le, big, al2, al4, albp, cbEmpty, heap⟩,
     InitCodeRelation.impCodeRel stackConf.jump offset (StackToLab.isGenGc dataConf.gcKind)
       maxHeap sp BvlToBvi.initGlobalsLocation (code1 dataConf code) _ ⟨every, codeEq⟩,
     oracleEq, oracleBound,
     by rw [codeEq, sptLookup_sptFromAList]
        simp [compileHOL, initStubs, sptAListLookup, stackErrLab],
     maxOk⟩
  revert main
  rcases hev : StackSemEvaluate.evaluate (initCode (StackToLab.isGenGc dataConf.gcKind) maxHeap
      sp, s2 stackConf dataConf maxHeap sp offset code t saveRegs coracle) with ⟨_ | _, t'⟩
  · rintro ⟨⟨w2, w3, w4, s2r2, a2, t2, s2r4, a4, lt, tsp, bound, s2r3⟩, hrel, hffi, -, hmd,
      hsmd, hmem⟩
    have lk : ∀ i, (i = 2 ∨ i = 3 ∨ i = 4) →
        (s2 stackConf dataConf maxHeap sp offset code t saveRegs coracle).regs.lookup i =
          some (t.regs (StackNames.findNameSpt stackConf.regNames i)) :=
      fun i hi => s2_regs_lookup hbij hi
    rw [lk 2 (.inl rfl), h2] at s2r2
    rw [lk 3 (.inr (.inl rfl)), h3] at s2r3
    rw [lk 4 (.inr (.inr rfl)), h4] at s2r4
    exact ⟨t', w2, w3, w4, rfl, Option.some.inj s2r2, Option.some.inj s2r3,
      Option.some.inj s2r4, a2, a4, lt, t2, tsp, bound, hrel, hffi, hmd, hsmd, hmem⟩
  · simp

/-- A successful `full_make_init` (`opt = SOME x`, as `full_make_init_semantics`
gives) is `init_reduce` of the `init_code` result state, and the stack state it
returns has `x`'s stack (HOL lines 1756-1797 and 1924-1929). -/
theorem fullMakeInitReduceWithArena {width : Nat} [NeZero width] {C F : Type}
    {stackConf : StackToLab.Config} {dataConf : DataToWord.Config} {maxHeap sp : Nat}
    {offset : BitVec width × BitVec width} {bitmaps : List (BitVec width)}
    {code : List (Nat × HolProg width)} {t : Flapjack.Compiler.Backend.LabSem.State width C F}
    {saveRegs : Nat → Bool} {dataSp : Nat}
    {coracle : Nat → C × List (Nat × HolProg width) × List (BitVec width)}
    {sst x t' : StackSemStateFiniteExact width C F} {arena : BitVec width → Prop}
    (hfmi : fullMakeInitWithArena stackConf dataConf maxHeap sp offset bitmaps code t
      saveRegs dataSp coracle arena = (sst, some x))
    (hev : StackSemEvaluate.evaluate (initCode (StackToLab.isGenGc dataConf.gcKind) maxHeap sp,
      s2 stackConf dataConf maxHeap sp offset code t saveRegs coracle) = (none, t')) :
    x = initReduceWithArena arena (StackToLab.isGenGc dataConf.gcKind) stackConf.jump offset sp
        (sptFromAList (code1 dataConf code)) bitmaps dataSp (coracle1 coracle) t' ∧
      sst.stack = x.stack := by
  unfold fullMakeInitWithArena at hfmi
  simp only [Prod.mk.injEq] at hfmi
  obtain ⟨hs, hopt⟩ := hfmi
  have hx : x = initReduceWithArena arena (StackToLab.isGenGc dataConf.gcKind) stackConf.jump
      offset sp (sptFromAList (code1 dataConf code)) bitmaps dataSp (coracle1 coracle) t' := by
    unfold makeInitOptWithArena at hopt
    rw [hev] at hopt
    simp only at hopt
    split at hopt
    · exact (Option.some.inj hopt).symm
    · cases hopt
  refine ⟨hx, ?_⟩
  rw [← hs]
  simp only [StackAlloc.makeInit, makeInitAnyWithArena]
  unfold makeInitOptWithArena at hopt ⊢
  rw [hopt]


#print axioms initCodeRunWithArena
#print axioms fullMakeInitReduceWithArena
end InitE.Op5
