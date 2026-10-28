import InitECandidate.Proofs.Op5.LabInitArena

namespace InitE.Op5
open Flapjack Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Backend.StackRemove.Proofs
open Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInitSemantics

theorem makeInitOptWithArena_eq_some {width : Nat} [NeZero width] {C F : Type}
    {generateGc : Bool} {maxHeap : Nat} {bitmaps : List (BitVec width)} {dataSpace : Nat}
    {oracle : Nat → C × List (Nat × HolProg width) × List (BitVec width)}
    {jump : Bool} {bounds : BitVec width × BitVec width} {pointer : Nat}
    {arena : BitVec width → Prop}
    {code : Spt (HolProg width)} {s t : StackSemStateFiniteExact width C F}
    (h : makeInitOptWithArena generateGc maxHeap bitmaps dataSpace oracle jump bounds pointer code s arena =
      some t) :
    ∃ post, t = initReduceWithArena arena generateGc jump bounds pointer code bitmaps dataSpace
        oracle post ∧
      initPropWithArena generateGc maxHeap dataSpace
        (InitLimits.getStackHeapLimit maxHeap (InitLimits.readPointers s)) t arena := by
  unfold makeInitOptWithArena at h
  split at h
  · cases h
  · split at h
    · cases h
      exact ⟨_, rfl, by assumption⟩
    · cases h

variable {width : Nat} [NeZero width] {C F : Type}
  (stackConf : StackToLab.Config) (dataConf : DataToWord.Config) (maxHeap sp : Nat)
  (offset : BitVec width × BitVec width) (bitmaps : List (BitVec width))
  (code : List (Nat × HolProg width)) (t : Flapjack.Compiler.Backend.LabSem.State width C F)
  (saveRegs : Nat → Bool) (dataSp : Nat)
  (coracle : Nat → C × List (Nat × HolProg width) × List (BitVec width))


/-- The full pipeline uses the unchanged Lab/Names/Alloc constructors and
arena-aware optional and total StackRemove initialization. -/
noncomputable def fullMakeInitWithArena (arena : BitVec width → Prop) :
    StackSemStateFiniteExact width C F × Option (StackSemStateFiniteExact width C F) :=
  (StackAlloc.makeInit dataConf (sptFromAList code) coracle
        (makeInitAnyWithArena (StackToLab.isGenGc dataConf.gcKind) maxHeap
          bitmaps dataSp (coracle1 coracle) stackConf.jump offset sp
          (sptFromAList (code1 dataConf code))
          (s2 stackConf dataConf maxHeap sp offset code t saveRegs coracle) arena),
       makeInitOptWithArena (StackToLab.isGenGc dataConf.gcKind) maxHeap
          bitmaps dataSp (coracle1 coracle) stackConf.jump offset sp
          (sptFromAList (code1 dataConf code))
          (s2 stackConf dataConf maxHeap sp offset code t saveRegs coracle) arena)

section Stage
variable {width : Nat} [NeZero width] {C F : Type}
  {stackConf : StackToLab.Config} {dataConf : DataToWord.Config} {maxHeap sp : Nat}
  {offset : BitVec width × BitVec width} {bitmaps : List (BitVec width)}
  {code : List (Nat × HolProg width)} {t : Flapjack.Compiler.Backend.LabSem.State width C F}
  {saveRegs : Nat → Bool} {dataSp : Nat}
  {coracle : Nat → C × List (Nat × HolProg width) × List (BitVec width)}

variable {arena : BitVec width → Prop}

theorem fullMakeInitWithArena_semantics {s : StackSemStateFiniteExact width C F}
    {opt : Option (StackSemStateFiniteExact width C F)}
    (hfm : fullMakeInitWithArena stackConf dataConf maxHeap sp offset bitmaps code t saveRegs dataSp
      coracle arena = (s, opt))
    (hA : labAssumptionsWithArena stackConf dataConf maxHeap sp offset bitmaps code t saveRegs dataSp coracle arena) :
    opt ≠ none ∧
      (StackSemEvaluate.semantics BvlToBvi.initGlobalsLocation s ≠ .fail →
        Flapjack.Compiler.Backend.LabSem.semantics t =
          StackSemEvaluate.semantics BvlToBvi.initGlobalsLocation s) := by
  unfold fullMakeInitWithArena at hfm
  simp only [Prod.mk.injEq] at hfm
  obtain ⟨rfl, rfl⟩ := hfm
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hgood, hgoodO, -, -, -, -, -, -, -, -⟩ := id hA
  obtain ⟨s1, hopt, hsem⟩ := lab_init_semantics_withArena hA
  refine ⟨by rw [hopt]; simp, fun hS => ?_⟩
  have hs1 : makeInitAnyWithArena (StackToLab.isGenGc dataConf.gcKind) maxHeap
      bitmaps dataSp (coracle1 coracle) stackConf.jump offset sp
      (sptFromAList (code1 dataConf code))
      (s2 stackConf dataConf maxHeap sp offset code t saveRegs coracle) arena = s1 := by
    unfold makeInitAnyWithArena
    rw [hopt]
  rw [hs1] at hS ⊢
  obtain ⟨post, hpost, hprop⟩ := makeInitOptWithArena_eq_some hopt
  -- rawcall
  have hF := StackRawCall.CompileSemantics.compileSemantics code
    (StackAlloc.makeInit dataConf (sptFromAList code) coracle s1) BvlToBvi.initGlobalsLocation
    hgood.1 (by simp [StackAlloc.makeInit]) rfl hS
  have hm : { StackAlloc.makeInit dataConf (sptFromAList code) coracle s1 with
      code := sptFromAList (StackRawCall.compile code) } =
      StackAlloc.makeInit dataConf (sptFromAList (StackRawCall.compile code)) coracle s1 := by
    simp [StackAlloc.makeInit]
  rw [hm] at hF
  -- stack_alloc
  have hu : s1.useStack = true := by rw [hpost]; rfl
  have hus : s1.useStore = true := by rw [hpost]; rfl
  have hua : s1.useAlloc = false := by rw [hpost]; rfl
  have hcd : s1.code = sptFromAList (code1 dataConf code) := by rw [hpost]; rfl
  have hco : s1.compileOracle = coracle1 coracle := by rw [hpost]; rfl
  have hE := StackAlloc.make_init_semantics (code := StackRawCall.compile code) (oracle := coracle)
    (s := s1) (c := dataConf) (start := BvlToBvi.initGlobalsLocation) ⟨?_, ?_, hu, hus,
      by simp [hua], hcd, hco, ?_, ?_, by rw [StackRawCall.mapFstCompile]; exact hgood.1,
      by rw [hF]; exact hS⟩
  · have h1 := hE.trans hF
    have hS1 : StackSemEvaluate.semantics BvlToBvi.initGlobalsLocation s1 ≠ .fail := by
      rw [h1]; exact hS
    exact (hsem hS1).trans h1
  · intro k prog hk
    obtain ⟨⟨n0, p0⟩, hm0, he⟩ := List.mem_map.mp (sptAListLookup_mem hk)
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    obtain ⟨hst, hal⟩ := hgood.2.1 _ hm0
    refine ⟨by simp only [stackNumStubs, gcStubLocation] at hst ⊢; omega,
      (StackRawCall.callArgComp _ _).2.mpr hal⟩
  · intro i k q hq
    obtain ⟨hst, hal⟩ := (hgoodO i).2.1 _ hq
    exact ⟨by simp only [stackNumStubs, gcStubLocation] at hst ⊢; omega, hal⟩
  · subst hpost
    rcases hprop with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      hdb, _, _, _, hbl, _⟩
    simp only [initReduceWithArena, withArena, StackRemove.Proofs.InitReduce.initReduce] at hbl hdb ⊢
    simp only [List.length_nil, Nat.add_zero]
    omega
  · subst hpost
    rcases hprop with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, _, _, _, _, _, _, hsb, _⟩
    exact hsb

end Stage

#print axioms fullMakeInitWithArena_semantics
end InitE.Op5
