import InitECandidate.Proofs.Op5.EncodingInitArena
import Flapjack.Pancake.Proofs.PanToTarget.AssemblyWordToStack

namespace InitE.Op5
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.Asm
open Flapjack.Pancake.Proofs.PanToTarget

theorem fullMakeInitWithArena_bitmaps_code {width : Nat} [NeZero width] {C F : Type}
    (stackConf : StackToLab.Config) (dataConf : DataToWord.Config) (maxHeap sp : Nat)
    (offset : BitVec width × BitVec width) (bitmaps : List (BitVec width))
    (code : List (Nat × StackLang.HolProg width)) (s4 : LabSem.State width C F)
    (saveRegs : Nat → Bool) (dataSp : Nat)
    (coracle : Nat → C × List (Nat × StackLang.HolProg width) × List (BitVec width))
    (s x : StackSemStateFiniteExact width C F)
    (arena : BitVec width → Prop)
    (h : fullMakeInitWithArena stackConf dataConf maxHeap sp offset bitmaps code s4
      saveRegs dataSp coracle arena = (s, some x)) :
    s.bitmaps = bitmaps ∧ s.code = sptFromAList code := by
  unfold fullMakeInitWithArena at h
  simp only [Prod.mk.injEq] at h
  obtain ⟨rfl, hopt⟩ := h
  constructor
  · simp only [StackAlloc.makeInit, makeInitAnyWithArena, hopt]
    unfold makeInitOptWithArena at hopt
    split at hopt
    · cases hopt
    · split at hopt
      · cases hopt; rfl
      · cases hopt
  · rfl

/-- `init_state_ok` for the stack state of `full_make_init` with the proof's empty
word oracle (HOL proof lines 1624-1647, via `IMP_init_state_ok`). -/
theorem initStateOkWithArena {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (wprog : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (bitmaps : List (BitVec width)) (c'' : WordToStack.Native.Config) (fs : List Nat)
    (p : List (Nat × StackLang.HolProg width)) (cfg : C)
    (scc : StackToLab.Config) (dc : DataToWord.Config) (maxHeap stk : Nat)
    (stoff : BitVec width × BitVec width) (labSt : LabSem.State width C F)
    (saveRegs : Nat → Bool) (dataSp : Nat) (sst xxx : StackSemStateFiniteExact width C F)
    (good : goodDimindex width) (hregs : ac.avoidRegs.length + 13 ≤ ac.regCount)
    (hwts : WordToStack.Native.compileNative ac false wprog = (bitmaps, c'', fs, p))
    (arena : BitVec width → Prop)
    (hfmi : fullMakeInitWithArena scc dc maxHeap stk stoff bitmaps p labSt
      saveRegs dataSp (fun _ => (cfg, [], [])) arena = (sst, some xxx)) :
    WordToStackProofs.InitializationStateRel.initStateOk ac
      (ac.regCount - (ac.avoidRegs.length + 5)) sst
      (fun _ => ((bitmaps.length, cfg), ([] : List (Nat × Nat × WordLangProgHOL (BitVec width))))) := by
  have hbm := (WordToStack.Native.compileWordToStackBitmaps ac wprog bitmaps c'' (fs, p) hwts).1
  obtain ⟨t, rfl⟩ : ∃ t, bitmaps = 4 :: t := by
    cases bitmaps with
    | nil => exact absurd hbm id
    | cons h t => exact ⟨t, by simp_all⟩
  apply impInitStateOkWithArena (labSt := labSt) (saveRegs := saveRegs)
    (dataSp := dataSp) (xxx := xxx) (scc := scc) (dc := dc) (maxHeap := maxHeap) (stk := stk)
    (stoff := stoff) (p6 := p)
  refine ⟨by omega, rfl, good, fun n => ?_, ?_, hfmi⟩
  · simp
  · funext n
    simp [WordToStack.Native.compileWordToStackNative, appListAppend, appendAux]

/-- The word-level initial state `wst = word_to_stack$make_init ... sst` built on the
stack state of a successful `full_make_init` satisfies the state premises of
`word_to_word_compile_semantics` (HOL proof lines 1686-1716: `gc_fun_const_ok` via
`gc_fun_const_ok_word_gc_fun`, empty stack, its code, and `lookup 0 locals`). -/
theorem wordStateFactsWithArena {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k : Nat)
    (code : Spt (Nat × WordLangProgHOL (BitVec width)))
    (worac : Nat → (Nat × C) × List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (scc : StackToLab.Config) (dc : DataToWord.Config) (maxHeap stk : Nat)
    (stoff : BitVec width × BitVec width) (bitmaps : List (BitVec width))
    (p : List (Nat × StackLang.HolProg width)) (labSt : LabSem.State width C F)
    (saveRegs : Nat → Bool) (dataSp : Nat)
    (soracle : Nat → C × List (Nat × StackLang.HolProg width) × List (BitVec width))
    (sst xxx : StackSemStateFiniteExact width C F)
    (arena : BitVec width → Prop)
    (hfmi : fullMakeInitWithArena scc dc maxHeap stk stoff bitmaps p labSt
      saveRegs dataSp soracle arena = (sst, some xxx)) :
    let wst := WordToStack.Native.Initialization.makeInit ac k sst code worac
    WordSimp.gcFunConstOk wst.gcFun ∧ wst.stack = [] ∧ wst.code = code ∧
      sptLookup 0 wst.locals = some (.loc 1 0) := by
  unfold fullMakeInitWithArena at hfmi
  simp only [Prod.mk.injEq] at hfmi
  obtain ⟨rfl, -⟩ := hfmi
  refine ⟨?_, rfl, rfl, ?_⟩
  · exact DataToWord.Proofs.Gc.gcFunConstOkWordGcFun
  · simp [WordToStack.Native.Initialization.makeInit]; rfl


theorem labStackLinkWithArena {width : Nat} [NeZero width] {C F : Type}
    {stackConf : StackToLab.Config} {dataConf : DataToWord.Config} {maxHeap sp : Nat}
    {offset : BitVec width × BitVec width} {bitmaps : List (BitVec width)}
    {code : List (Nat × StackLang.HolProg width)} {t : LabSem.State width C F}
    {saveRegs : Nat → Bool} {dataSp : Nat}
    {coracle : Nat → C × List (Nat × StackLang.HolProg width) × List (BitVec width)}
    {s : StackSemStateFiniteExact width C F} {opt : Option (StackSemStateFiniteExact width C F)}
    (precise : Bool) (w : HolBehaviour) (hw : w ≠ .fail)
    {arena : BitVec width → Prop}
    (hpre : fullMakeInitWithArena stackConf dataConf maxHeap sp offset bitmaps code t
        saveRegs dataSp coracle arena = (s, opt) ∧
      labAssumptionsWithArena stackConf dataConf maxHeap sp offset bitmaps code t
        saveRegs dataSp coracle arena)
    (hstack : SemanticsPropsHOL.extendWithResourceLimitPrimeHOL precise (fun b => b = w)
      (StackSemEvaluate.semantics BvlToBvi.initGlobalsLocation s)) :
    opt ≠ none ∧
      SemanticsPropsHOL.extendWithResourceLimitPrimeHOL precise (fun b => b = w)
        (LabSem.semantics t) := by
  obtain ⟨hopt, hsem⟩ := fullMakeInitWithArena_semantics hpre.1 hpre.2
  refine ⟨hopt, ?_⟩
  rw [hsem (extendPrime_singleton_ne_fail precise w _ hstack hw)]
  exact hstack

#print axioms initStateOkWithArena
#print axioms labStackLinkWithArena
end InitE.Op5
