import InitECandidate.Runtime.WordToStackBudget
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompCorrect.FFI
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompCorrect.Alloc
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompCorrect.Return
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompCorrect.Install

namespace InitECandidate.Runtime.WordToStack.Zero
open Flapjack Flapjack.WordToStackProofs Flapjack.WordToStackProofs.CompCorrect
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native

/-! Zero-extra-clock FFI, allocation, return and dynamic-install simulations,
including all original resource, frame and result-placement postconditions. -/
namespace FFI
open Flapjack.WordToStackProofs.CompCorrect.FFI
theorem compCorrectFFI {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (index : Basis.Pure.MlString.MlString)
    (ptr1 len1 ptr2 len2 : Nat) (names : WordLangCutsetsHOL) (k f frame : Nat)
    (source sourcePost : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F)
    (result : Option (WordSemResult width))
    (bs bsPost : AppList (BitVec width)) (n nPost : Nat)
    (compiled : HolProg width) (lens : List Nat)
    (premises : WordSemStateFiniteExact.evaluate (.ffi index ptr1 len1 ptr2 len2 names) source =
        (result, sourcePost) ∧
      result ≠ some .error ∧ stateRel ac k f frame source target lens 0 ∧
      postAllocConventionsHOL k
        ((.ffi index ptr1 len1 ptr2 len2 names) : WordLangProgHOL (BitVec width)) = true ∧
      flatExpConventions
        ((.ffi index ptr1 len1 ptr2 len2 names) : WordLangProgHOL (BitVec width)) = true ∧
      compNative ac false (.ffi index ptr1 len1 ptr2 len2 names) (bs, n) (k, f, frame) =
        (compiled, (bsPost, nPost)) ∧
      (appListAppend bs).length ≤ n ∧
      n - (appListAppend bs).length ≤ target.bitmaps.length ∧
      List.IsPrefix (appListAppend bsPost) (target.bitmaps.drop (n - (appListAppend bs).length)) ∧
      (∀ loc, StackSem.getLabelsExact compiled loc → StackSem.locCheckExact target.code loc) ∧
      maxVarHOL ((.ffi index ptr1 len1 ptr2 len2 names) : WordLangProgHOL (BitVec width)) <
        2 * frame + 2 * k) :
    ∃ (extraClock : Nat), extraClock ≤ 0 ∧ ∃ (targetPost : StackSemStateFiniteExact width C F)
      (targetResult : Option (StackSemResult width)),
      StackSemEvaluate.evaluate (compiled, {target with clock := target.clock + extraClock}) =
        (targetResult, targetPost) ∧
      compCorrectResult ac k f frame source sourcePost targetPost result targetResult lens := by
  obtain ⟨execution, notError, related, conventions, -, compilation, -, -, -, -, -⟩ := premises
  obtain ⟨rfl, rfl, rfl, rfl, hc1, hc2⟩ :=
    ffiConventions k index ptr1 len1 ptr2 len2 names conventions
  simp only [compNative, Prod.mk.injEq] at compilation
  obtain ⟨rfl, -⟩ := compilation
  have htarget : {target with clock := target.clock + 0} = target := by simp
  refine ⟨0, Nat.le_refl 0, ?_⟩
  rw [htarget]
  have related' := related
  unfold stateRel at related'
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18,
    r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36,
    r37, r38, rloc⟩ := related'
  have hvar : ∀ m v, WordSemStateFiniteExact.getVar (2 * m) source = some v → m < k →
      StackSemStateOps.getVar m target = some v := by
    intro m v hm hlt
    have := StateRelGetVar.stateRelGetVarImp' ac k f frame source target lens 0 (2 * m) v
      ⟨related, hm, by omega, by omega⟩
    rwa [show 2 * m / 2 = m by omega] at this
  rw [WordSemStateFiniteExact.evaluate] at execution
  rw [StackSemEvaluate.evaluate_ffi]
  simp only [show (2 : Nat) / 2 = 1 by rfl, show (4 : Nat) / 2 = 2 by rfl,
    show (6 : Nat) / 2 = 3 by rfl, show (8 : Nat) / 2 = 4 by rfl]
  rcases h4 : WordSemStateFiniteExact.getVar 4 source with _ | (w | ⟨_, _⟩) <;>
    rcases h2 : WordSemStateFiniteExact.getVar 2 source with _ | (w2 | ⟨_, _⟩) <;>
    rcases h8 : WordSemStateFiniteExact.getVar 8 source with _ | (w3 | ⟨_, _⟩) <;>
    rcases h6 : WordSemStateFiniteExact.getVar 6 source with _ | (w4 | ⟨_, _⟩) <;>
    simp only [h4, h2, h8, h6, Prod.mk.injEq] at execution <;>
    try exact absurd execution.1.symm notError
  rw [hvar 2 _ h4 (by omega), hvar 1 _ h2 (by omega), hvar 4 _ h8 (by omega),
    hvar 3 _ h6 (by omega)]
  simp only [r8, r9, r15, r4]
  rcases hce : wordSemCutEnv names source.locals with _ | env
  · simp only [hce, Prod.mk.injEq] at execution
    exact absurd execution.1.symm notError
  simp only [hce] at execution
  rcases hr1 : readBytearrayWordHOL w2 w.toNat
      (memLoadByteAuxExact source.memory source.mdomain source.be) with _ | bytes <;>
    rcases hr2 : readBytearrayWordHOL w4 w3.toNat
      (memLoadByteAuxExact source.memory source.mdomain source.be) with _ | bytes2 <;>
    simp only [hr1, hr2, Prod.mk.injEq] at execution ⊢ <;>
    try exact absurd execution.1.symm notError
  rcases hcall : callFFIHOL source.ffi (.extCall index) bytes bytes2 with ⟨newFfi, newBytes⟩ | outcome <;>
    simp only [hcall, Prod.mk.injEq] at execution ⊢ <;> obtain ⟨rfl, rfl⟩ := execution
  · refine ⟨_, _, ⟨rfl, rfl⟩, ?_⟩
    unfold compCorrectResult
    simp only [Option.map_none, ne_eq, not_true_eq_false, if_false]
    have henv : env = sptUnion (sptInter source.locals names.2) (sptInter source.locals names.1) := by
      unfold wordSemCutEnv at hce
      rcases hcs : wordSemCutEnvs names source.locals with _ | ⟨e1, e2⟩
      · rw [hcs] at hce; cases hce
      rw [hcs] at hce
      obtain ⟨he1, he2⟩ := AllocStateRel.cutEnvs_eq hcs
      simp only [Option.some.injEq] at hce he1 he2
      rw [← hce, ← he1, ← he2]
    unfold stateRel
    refine ⟨r1, r2, r3, rfl, r5, r6, r7, rfl, rfl, r10, r11, r12, r13, r14, rfl, rfl, r17, rfl,
      r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35,
      ?_, r37, r38, ?_⟩
    · show sptWf env = true
      rw [henv]
      exact sptWfUnion _ _ ⟨sptWfInter _ _, sptWfInter _ _⟩
    · intro m v hm
      change sptLookup m env = some v at hm
      rw [henv, sptLookup_sptUnion, sptLookup_sptInterCases, sptLookup_sptInterCases] at hm
      have hlook : sptLookup m source.locals = some v ∧
          (sptDomain names.1 m ∨ sptDomain names.2 m) := by
        unfold sptDomain
        revert hm
        cases sptLookup m source.locals <;> cases sptLookup m names.2 <;>
          cases sptLookup m names.1 <;> simp
      obtain ⟨hl, hd⟩ := hlook
      have hev : m % 2 = 0 ∧ 2 * k ≤ m := hd.elim (hc1 m) (hc2 m)
      obtain ⟨he, hif⟩ := rloc m v hl
      refine ⟨he, ?_⟩
      rw [if_neg (by omega)] at hif ⊢
      exact hif
  · refine ⟨_, _, ⟨rfl, rfl⟩, ?_⟩
    unfold compCorrectResult
    simp only [Option.map_some, compileResult, ne_eq, not_true_eq_false, if_false]
    exact ⟨r4.symm, r1⟩


#print axioms compCorrectFFI
end FFI

namespace Alloc
open Flapjack.WordToStackProofs.CompCorrect.Alloc
theorem compCorrectAlloc {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (dest : Nat) (names : WordLangCutsetsHOL) (k f frame : Nat)
    (source sourcePost : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F)
    (result : Option (WordSemResult width))
    (bs bsPost : AppList (BitVec width)) (n nPost : Nat)
    (compiled : HolProg width) (lens : List Nat)
    (premises : WordSemStateFiniteExact.evaluate (.alloc dest names) source = (result, sourcePost) ∧
      result ≠ some .error ∧ stateRel ac k f frame source target lens 0 ∧
      postAllocConventionsHOL k ((.alloc dest names) : WordLangProgHOL (BitVec width)) = true ∧
      flatExpConventions ((.alloc dest names) : WordLangProgHOL (BitVec width)) = true ∧
      compNative ac false (.alloc dest names) (bs, n) (k, f, frame) = (compiled, (bsPost, nPost)) ∧
      (appListAppend bs).length ≤ n ∧
      n - (appListAppend bs).length ≤ target.bitmaps.length ∧
      List.IsPrefix (appListAppend bsPost) (target.bitmaps.drop (n - (appListAppend bs).length)) ∧
      (∀ loc, StackSem.getLabelsExact compiled loc → StackSem.locCheckExact target.code loc) ∧
      maxVarHOL ((.alloc dest names) : WordLangProgHOL (BitVec width)) < 2 * frame + 2 * k) :
    ∃ (extraClock : Nat), extraClock ≤ 0 ∧ ∃ (targetPost : StackSemStateFiniteExact width C F)
      (targetResult : Option (StackSemResult width)),
      StackSemEvaluate.evaluate (compiled, {target with clock := target.clock + extraClock}) =
        (targetResult, targetPost) ∧
      compCorrectResult ac k f frame source sourcePost targetPost result targetResult lens := by
  obtain ⟨execution, notError, related, conventions, -, compilation, hbsn, hbsl, hpre, -,
    maxVar⟩ := premises
  obtain ⟨rfl, hc1, hc2⟩ := allocConventions k dest names conventions
  have hn1 : ∀ x, sptDomain names.1 x → x % 2 = 0 ∧ k ≤ x / 2 :=
    fun x hx => ⟨(hc1 x hx).1, by have := (hc1 x hx).2; omega⟩
  have hn2 : ∀ x, sptDomain names.2 x → x % 2 = 0 ∧ k ≤ x / 2 :=
    fun x hx => ⟨(hc2 x hx).1, by have := (hc2 x hx).2; omega⟩
  have related' := related
  unfold stateRel at related'
  obtain ⟨r1, -, -, -, -, -, r7, -, -, r10, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, -, -, r35, -, -, -, -⟩ := related'
  -- the allocation request comes from source variable 2, i.e. target register 1
  rw [WordSemStateFiniteExact.evaluate] at execution
  rcases hg : WordSemStateFiniteExact.getVar 2 source with _ | (w | ⟨_, _⟩)
  · simp only [hg, Prod.mk.injEq] at execution; exact absurd execution.1.symm notError
  rotate_left
  · simp only [hg, Prod.mk.injEq] at execution; exact absurd execution.1.symm notError
  simp only [hg] at execution
  have hg1 : StackSemStateOps.getVar 1 target = some (.word w) :=
    StateRelGetVar.stateRelGetVarImp' ac k f frame source target lens 0 2 _
      ⟨related, hg, rfl, by omega⟩
  rcases hcut : wordSemCutEnvs names source.locals with _ | envs
  · simp only [WordSemStateFiniteExact.alloc, hcut, Prod.mk.injEq] at execution
    exact absurd execution.1.symm notError
  simp only [compNative] at compilation
  rcases hwl : wLiveNative names (bs, n) (k, f, frame) with ⟨q1, bsw⟩
  rw [hwl] at compilation
  simp only [Prod.mk.injEq] at compilation
  obtain ⟨rfl, rfl⟩ := compilation
  have htarget : {target with clock := target.clock + 0} = target := by simp
  -- the result relation for a simulated allocation
  have finish : ∀ (t1 : StackSemStateFiniteExact width C F) (res1 : Option (StackSemResult width)),
      (result = none → res1 = none ∧ stateRel ac k f frame sourcePost t1 lens 0) →
      (result ≠ none → result = some .notEnoughSpace ∧ res1 = some (.halt (.word 1)) ∧
          sourcePost.clock = t1.clock ∧ sourcePost.ffi = t1.ffi) →
      compCorrectResult ac k f frame source sourcePost t1 result res1 lens := by
    intro t1 res1 hnone hsome
    unfold compCorrectResult
    by_cases hres : result = none
    · obtain ⟨rfl, hrel1⟩ := hnone hres
      subst hres
      simp only [Option.map_none, ne_eq, not_true_eq_false, if_false]
      exact hrel1
    · obtain ⟨rfl, rfl, hcl, hff⟩ := hsome hres
      simp only [Option.map_some, compileResult, ne_eq, not_true_eq_false, if_false]
      exact ⟨hff, hcl⟩
  by_cases hf : 1 ≤ f
  · obtain ⟨t5, hev5, hpush5, hrel5, -, -, hget5⟩ :=
      EvaluateWLive.evaluateWLive ac k f frame names bs n q1 bsPost nPost source target lens envs
        ⟨by rw [hwl], hn1, hn2, related, hf, hcut, hbsn, hbsl, hpre⟩
    have hrel5' := hrel5
    unfold stateRel at hrel5'
    have hclock5 : t5.clock = target.clock := hrel5'.1.symm.trans r1
    have huse5 : t5.useAlloc = true := hrel5'.2.2.2.2.2.2.1
    have hg5 : StackSemStateOps.getVar 1 t5 = some (.word w) :=
      (hget5 1 (by omega)).trans hg1
    obtain ⟨t1, res1, halloc1, hif⟩ :=
      AllocStateRel.allocImpAlloc ac k f frame w names source sourcePost result t5 lens envs
        ⟨execution, hn1, hn2, hf, hrel5, hpush5, hcut, notError⟩
    refine ⟨0, Nat.le_refl 0, t1, res1, ?_, finish t1 res1
      (fun hr => by rw [if_pos hr] at hif; exact ⟨hif.1, hif.2.1⟩)
      (fun hr => by rw [if_neg hr] at hif; exact hif)⟩
    rw [htarget, StackSemEvaluate.evaluate_seq, hev5]
    simp only [StackSemControl.fixClock]
    rw [show min target.clock t5.clock = t5.clock by omega]
    show StackSemEvaluate.evaluate (Prog.alloc 1, t5) = (res1, t1)
    rw [StackSemEvaluate.evaluate_alloc]
    simp only [huse5, Bool.not_true, Bool.false_eq_true, if_false, hg5]
    exact halloc1
  · have hf0 : f = 0 := by omega
    have hfr0 : frame = 0 := by
      by_cases h : frame = 0
      · exact h
      · rw [if_neg h] at r35; omega
    subst hf0 hfr0
    simp only [wLiveNative, if_true, Prod.mk.injEq] at hwl
    obtain ⟨rfl, -⟩ := hwl
    -- with no frame, the stack-placed cutset names cannot exist
    have hempty : ∀ t : Spt Unit, (∀ x, sptDomain t x → 2 * k ≤ x) →
        maxList ((sptToAList t).map Prod.fst) < 2 * k → sptDomain t = fun _ => False := by
      intro t hge hlt
      funext x
      apply propext
      constructor
      · intro hx
        obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp hx
        have hm := maxList_ge_of_mem ((sptToAList t).map Prod.fst) x
          (List.mem_map.mpr ⟨(x, u), (sptToAList_mem_iff_lookup t x u).mpr hu, rfl⟩)
        have := hge x hx
        omega
      · exact False.elim
    simp only [maxVarHOL, cutsetsMaxHOL, max_lt_iff] at maxVar
    have hd1 := hempty names.1 (fun x hx => (hc1 x hx).2) (by omega)
    have hd2 := hempty names.2 (fun x hx => (hc2 x hx).2) (by omega)
    obtain ⟨t1, res1, halloc1, hif⟩ :=
      AllocStateRel.allocImpAlloc2 ac k w names source sourcePost result target lens
        ⟨execution, related, hd1, hd2, notError⟩
    refine ⟨0, Nat.le_refl 0, t1, res1, ?_, finish t1 res1
      (fun hr => by rw [if_pos hr] at hif; exact ⟨hif.1, hif.2.1⟩)
      (fun hr => by rw [if_neg hr] at hif; exact hif)⟩
    rw [htarget, StackSemEvaluate.evaluate_seq, StackSemEvaluate.evaluate_skip]
    simp only [StackSemControl.fixClock, Nat.min_self]
    show StackSemEvaluate.evaluate (Prog.alloc 1, target) = (res1, t1)
    rw [StackSemEvaluate.evaluate_alloc]
    simp only [r7, Bool.not_true, Bool.false_eq_true, if_false, hg1]
    exact halloc1


#print axioms compCorrectAlloc
end Alloc

namespace Return
open Flapjack.WordToStackProofs.CompCorrect.Return
theorem compCorrectReturn {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (register : Nat) (names : List Nat)
    (source : WordSemStateFiniteExact width (Nat × C) F) :
    BoundedSimulation ac (.return register names) source := by
  intro k f frame sourcePost target result bs bsPost n nPost compiled lens premises
  rcases premises with ⟨execution, notError, related, conventions, flat,
    compilation, lengthBound, bitmapBound, bitmapPrefix, labels, maximum⟩
  rw [WordSemStateFiniteExact.evaluate] at execution
  cases sourceRead : WordSemStateFiniteExact.getVar register source with
  | none =>
    simp only [sourceRead, Prod.mk.injEq] at execution
    exact absurd execution.1.symm notError
  | some address =>
    cases address with
    | word word =>
      simp only [sourceRead, Prod.mk.injEq] at execution
      exact absurd execution.1.symm notError
    | loc first second =>
      cases sourceValues : WordSemStateFiniteExact.getVars names source with
      | none =>
        simp only [sourceRead, sourceValues, Prod.mk.injEq] at execution
        exact absurd execution.1.symm notError
      | some values =>
        simp only [sourceRead, sourceValues, Prod.mk.injEq] at execution
        obtain ⟨rfl, rfl⟩ := execution
        obtain ⟨even, canonical, nameBound, countBound⟩ := returnFacts related conventions maximum
        rcases format : Compiler.Backend.WordToStackRegFormat.wReg1 register (k, f, frame) with ⟨loads, output⟩
        simp only [compNative, format, Prod.mk.injEq] at compilation
        obtain ⟨rfl, _⟩ := compilation
        obtain ⟨loaded, loadRun, clockSame, loadRelated, stackLength, spaceSame, bitmapSame,
          preserved, outputNotScratch, outputValue⟩ :=
          LoadRegister.evaluateWStackLoadWReg1 ac k f frame register output loads
            source target lens (.loc first second) format even sourceRead related
        let count := Compiler.Backend.WordToStack.numStackRet k names
        let free := Compiler.Backend.WordToStack.skipFree k f frame names
        let post : StackSemStateFiniteExact width C F :=
          {loaded with stackSpace := loaded.stackSpace + free}
        have freeSpace : loaded.stackSpace + free = loaded.stackSpace + f - count := by
          dsimp [free, count, Compiler.Backend.WordToStack.skipFree]
          omega
        have useStack : loaded.useStack = true := loadRelated.2.2.2.2.1
        have frameBound : loaded.stackSpace + f ≤ loaded.stack.length := by
          unfold stateRel at loadRelated
          aesop (config := { enableSimp := false })
        have freeBound : loaded.stackSpace + free ≤ loaded.stack.length := by
          dsimp [free, Compiler.Backend.WordToStack.skipFree]
          omega
        refine ⟨0, Nat.le_refl 0, post, some (.result (.loc first second)), ?_, ?_⟩
        · simp only [Nat.add_zero]
          rw [LoadRegister.evaluateWStackLoadSeq, StackSemEvaluate.evaluate_seq, loadRun]
          simp only [StackSemControl.fixClock, clockSame, Nat.min_self]
          rw [CallHelpers.evaluateSeqStackFree free (.ret output) loaded
            ⟨useStack, by omega⟩]
          rw [StackSemEvaluate.evaluate_seq, StackSemEvaluate.evaluate_stackFree,
            if_neg (by simp [useStack]), if_neg (by omega)]
          simp only [StackSemControl.fixClock, Nat.min_self]
          rw [StackSemEvaluate.evaluate_ret]
          simp only [StackSemStateOps.getVar] at outputValue ⊢
          rw [outputValue]
        · have lengths := WordSemStateFiniteExact.getVarsLengthLemma names source values sourceValues
          have kLarge : 4 < k := related.2.2.2.2.2.2.2.2.2.1
          have extraEq : values.length - (k - 1) = count := by
            dsimp [count, Compiler.Backend.WordToStack.numStackRet]
            omega
          simp only [compCorrectResult, Option.map_some, compileResult,
            ne_eq, not_true_eq_false, ↓reduceIte]
          constructor
          · rw [extraEq]
            have relation := stateRelReturnFlush loadRelated countBound
            simpa only [post, freeSpace] using relation
          · have placements := returnPlacements loadRelated canonical sourceValues countBound
            simpa only [post, freeSpace] using placements


#print axioms compCorrectReturn
end Return

namespace Install
open Flapjack.WordToStackProofs.CompCorrect.Install
theorem compCorrectInstall {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (ptr len dptr dlen : Nat) (names : WordLangCutsetsHOL)
    (source : WordSemStateFiniteExact width (Nat × C) F) :
    BoundedSimulation ac (.install ptr len dptr dlen names) source := by
  intro k f frame sourcePost target result bs bsPost n nPost compiled lens premises
  obtain ⟨execution, notError, related, conventions, -, compilation, -, -, -, -, -⟩ := premises
  obtain ⟨rfl, rfl, hd3, hd4, hc1, hc2⟩ :=
    installConventions k ptr len dptr dlen names conventions
  rcases fmt1 : Compiler.Backend.WordToStackRegFormat.wReg1 dptr (k, f, frame) with ⟨xs, reg3⟩
  rcases fmt2 : Compiler.Backend.WordToStackRegFormat.wReg2 dlen (k, f, frame) with ⟨ys, reg4⟩
  have programEq := congrArg Prod.fst compilation
  simp only [compNative, fmt1, fmt2] at programEq
  subst compiled
  -- The source run.
  rw [WordSemStateFiniteExact.evaluate] at execution
  rcases hce : wordSemCutEnv names source.locals with _ | env
  · simp only [hce, Prod.mk.injEq] at execution
    exact absurd execution.1.symm notError
  simp only [hce] at execution
  rcases h2 : WordSemStateFiniteExact.getVar 2 source with _ | (w1 | ⟨_, _⟩) <;>
    rcases h4 : WordSemStateFiniteExact.getVar 4 source with _ | (w2 | ⟨_, _⟩) <;>
    rcases h3 : WordSemStateFiniteExact.getVar dptr source with _ | (w3 | ⟨_, _⟩) <;>
    rcases h5 : WordSemStateFiniteExact.getVar dlen source with _ | (w4 | ⟨_, _⟩) <;>
    simp only [h2, h4, h3, h5, Prod.mk.injEq] at execution <;>
    try exact absurd execution.1.symm notError
  rcases hor : source.compileOracle 0 with ⟨⟨bm0, cfg⟩, progs⟩
  simp only [hor] at execution
  rcases hcf : wordSemBufferFlush source.codeBuffer w1 w2 with _ | ⟨bytes, cb⟩ <;>
    rcases hdf : wordSemBufferFlush source.dataBuffer w3 w4 with _ | ⟨data, db⟩ <;>
    simp only [hcf, hdf, Prod.mk.injEq] at execution <;>
    try exact absurd execution.1.symm notError
  rcases hsc : source.compile (bm0, cfg) progs with _ | ⟨bytes', data', cfg'⟩ <;>
    rcases progs with _ | ⟨⟨kk, argc, prog⟩, rest⟩ <;>
    simp only [hsc, Prod.mk.injEq] at execution <;>
    try first
      | exact absurd execution.1.symm notError
      | exact absurd (congrArg Prod.fst execution).symm notError
  by_cases hcond : bytes = bytes' ∧ data = data' ∧
      (holShiftSeq 1 source.compileOracle 0).1 = cfg'
  swap
  · rw [if_neg hcond] at execution
    exact absurd (congrArg Prod.fst execution).symm notError
  rw [if_pos hcond] at execution
  simp only [Prod.mk.injEq] at execution
  obtain ⟨rfl, rfl⟩ := execution
  -- The target loads of the data pointer and length.
  obtain ⟨t1, run1, clock1, rel1, -, -, -, -, regNe, loaded1⟩ :=
    LoadRegister.evaluateWStackLoadWReg1 ac k f frame dptr reg3 xs source target lens
      (.word w3) fmt1 hd3 h3 related
  obtain ⟨t2, run2, clock2, -, rel2, -, -, otherReads, -, loaded2⟩ :=
    LoadRegisterTwo.evaluateWStackLoadWReg2 ac k f frame dlen reg4 ys source t1 lens
      (.word w4) fmt2 hd4 h5 rel1
  have r10 : 4 < k := rel2.2.2.2.2.2.2.2.2.2.1
  have read1 : StackSemStateOps.getVar 1 t2 = some (.word w1) := by
    have := StateRelGetVar.stateRelGetVarImp' ac k f frame source t2 lens 0 2 _
      ⟨rel2, h2, rfl, by omega⟩
    simpa using this
  have read2 : StackSemStateOps.getVar 2 t2 = some (.word w2) := by
    have := StateRelGetVar.stateRelGetVarImp' ac k f frame source t2 lens 0 4 _
      ⟨rel2, h4, rfl, by omega⟩
    simpa using this
  have read3 : StackSemStateOps.getVar reg3 t2 = some (.word w3) := by
    rw [otherReads reg3 regNe]; exact loaded1
  -- The target compiler and oracle on the installed programs.
  have rel2' := rel2
  unfold stateRel at rel2'
  obtain ⟨-, -, -, -, r5, -, -, -, -, -, -, -, -, -, -, -, -, -, r19, r20, r21, r22, -⟩ := rel2'
  rcases hcw : compileWordToStackNative ac false k ((kk, argc, prog) :: rest) (.nil, bm0) with
    ⟨progs2, fs, bm⟩
  have hsc' := hsc
  rw [r21] at hsc'
  simp only [hcw] at hsc'
  rcases htc : t2.compile cfg progs2 with _ | ⟨bytes2, cfg2⟩
  · simp [htc] at hsc'
  simp only [htc, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hsc'
  obtain ⟨rfl, rfl, rfl⟩ := hsc'
  have hor2 : t2.compileOracle 0 = (cfg, progs2, appListAppend bm.1) := by
    rw [r22]; simp only [hor, hcw]
  have hmap := mapFstCompileWordToStack ac false k _ _ _ _ hcw
  rcases progs2 with _ | ⟨⟨kk2, prog2⟩, rest2⟩
  · simp at hmap
  simp only [List.map_cons, List.cons.injEq] at hmap
  obtain ⟨rfl, -⟩ := hmap
  have hflush : wordSemBufferFlush source.dataBuffer w3 w4 = some (data, db) := hdf
  have hdata : source.dataBuffer.buffer = appListAppend bm.1 := by
    unfold wordSemBufferFlush at hflush
    split at hflush
    · simp only [Option.some.injEq, Prod.mk.injEq] at hflush
      rw [hflush.1, hcond.2.1]
    · cases hflush
  have hdb : db.buffer = [] ∧ db.spaceLeft = source.dataBuffer.spaceLeft := by
    unfold wordSemBufferFlush at hflush
    split at hflush
    · simp only [Option.some.injEq, Prod.mk.injEq] at hflush
      rw [← hflush.2]; exact ⟨rfl, rfl⟩
    · cases hflush
  have hcfg : (source.compileOracle 1).1 = (bm.2, cfg2) := hcond.2.2
  have hnew : (holShiftSeq 1 t2.compileOracle 0).1 = cfg2 := by
    show (t2.compileOracle 1).1 = cfg2
    rcases hso : source.compileOracle 1 with ⟨⟨b1, c1⟩, ps⟩
    rw [r22]
    simp only [hso]
    rw [hso] at hcfg
    simp only [Prod.mk.injEq] at hcfg
    rcases compileWordToStackNative ac false k ps (.nil, b1) with ⟨a, b, c⟩
    exact hcfg.2
  -- The target run and the related post-states.
  refine ⟨0, Nat.le_refl 0, { t2 with
      bitmaps := t2.bitmaps ++ appListAppend bm.1
      codeBuffer := cb
      dataBuffer := db
      code := sptUnion t2.code (sptFromAList ((kk2, prog2) :: rest2))
      regs := (StackSemStateOps.restrictIn t2.regs t2.ffiSaveRegs).updateEq (1, .loc kk2 0)
      fpRegs := HolFiniteMapExact.empty
      compileOracle := holShiftSeq 1 t2.compileOracle }, none, ?_, ?_⟩
  · simp only [Nat.add_zero, wStackLoadAppend, Function.comp_apply,
      show (2 : Nat) / 2 = 1 by rfl, show (4 : Nat) / 2 = 2 by rfl]
    rw [LoadRegister.evaluateWStackLoadSeq, StackSemEvaluate.evaluate_seq, run1]
    have fix1 : StackSemControl.fixClock target ((none : Option (StackSemResult width)), t1) =
        (none, t1) := by
      have le : t1.clock ≤ target.clock := by omega
      simp only [StackSemControl.fixClock, Nat.min_eq_right le]
    simp only [fix1]
    rw [LoadRegister.evaluateWStackLoadSeq, StackSemEvaluate.evaluate_seq, run2]
    have fix2 : StackSemControl.fixClock t1 ((none : Option (StackSemResult width)), t2) =
        (none, t2) := by
      have le : t2.clock ≤ t1.clock := by omega
      simp only [StackSemControl.fixClock, Nat.min_eq_right le]
    simp only [fix2]
    rw [StackSemEvaluate.evaluate_install]
    simp only [read1, read2, read3, loaded2, hor2, r20, r19, r5, hcf, hflush, if_true, htc]
    rw [if_pos ⟨hcond.1, hcond.2.1.trans (congrArg (fun x => x.2.2) hor2).symm, hnew⟩]
  · simp only [compCorrectResult, Option.map_none, ne_eq, not_true_eq_false, ↓reduceIte]
    exact installRelation ac k f frame source t2 lens rel2 names hc1 hc2 env hce bm0 cfg kk2 argc
      prog rest hor (_ :: rest2) fs bm hcw cfg2 hcfg cb db hdata hdb


#print axioms compCorrectInstall
end Install

end InitECandidate.Runtime.WordToStack.Zero
