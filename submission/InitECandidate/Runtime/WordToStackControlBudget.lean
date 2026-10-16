import InitECandidate.Runtime.WordToStackBudget
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompCorrect.Clock
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompCorrect.Flat
namespace InitECandidate.Runtime.WordToStack.Zero
open Flapjack Flapjack.WordToStackProofs Flapjack.WordToStackProofs.CompCorrect
open Flapjack.WordToStackProofs.CompCorrect.Clock
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native

/-! Exact zero-extra-clock variants of the pinned control, clock and rejected
flat-expression cases, retaining the entire original simulation conclusion. -/
theorem compCorrectSkip {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k f frame : Nat)
    (source sourcePost : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F)
    (result : Option (WordSemResult width))
    (bs bsPost : AppList (BitVec width)) (n nPost : Nat)
    (compiled : HolProg width) (lens : List Nat)
    (premises : WordSemStateFiniteExact.evaluate .skip source = (result, sourcePost) ∧
      result ≠ some .error ∧ stateRel ac k f frame source target lens 0 ∧
      postAllocConventionsHOL k (.skip : WordLangProgHOL (BitVec width)) = true ∧ flatExpConventions (.skip : WordLangProgHOL (BitVec width)) = true ∧
      compNative ac false .skip (bs, n) (k, f, frame) = (compiled, (bsPost, nPost)) ∧
      (appListAppend bs).length ≤ n ∧
      n - (appListAppend bs).length ≤ target.bitmaps.length ∧
      List.IsPrefix (appListAppend bsPost) (target.bitmaps.drop (n - (appListAppend bs).length)) ∧
      (∀ loc, StackSem.getLabelsExact compiled loc → StackSem.locCheckExact target.code loc) ∧
      maxVarHOL (.skip : WordLangProgHOL (BitVec width)) < 2 * frame + 2 * k) :
    ∃ (extraClock : Nat), extraClock ≤ 0 ∧ ∃ (targetPost : StackSemStateFiniteExact width C F)
      (targetResult : Option (StackSemResult width)),
      StackSemEvaluate.evaluate (compiled, {target with clock := target.clock + extraClock}) =
        (targetResult, targetPost) ∧
      compCorrectResult ac k f frame source sourcePost targetPost result targetResult lens := by
  have execution := premises.1
  simp only [WordSemStateFiniteExact.evaluate] at execution
  obtain ⟨resultEq, postEq⟩ := Prod.mk.inj execution
  have compilation := premises.2.2.2.2.2.1
  have programEq := congrArg Prod.fst compilation
  simp only [compNative] at programEq
  subst compiled
  subst result
  subst sourcePost
  refine ⟨0, Nat.le_refl 0, target, none, ?_, ?_⟩
  · simp only [Nat.add_zero, StackSemEvaluate.evaluate_skip]
  · simpa only [compCorrectResult, compileResult, Option.map_some, Option.map_none,
      ne_eq, not_true_eq_false, ↓reduceIte] using premises.2.2.1

/-- Full original comp_correct Break case. All original premises and the
entire conclusion are retained; native target execution is derived with zero
extra clock. Evaluator closure inherits reals_as_rational_cuts; this structural
case asserts no numerical FP correspondence. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compCorrectBreak {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (label : Nat) (k f frame : Nat)
    (source sourcePost : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F)
    (result : Option (WordSemResult width))
    (bs bsPost : AppList (BitVec width)) (n nPost : Nat)
    (compiled : HolProg width) (lens : List Nat)
    (premises : WordSemStateFiniteExact.evaluate (.break label) source = (result, sourcePost) ∧
      result ≠ some .error ∧ stateRel ac k f frame source target lens 0 ∧
      postAllocConventionsHOL k ((.break label) : WordLangProgHOL (BitVec width)) = true ∧ flatExpConventions ((.break label) : WordLangProgHOL (BitVec width)) = true ∧
      compNative ac false (.break label) (bs, n) (k, f, frame) = (compiled, (bsPost, nPost)) ∧
      (appListAppend bs).length ≤ n ∧
      n - (appListAppend bs).length ≤ target.bitmaps.length ∧
      List.IsPrefix (appListAppend bsPost) (target.bitmaps.drop (n - (appListAppend bs).length)) ∧
      (∀ loc, StackSem.getLabelsExact compiled loc → StackSem.locCheckExact target.code loc) ∧
      maxVarHOL ((.break label) : WordLangProgHOL (BitVec width)) < 2 * frame + 2 * k) :
    ∃ (extraClock : Nat), extraClock ≤ 0 ∧ ∃ (targetPost : StackSemStateFiniteExact width C F)
      (targetResult : Option (StackSemResult width)),
      StackSemEvaluate.evaluate (compiled, {target with clock := target.clock + extraClock}) =
        (targetResult, targetPost) ∧
      compCorrectResult ac k f frame source sourcePost targetPost result targetResult lens := by
  have execution := premises.1
  simp only [WordSemStateFiniteExact.evaluate] at execution
  obtain ⟨resultEq, postEq⟩ := Prod.mk.inj execution
  have compilation := premises.2.2.2.2.2.1
  have programEq := congrArg Prod.fst compilation
  simp only [compNative] at programEq
  subst compiled
  subst result
  subst sourcePost
  refine ⟨0, Nat.le_refl 0, target, some (.break label), ?_, ?_⟩
  · simp only [Nat.add_zero, StackSemEvaluate.evaluate_break]
  · simpa only [compCorrectResult, compileResult, Option.map_some, Option.map_none,
      ne_eq, not_true_eq_false, ↓reduceIte] using premises.2.2.1

/-- Full original comp_correct Continue case. All original premises and the
entire conclusion are retained; native target execution is derived with zero
extra clock. Evaluator closure inherits reals_as_rational_cuts; this structural
case asserts no numerical FP correspondence. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compCorrectContinue {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (label : Nat) (k f frame : Nat)
    (source sourcePost : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F)
    (result : Option (WordSemResult width))
    (bs bsPost : AppList (BitVec width)) (n nPost : Nat)
    (compiled : HolProg width) (lens : List Nat)
    (premises : WordSemStateFiniteExact.evaluate (.continue label) source = (result, sourcePost) ∧
      result ≠ some .error ∧ stateRel ac k f frame source target lens 0 ∧
      postAllocConventionsHOL k ((.continue label) : WordLangProgHOL (BitVec width)) = true ∧ flatExpConventions ((.continue label) : WordLangProgHOL (BitVec width)) = true ∧
      compNative ac false (.continue label) (bs, n) (k, f, frame) = (compiled, (bsPost, nPost)) ∧
      (appListAppend bs).length ≤ n ∧
      n - (appListAppend bs).length ≤ target.bitmaps.length ∧
      List.IsPrefix (appListAppend bsPost) (target.bitmaps.drop (n - (appListAppend bs).length)) ∧
      (∀ loc, StackSem.getLabelsExact compiled loc → StackSem.locCheckExact target.code loc) ∧
      maxVarHOL ((.continue label) : WordLangProgHOL (BitVec width)) < 2 * frame + 2 * k) :
    ∃ (extraClock : Nat), extraClock ≤ 0 ∧ ∃ (targetPost : StackSemStateFiniteExact width C F)
      (targetResult : Option (StackSemResult width)),
      StackSemEvaluate.evaluate (compiled, {target with clock := target.clock + extraClock}) =
        (targetResult, targetPost) ∧
      compCorrectResult ac k f frame source sourcePost targetPost result targetResult lens := by
  have execution := premises.1
  simp only [WordSemStateFiniteExact.evaluate] at execution
  obtain ⟨resultEq, postEq⟩ := Prod.mk.inj execution
  have compilation := premises.2.2.2.2.2.1
  have programEq := congrArg Prod.fst compilation
  simp only [compNative] at programEq
  subst compiled
  subst result
  subst sourcePost
  refine ⟨0, Nat.le_refl 0, target, some (.continue label), ?_, ?_⟩
  · simp only [Nat.add_zero, StackSemEvaluate.evaluate_continue]
  · simpa only [compCorrectResult, compileResult, Option.map_some, Option.map_none,
      ne_eq, not_true_eq_false, ↓reduceIte] using premises.2.2.1


theorem compCorrectTick {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k f frame : Nat)
    (source sourcePost : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F)
    (result : Option (WordSemResult width))
    (bs bsPost : AppList (BitVec width)) (n nPost : Nat)
    (compiled : HolProg width) (lens : List Nat)
    (premises : WordSemStateFiniteExact.evaluate .tick source = (result, sourcePost) ∧
      result ≠ some .error ∧ stateRel ac k f frame source target lens 0 ∧
      postAllocConventionsHOL k (.tick : WordLangProgHOL (BitVec width)) = true ∧ flatExpConventions (.tick : WordLangProgHOL (BitVec width)) = true ∧
      compNative ac false .tick (bs, n) (k, f, frame) = (compiled, (bsPost, nPost)) ∧
      (appListAppend bs).length ≤ n ∧
      n - (appListAppend bs).length ≤ target.bitmaps.length ∧
      List.IsPrefix (appListAppend bsPost) (target.bitmaps.drop (n - (appListAppend bs).length)) ∧
      (∀ loc, StackSem.getLabelsExact compiled loc → StackSem.locCheckExact target.code loc) ∧
      maxVarHOL (.tick : WordLangProgHOL (BitVec width)) < 2 * frame + 2 * k) :
    ∃ (extraClock : Nat), extraClock ≤ 0 ∧ ∃ (targetPost : StackSemStateFiniteExact width C F)
      (targetResult : Option (StackSemResult width)),
      StackSemEvaluate.evaluate (compiled, {target with clock := target.clock + extraClock}) =
        (targetResult, targetPost) ∧
      compCorrectResult ac k f frame source sourcePost targetPost result targetResult lens := by
  have related := premises.2.2.1
  have clocks : source.clock = target.clock := by
    unfold stateRel at related
    exact related.1
  have programEq := congrArg Prod.fst premises.2.2.2.2.2.1
  simp only [compNative] at programEq
  subst compiled
  have execution := premises.1
  rw [WordSemStateFiniteExact.evaluate] at execution
  by_cases zero : source.clock = 0
  · simp only [zero, ↓reduceIte] at execution
    obtain ⟨resultEq, postEq⟩ := Prod.mk.inj execution
    subst result
    subst sourcePost
    refine ⟨0, Nat.le_refl 0, StackSemStateOps.emptyEnv target, some .timeOut, ?_, ?_⟩
    · change StackSemEvaluate.evaluate (.tick, target) =
        (some .timeOut, StackSemStateOps.emptyEnv target)
      rw [StackSemEvaluate.evaluate_tick, if_pos (clocks.symm.trans zero)]
    · simp only [compCorrectResult, Option.map_some, compileResult, ne_eq,
        not_true_eq_false, ↓reduceIte]
      exact ⟨related.2.2.2.1.symm, clocks⟩
  · simp only [zero, ↓reduceIte] at execution
    obtain ⟨resultEq, postEq⟩ := Prod.mk.inj execution
    subst result
    subst sourcePost
    refine ⟨0, Nat.le_refl 0, StackSemStateOps.decClock target, none, ?_, ?_⟩
    · change StackSemEvaluate.evaluate (.tick, target) =
        (none, StackSemStateOps.decClock target)
      have targetNonzero : target.clock ≠ 0 := fun h => zero (clocks.trans h)
      rw [StackSemEvaluate.evaluate_tick, if_neg targetNonzero]
    · simp only [compCorrectResult, Option.map_none, ne_eq, not_true_eq_false, ↓reduceIte]
      exact stateRelDecClock ac k f frame source target lens 0 related

/-- Full original comp_correct MustTerminate case. All original premises and
conclusion remain: stateRel already implies source termdep=0, so the native
execution returns Error, contradicting the original error-free premise. Evaluator closure inherits reals_as_rational_cuts; this structural
case asserts no numerical FP correspondence. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compCorrectMustTerminate {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (body : WordLangProgHOL (BitVec width)) (k f frame : Nat)
    (source sourcePost : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F)
    (result : Option (WordSemResult width))
    (bs bsPost : AppList (BitVec width)) (n nPost : Nat)
    (compiled : HolProg width) (lens : List Nat)
    (premises : WordSemStateFiniteExact.evaluate (.mustTerminate body) source = (result, sourcePost) ∧
      result ≠ some .error ∧ stateRel ac k f frame source target lens 0 ∧
      postAllocConventionsHOL k ((.mustTerminate body) : WordLangProgHOL (BitVec width)) = true ∧ flatExpConventions ((.mustTerminate body) : WordLangProgHOL (BitVec width)) = true ∧
      compNative ac false (.mustTerminate body) (bs, n) (k, f, frame) = (compiled, (bsPost, nPost)) ∧
      (appListAppend bs).length ≤ n ∧
      n - (appListAppend bs).length ≤ target.bitmaps.length ∧
      List.IsPrefix (appListAppend bsPost) (target.bitmaps.drop (n - (appListAppend bs).length)) ∧
      (∀ loc, StackSem.getLabelsExact compiled loc → StackSem.locCheckExact target.code loc) ∧
      maxVarHOL ((.mustTerminate body) : WordLangProgHOL (BitVec width)) < 2 * frame + 2 * k) :
    ∃ (extraClock : Nat), extraClock ≤ 0 ∧ ∃ (targetPost : StackSemStateFiniteExact width C F)
      (targetResult : Option (StackSemResult width)),
      StackSemEvaluate.evaluate (compiled, {target with clock := target.clock + extraClock}) =
        (targetResult, targetPost) ∧
      compCorrectResult ac k f frame source sourcePost targetPost result targetResult lens := by
  have related := premises.2.2.1
  unfold stateRel at related
  rcases related with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, termDepth, _⟩
  have execution := premises.1
  rw [WordSemStateFiniteExact.evaluate] at execution
  simp only [termDepth, ↓reduceDIte] at execution
  have resultEq := (Prod.mk.inj execution).1
  exact False.elim (premises.2.1 resultEq.symm)


theorem compCorrectAssign {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (name : Nat) (expression : WordLangExpHOL (BitVec width)) (k f frame : Nat)
    (source sourcePost : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F)
    (result : Option (WordSemResult width))
    (bs bsPost : AppList (BitVec width)) (n nPost : Nat)
    (compiled : HolProg width) (lens : List Nat)
    (premises : WordSemStateFiniteExact.evaluate (.assign name expression) source = (result, sourcePost) ∧
      result ≠ some .error ∧ stateRel ac k f frame source target lens 0 ∧
      postAllocConventionsHOL k ((.assign name expression) : WordLangProgHOL (BitVec width)) = true ∧ flatExpConventions ((.assign name expression) : WordLangProgHOL (BitVec width)) = true ∧
      compNative ac false (.assign name expression) (bs, n) (k, f, frame) = (compiled, (bsPost, nPost)) ∧
      (appListAppend bs).length ≤ n ∧
      n - (appListAppend bs).length ≤ target.bitmaps.length ∧
      List.IsPrefix (appListAppend bsPost) (target.bitmaps.drop (n - (appListAppend bs).length)) ∧
      (∀ loc, StackSem.getLabelsExact compiled loc → StackSem.locCheckExact target.code loc) ∧
      maxVarHOL ((.assign name expression) : WordLangProgHOL (BitVec width)) < 2 * frame + 2 * k) :
    ∃ (extraClock : Nat), extraClock ≤ 0 ∧ ∃ (targetPost : StackSemStateFiniteExact width C F)
      (targetResult : Option (StackSemResult width)),
      StackSemEvaluate.evaluate (compiled, {target with clock := target.clock + extraClock}) =
        (targetResult, targetPost) ∧
      compCorrectResult ac k f frame source sourcePost targetPost result targetResult lens := by
  have flat := premises.2.2.2.2.1
  simp only [flatExpConventions, Bool.false_eq_true] at flat

/-- Full original comp_correct Store case. All original premises and
complete target clock/run/result/resource conclusion are retained. HOL's own
flat_exp_conventions premise rejects this constructor with arbitrary payloads;
no extra impossible guard or successful-execution restriction is introduced.
Evaluator closure inherits reals_as_rational_cuts; no numerical FP assertion. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compCorrectStore {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (address : WordLangExpHOL (BitVec width)) (value : Nat) (k f frame : Nat)
    (source sourcePost : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F)
    (result : Option (WordSemResult width))
    (bs bsPost : AppList (BitVec width)) (n nPost : Nat)
    (compiled : HolProg width) (lens : List Nat)
    (premises : WordSemStateFiniteExact.evaluate (.store address value) source = (result, sourcePost) ∧
      result ≠ some .error ∧ stateRel ac k f frame source target lens 0 ∧
      postAllocConventionsHOL k ((.store address value) : WordLangProgHOL (BitVec width)) = true ∧ flatExpConventions ((.store address value) : WordLangProgHOL (BitVec width)) = true ∧
      compNative ac false (.store address value) (bs, n) (k, f, frame) = (compiled, (bsPost, nPost)) ∧
      (appListAppend bs).length ≤ n ∧
      n - (appListAppend bs).length ≤ target.bitmaps.length ∧
      List.IsPrefix (appListAppend bsPost) (target.bitmaps.drop (n - (appListAppend bs).length)) ∧
      (∀ loc, StackSem.getLabelsExact compiled loc → StackSem.locCheckExact target.code loc) ∧
      maxVarHOL ((.store address value) : WordLangProgHOL (BitVec width)) < 2 * frame + 2 * k) :
    ∃ (extraClock : Nat), extraClock ≤ 0 ∧ ∃ (targetPost : StackSemStateFiniteExact width C F)
      (targetResult : Option (StackSemResult width)),
      StackSemEvaluate.evaluate (compiled, {target with clock := target.clock + extraClock}) =
        (targetResult, targetPost) ∧
      compCorrectResult ac k f frame source sourcePost targetPost result targetResult lens := by
  have flat := premises.2.2.2.2.1
  simp only [flatExpConventions, Bool.false_eq_true] at flat


#print axioms compCorrectSkip
#print axioms compCorrectBreak
#print axioms compCorrectContinue
#print axioms compCorrectTick
#print axioms compCorrectMustTerminate
#print axioms compCorrectAssign
#print axioms compCorrectStore
end InitECandidate.Runtime.WordToStack.Zero
