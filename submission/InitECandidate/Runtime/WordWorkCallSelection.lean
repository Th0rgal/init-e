import InitECandidate.Runtime.WordWorkCallBudgets
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompCorrect.CallReturning
namespace InitECandidate.Runtime.WordToStack
open Flapjack Flapjack.WordSemStateFiniteExact
open Flapjack.WordToStackProofs.CompCorrect.CallReturning

theorem tail_call_budgets {width : Nat} [NeZero width] {C F : Type}
    (dest : Option Nat) (args : List Nat) (source : WordSemStateFiniteExact width (Nat × C) F)
    (xs args1 : List (WordLocW width)) (prog : WordLangProgHOL (BitVec width)) (ss : Option Nat)
    (get : getVars args source = some xs) (bad : ¬wordSemBadDestArgs dest args = true)
    (find : wordSemFindCode dest (wordSemAddRetLoc
      (none : Option (List Nat × WordLangCutsetsHOL × WordLangProgHOL (BitVec width) × Nat × Nat)) xs)
      source.code source.stackSize = some (args1, prog, ss)) (nonzero : source.clock ≠ 0) :
    callWorkBudgets none dest args none source =
      (wordWork prog (Flapjack.WordSemStateFiniteExact.callEnv args1 ss
        (Flapjack.WordSemStateFiniteExact.decClock source)), 0, 0) := by
  simp only [callWorkBudgets, get, bad, Bool.false_eq_true, if_false, find, nonzero]

theorem returning_callee_budget {width : Nat} [NeZero width] {C F : Type}
    (values : List Nat) (names : WordLangCutsetsHOL) (retCode : WordLangProgHOL (BitVec width))
    (l1 l2 : Nat) (dest : Option Nat) (args : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
    (source : WordSemStateFiniteExact width (Nat × C) F)
    (xs args1 : List (WordLocW width)) (prog : WordLangProgHOL (BitVec width))
    (ss : Option Nat) (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (guards : SourceGuards values names retCode l1 l2 dest args source xs args1 prog ss envs)
    (nonzero : source.clock ≠ 0) :
    (callWorkBudgets (some (values, names, retCode, l1, l2)) dest args handler source).1 =
      wordWork prog (Flapjack.WordSemStateFiniteExact.callEnv args1 ss
        (pushEnv envs handler (Flapjack.WordSemStateFiniteExact.decClock source))) := by
  obtain ⟨get, bad, find, valid, cut⟩ := guards
  simp only [callWorkBudgets, get, bad, Bool.false_eq_true, if_false, find, valid, cut, nonzero]
  rw [fix_clock_evaluate]
  cases run : evaluate prog (Flapjack.WordSemStateFiniteExact.callEnv args1 ss
        (pushEnv envs handler (Flapjack.WordSemStateFiniteExact.decClock source))) with
  | mk result post =>
      cases result with
      | none => rfl
      | some result => cases result <;> rfl

theorem returning_continuation_budget {width : Nat} [NeZero width] {C F : Type}
    (values : List Nat) (names : WordLangCutsetsHOL) (retCode : WordLangProgHOL (BitVec width))
    (l1 l2 : Nat) (dest : Option Nat) (args : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
    (source : WordSemStateFiniteExact width (Nat × C) F)
    (xs args1 : List (WordLocW width)) (prog : WordLangProgHOL (BitVec width))
    (ss : Option Nat) (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (guards : SourceGuards values names retCode l1 l2 dest args source xs args1 prog ss envs)
    (nonzero : source.clock ≠ 0)
    (location : WordLocW width) (returned : List (WordLocW width))
    (post popped : WordSemStateFiniteExact width (Nat × C) F)
    (run : evaluate prog (Flapjack.WordSemStateFiniteExact.callEnv args1 ss
        (pushEnv envs handler (Flapjack.WordSemStateFiniteExact.decClock source))) = (some (.result location returned), post))
    (checked : ¬(location ≠ .loc l1 l2 ∨ returned.length ≠ values.length))
    (pop : popEnv post = some popped) (domain : sptDomainEqUnion popped.locals envs.1 envs.2) :
    (callWorkBudgets (some (values, names, retCode, l1, l2)) dest args handler source).2.1 =
      wordWork retCode (Flapjack.WordSemStateFiniteExact.setVars values returned popped) := by
  obtain ⟨get, bad, find, valid, cut⟩ := guards
  simp only [callWorkBudgets, get, bad, Bool.false_eq_true, if_false, find, valid, cut, nonzero]
  rw [fix_clock_evaluate, run]
  simp only [checked, pop, domain, if_true, if_false]

theorem exception_continuation_budget {width : Nat} [NeZero width] {C F : Type}
    (values : List Nat) (names : WordLangCutsetsHOL) (retCode : WordLangProgHOL (BitVec width))
    (l1 l2 : Nat) (dest : Option Nat) (args : List Nat)
    (reg h1 h2 : Nat) (handlerCode : WordLangProgHOL (BitVec width))
    (source : WordSemStateFiniteExact width (Nat × C) F)
    (xs args1 : List (WordLocW width)) (prog : WordLangProgHOL (BitVec width))
    (ss : Option Nat) (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (guards : SourceGuards values names retCode l1 l2 dest args source xs args1 prog ss envs)
    (nonzero : source.clock ≠ 0)
    (location value : WordLocW width) (post : WordSemStateFiniteExact width (Nat × C) F)
    (run : evaluate prog (Flapjack.WordSemStateFiniteExact.callEnv args1 ss
        (pushEnv envs (some (reg, handlerCode, h1, h2)) (Flapjack.WordSemStateFiniteExact.decClock source))) = (some (.exception location value), post))
    (checked : ¬location ≠ .loc h1 h2) (domain : sptDomainEqUnion post.locals envs.1 envs.2) :
    (callWorkBudgets (some (values, names, retCode, l1, l2)) dest args
      (some (reg, handlerCode, h1, h2)) source).2.2 =
      wordWork handlerCode (Flapjack.WordSemStateFiniteExact.setVar reg value post) := by
  obtain ⟨get, bad, find, valid, cut⟩ := guards
  simp only [callWorkBudgets, get, bad, Bool.false_eq_true, if_false, find, valid, cut, nonzero]
  rw [fix_clock_evaluate, run]
  simp only [checked, domain, if_true, if_false]

#print axioms exception_continuation_budget
#print axioms returning_continuation_budget
end InitECandidate.Runtime.WordToStack
