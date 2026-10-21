import InitECandidate.Runtime.SSAReturningExceptionCost
import InitECandidate.Runtime.WordStackValueGlobalCost
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASemanticCallCase
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.WordAlloc
open Flapjack.WordSemStateFiniteExact
set_option maxHeartbeats 6000000
set_option pp.structureInstances false

/-- A real callee exception unwinds to the pushed handler frame. Root and
saved-cut invariants derive the restored domains and strong locals relation;
whole saved-stack-value cost transport supplies the same callee work bound.
No target run, restored state relation or callee IH is assumed. -/
theorem ssa_returning_handler_exception_cost {C F : Type}
    (SP TP : WordLangProgHOL (BitVec 64) → Nat) (prices : ∀ p, TP p ≤ SP p)
    (body : WordLangProgHOL (BitVec 64))
    (callee targetCallee returned : WordSemStateFiniteExact 64 C F)
    (original : List (WordSemStackFrame 64)) (size : Option Nat)
    (first second targetFirst targetSecond : Spt (WordLocW 64))
    (roots targetRoots : List (Nat × WordLocW 64))
    (oldHandler l1 l2 : Nat) (x y : WordLocW 64) (f : Nat → Nat)
    (sourceShape : callee.stack = .stackFrame size (sptToAList first) roots
      (some (oldHandler,l1,l2)) :: original)
    (targetShape : targetCallee.stack = .stackFrame size (sptToAList targetFirst) targetRoots
      (some (oldHandler,l1,l2)) :: original)
    (handlerPosition : callee.handler = original.length)
    (entry : {callee with stack := targetCallee.stack} = targetCallee)
    (values : WordSemStackEq.sValEq callee.stack targetCallee.stack)
    (rootKeys : ∀ key, key ∈ roots.map Prod.fst ↔ sptDomain second key)
    (targetRootKeys : ∀ key, key ∈ targetRoots.map Prod.fst ↔ sptDomain targetSecond key)
    (rootMap : roots.map (fun (key,value) => (f key,value)) = targetRoots)
    (firstRelated : Flapjack.WordAlloc.strongLocalsRel f (sptDomain first) first targetFirst)
    (injective : ∀ a b, (sptDomain first a ∨ sptDomain second a) →
      (sptDomain first b ∨ sptDomain second b) → f a = f b → a = b)
    (run : WordSemStateFiniteExact.evaluate body callee = (some (.exception x y),returned)) :
    ∃ targetReturned,
      WordSemStateFiniteExact.evaluate body targetCallee = (some (.exception x y),targetReturned) ∧
      Flapjack.WordAlloc.wordStateEqRel returned targetReturned ∧
      sptDomain returned.locals = (fun key => sptDomain first key ∨ sptDomain second key) ∧
      sptDomain targetReturned.locals = (fun key => sptDomain targetFirst key ∨ sptDomain targetSecond key) ∧
      (∀ live, Flapjack.WordAlloc.strongLocalsRel f live returned.locals targetReturned.locals) ∧
      wordExecutionCost (fun p _ => TP p) body targetCallee ≤
        wordExecutionCost (fun p _ => SP p) body callee := by
  have transport := WordSemStackEq.evaluateStackSwap body callee
  unfold WordSemStackEq.stackSwapPost at transport
  rw [run] at transport
  obtain ⟨_,e0,e,n,tail,m,locals,handlerFrame,_,⟨keys,localShape⟩,
    tailKeys,returnedHandler,swapped⟩ := transport
  have length : callee.handler+1 = callee.stack.length := by
    rw [handlerPosition,sourceShape]
    simp
  rw [WordSemStackEq.lastNLengthCond _ _ length,sourceShape] at handlerFrame
  simp only [List.cons.injEq,WordSemStackFrame.stackFrame.injEq,Option.some.injEq] at handlerFrame
  obtain ⟨⟨rfl,rfl,rfl,rfl⟩,rfl⟩ := handlerFrame
  have targetFrame : wordSemLastN (callee.handler+1) targetCallee.stack =
      .stackFrame size (sptToAList targetFirst) targetRoots (some (oldHandler,l1,l2)) :: original := by
    rw [WordSemStackEq.lastNLengthCond _ _ (by rw [handlerPosition,targetShape]; simp)]
    exact targetShape
  obtain ⟨stack,restored,actual,⟨newLocals,newKeys,newShape,sameValues⟩,stackValues,stackKeys⟩ :=
    swapped targetCallee.stack (sptToAList targetFirst) targetRoots original ⟨targetFrame,values⟩
  have stackEqual : stack = returned.stack :=
    (WordSemStackEq.sValAndKeyEq _ _ ⟨stackValues,
      WordSemStackEq.sKeyEqTrans _ _ _ ⟨tailKeys,stackKeys⟩⟩).symm
  rw [entry,stackEqual,←returnedHandler] at actual
  refine ⟨{returned with locals := restored},actual,?_,?_,?_,?_,?_⟩
  · simp [Flapjack.WordAlloc.wordStateEqRel]
  · rw [localShape,sptDomain_sptUnion]
    funext key
    apply propext
    simp only [sptDomainFromAList]
    rw [←keys,rootKeys]
    simpa only [sptMemMapFstToAList] using (Or.comm :
      (sptDomain second key ∨ sptDomain first key) ↔ (sptDomain first key ∨ sptDomain second key))
  · change sptDomain restored = _
    rw [newShape,sptDomain_sptUnion]
    funext key
    apply propext
    simp only [sptDomainFromAList]
    rw [←newKeys,targetRootKeys]
    simpa only [sptMemMapFstToAList] using (Or.comm :
      (sptDomain targetSecond key ∨ sptDomain targetFirst key) ↔
        (sptDomain targetFirst key ∨ sptDomain targetSecond key))
  · have keyMap : newLocals.map Prod.fst = (locals.map Prod.fst).map f := by
      rw [←newKeys,←Flapjack.WordAlloc.keyMapImplies f roots targetRoots rootMap,keys]
    have zip : locals = (locals.map Prod.fst).zip (newLocals.map Prod.snd) := by
      rw [←sameValues]
      have pairs : ∀ entries : List (Nat × WordLocW 64),
          (entries.map Prod.fst).zip (entries.map Prod.snd) = entries := by
        intro entries
        induction entries with
        | nil => rfl
        | cons pair rest ih => simp [ih]
      exact (pairs locals).symm
    intro live
    rw [localShape,newShape,zip]
    apply Flapjack.WordAlloc.allocLocalsRel f first targetFirst (locals.map Prod.fst) newLocals
      keyMap _ firstRelated live
    intro a b inA inB equal
    apply injective a b _ _ equal
    · exact inA.elim (fun h => Or.inr ((rootKeys a).mp (keys ▸ h))) Or.inl
    · exact inB.elim (fun h => Or.inr ((rootKeys b).mp (keys ▸ h))) Or.inl

  · have safe : (evaluate body callee).1 ≠ some .error := by
      simp only [run]
      simp
    have same := word_stack_value_executed_cost SP body callee safe targetCallee.stack values
    rw [entry] at same
    have monotone := wordExecutionCost_mono (fun p (_ : WordSemStateFiniteExact 64 C F) => TP p)
      (fun p _ => SP p) (fun p _ => prices p) body targetCallee
    exact monotone.trans (Nat.le_of_eq same)

#print axioms ssa_returning_handler_exception_cost
end InitECandidate.Runtime.FineCost
