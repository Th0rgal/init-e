import InitECandidate.Runtime.FullSSAMappedReturnFrame
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASemanticCallReturn
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.WordAlloc
open Flapjack.WordSemStateFiniteExact
set_option maxHeartbeats 5000000
set_option pp.structureInstances false

/-- Restore the actual saved cut after the compiled callee. Stack-value/key
transport supplies the original renamed pop; the mapped frame supplies the
compiled pop. Both union-domain guards and strong saved locals are derived. -/
theorem ssa_returning_mapped_pop_cut {C F : Type}
    (source target returned : WordSemStateFiniteExact 64 C F)
    (first second targetFirst targetSecond : Spt (WordLocW 64))
    (handler targetHandler : Option (Nat × WordLangProgHOL (BitVec 64) × Nat × Nat))
    (targetStack : List (WordSemStackFrame 64)) (f : Nat → Nat)
    (sourceRoots targetRoots : List (Nat × WordLocW 64))
    (sourcePerm targetPerm : Nat → Nat → Nat)
    (sameStack : source.stack = target.stack)
    (sourceRootRead : wordSemEnvToList second source.permute = (sourceRoots,sourcePerm))
    (targetRootRead : wordSemEnvToList targetSecond target.permute = (targetRoots,targetPerm))
    (rootMap : sourceRoots.map (fun (key,value) => (f key,value)) = targetRoots)
    (firstRelated : Flapjack.WordAlloc.strongLocalsRel f (sptDomain first) first targetFirst)
    (injective : ∀ a b, (sptDomain first a ∨ sptDomain second a) →
      (sptDomain first b ∨ sptDomain second b) → f a = f b → a = b)
    (sourceKeys : WordSemStackEq.sKeyEq
      (WordSemStateFiniteExact.pushEnv (first,second) handler source).stack returned.stack)
    (targetKeys : WordSemStackEq.sKeyEq
      (WordSemStateFiniteExact.pushEnv (targetFirst,targetSecond) targetHandler target).stack targetStack)
    (values : WordSemStackEq.sValEq returned.stack targetStack)
    (compiledReturned : WordSemStateFiniteExact 64 C F)
    (compiledFrame : FullSSATableFrame {returned with stack := targetStack} compiledReturned) :
    ∃ popped targetPopped,
      popEnv returned = some popped ∧ popEnv compiledReturned = some targetPopped ∧
      FullSSATableFrame popped targetPopped ∧
      sptDomain popped.locals = (fun key => sptDomain first key ∨ sptDomain second key) ∧
      sptDomainEqUnion targetPopped.locals targetFirst targetSecond ∧
      (∀ live, Flapjack.WordAlloc.strongLocalsRel f live popped.locals targetPopped.locals) := by
  obtain ⟨popped,renamedPopped,sourcePop,renamedPop,popFrame,sourceDomain,strong⟩ :=
    returningPopCutRelation source target returned first second targetFirst targetSecond handler targetHandler
      targetStack f sourceRoots targetRoots sourcePerm targetPerm sameStack sourceRootRead targetRootRead
      rootMap firstRelated injective sourceKeys targetKeys values
  obtain ⟨compiledPopped,compiledPop,mappedFrame,sameLocals⟩ := fullSSATableFrame_popEnv
    {returned with stack := targetStack} compiledReturned renamedPopped compiledFrame renamedPop
  have targetDomain : sptDomainEqUnion compiledPopped.locals targetFirst targetSecond := by
    obtain ⟨_,_,_,_,_,otherPop,otherRun,_,otherDomain,_⟩ := WordSemStackEq.pushEnvPopEnvSKeyEq
      (targetFirst,targetSecond) targetHandler target {returned with stack := targetStack} targetKeys
    have equal : otherPop = renamedPopped := by
      rw [renamedPop] at otherRun
      exact Option.some.inj otherRun.symm
    rw [equal] at otherDomain
    intro key
    change sptDomain compiledPopped.locals key ↔ sptDomain targetFirst key ∨ sptDomain targetSecond key
    rw [←sameLocals]
    have equality := congrFun otherDomain key
    rw [←equality]
    exact Or.comm
  refine ⟨popped,compiledPopped,sourcePop,compiledPop,
    fullSSATableFrame_source_transport popped renamedPopped compiledPopped popFrame mappedFrame,
    sourceDomain,targetDomain,?_⟩
  intro live
  rw [←sameLocals]
  exact strong live

#print axioms ssa_returning_mapped_pop_cut
end InitECandidate.Runtime.FineCost
