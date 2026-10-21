import InitECandidate.Runtime.FullSSAMappedCalleeCost
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.WordAlloc
open Flapjack.WordSemStateFiniteExact
set_option maxHeartbeats 4000000
set_option pp.structureInstances false

/-- Compose the old saved-stack restoration frame with the compiled callee's
mapped frame. The code equation is transported, not erased. -/
theorem fullSSATableFrame_source_transport {C F : Type}
    (source middle target : WordSemStateFiniteExact 64 C F)
    (first : Flapjack.WordAlloc.wordStateEqRel source middle)
    (second : FullSSATableFrame middle target) : FullSSATableFrame source target := by
  simp_all [FullSSATableFrame,Flapjack.WordAlloc.wordStateEqRel]

theorem fullSSATableFrame_target_transport {C F : Type}
    (source middle target : WordSemStateFiniteExact 64 C F)
    (first : FullSSATableFrame source middle)
    (second : Flapjack.WordAlloc.wordStateEqRel middle target) : FullSSATableFrame source target := by
  simp_all [FullSSATableFrame,Flapjack.WordAlloc.wordStateEqRel]

/-- Local renaming and scheduler replacement are tracked separately from the
nonlocal frame, exactly as in the underlying SSA relation. -/
theorem fullSSATableFrame_locals_permute {C F : Type}
    (source target : WordSemStateFiniteExact 64 C F) (frame : FullSSATableFrame source target)
    (sourceLocals targetLocals : Spt (WordLocW 64)) (sourcePerm targetPerm : Nat → Nat → Nat) :
    FullSSATableFrame {source with locals := sourceLocals,permute := sourcePerm}
      {target with locals := targetLocals,permute := targetPerm} := by
  simpa only [FullSSATableFrame,Flapjack.WordAlloc.wordStateEqRel] using frame

/-- Pop an actual saved frame after a compiled callee return. Saved stack keys
are equal at this interface, so the restored locals are exactly equal even
when the current locals before pop differed. -/
theorem fullSSATableFrame_popEnv {C F : Type}
    (source target sourcePopped : WordSemStateFiniteExact 64 C F)
    (frame : FullSSATableFrame source target) (sourcePop : popEnv source = some sourcePopped) :
    ∃ targetPopped, popEnv target = some targetPopped ∧
      FullSSATableFrame sourcePopped targetPopped ∧ sourcePopped.locals = targetPopped.locals := by
  have sameStack : target.stack = source.stack := frame.1.2.2.2.1
  cases sourceStack : source.stack with
  | nil => simp [popEnv,sourceStack] at sourcePop
  | cons saved tail =>
    rcases saved with ⟨size,first,second,handler⟩
    cases handler with
    | none =>
      simp only [popEnv,sourceStack,Option.some.injEq] at sourcePop
      subst sourcePopped
      refine ⟨{target with locals := sptUnion (sptFromAList second) (sptFromAList first), stack := tail,localsSize := size},?_,?_,rfl⟩
      · simp only [popEnv,sameStack,sourceStack]
      · simp_all [FullSSATableFrame,Flapjack.WordAlloc.wordStateEqRel]
    | some handler =>
      rcases handler with ⟨oldHandler,l1,l2⟩
      simp only [popEnv,sourceStack,Option.some.injEq] at sourcePop
      subst sourcePopped
      refine ⟨{target with locals := sptUnion (sptFromAList second) (sptFromAList first), stack := tail,localsSize := size,handler := oldHandler},?_,?_,rfl⟩
      · simp only [popEnv,sameStack,sourceStack]
      · simp_all [FullSSATableFrame,Flapjack.WordAlloc.wordStateEqRel]

#print axioms fullSSATableFrame_source_transport
#print axioms fullSSATableFrame_target_transport
#print axioms fullSSATableFrame_locals_permute
#print axioms fullSSATableFrame_popEnv
end InitECandidate.Runtime.FineCost
