import InitECandidate.Runtime.PanCrepClock
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang

/-- Full initial relations for the original Crep-to-Loop simulation. -/
def CrepLoopRelated {width : Nat} [NeZero width] {F : Type}
    (s : CrepSemHOLState width F) (t : LoopSemStateFiniteExact width F)
    (ctxt : CrepToLoopContextExact) (live : NumSet) : Prop :=
  crepToLoopStateRelExact s t ∧
  crepToLoopMemRelHOLExact s.memory t.memory s.memaddrs ∧
  crepToLoopGlobalsRelHOLExact s.globals t.globals ∧
  crepToLoopCodeRelExact ctxt s.code t.code ∧
  crepToLoopLocalsRelExact ctxt live s.locals t.locals

/-- Quantitative composition of the original Pancake-to-Crep and optimized
Crep-to-Loop compilers for a returning source execution. -/
theorem pan_return_loop_bounded {width : Nat} [NeZero width] {F : Type}
    (p : ProgHOL width) (s post : PanSemStateFiniteExact width F) (value : ValueHOL width)
    (crep : CrepSemHOLState width F) (panContext : PanToCrepContextExact width)
    (loop : LoopSemStateFiniteExact width F) (loopContext : CrepToLoopContextExact)
    (live : NumSet) (limit : Nat)
    (run : s.evaluateHOLFiniteState p = (some (.returned value),post))
    (state : panToCrepStateRelFiniteExact s crep)
    (code : codeRelExactHOLW panContext s.code crep.code)
    (exceptions : panToCrepExcpRelFiniteExact panContext.eids s.eshapes)
    (locals : panToCrepLocalsRelFiniteExact panContext s.locals crep.locals)
    (localised : localisedProgHOL p = true)
    (related : CrepLoopRelated crep loop loopContext live)
    (small : sizeOf (compileProgExactHOLW panContext p) ≤ limit)
    (bounded : CrepCodeSize limit crep) :
    ∃ extra, extra ≤ workCeiling limit s.clock (sizeOf (compileProgExactHOLW panContext p)) ∧
      ∃ (crepPost : CrepSemHOLState width F) (loopPost : LoopSemStateFiniteExact width F),
      LoopSemStateFiniteExact.evaluate
        (ocompileHOLExact loopContext live (compileProgExactHOLW panContext p))
        {loop with clock := loop.clock + extra} =
          (some (.result ((flattenHOL value).map wlabWlocExact)),loopPost) ∧
      panToCrepStateRelFiniteExact post crepPost ∧
      codeRelExactHOLW panContext post.code crepPost.code ∧
      panToCrepExcpRelFiniteExact panContext.eids post.eshapes ∧
      crepToLoopStateRelExact crepPost loopPost ∧
      crepToLoopMemRelHOLExact crepPost.memory loopPost.memory crepPost.memaddrs ∧
      crepToLoopGlobalsRelHOLExact crepPost.globals loopPost.globals ∧
      crepToLoopCodeRelExact loopContext crepPost.code loopPost.code := by
  obtain ⟨result,crepPost,initialClock,finalClock,evaluated,postState,postCode,postExceptions,outcome⟩ :=
    pan_crep_same_clock p s (some (.returned value)) post crep panContext
      ⟨run,by simp,state,code,exceptions,locals,localised⟩
  change result = some (.return (flattenHOL value)) at outcome
  subst result
  obtain ⟨extra,extraSmall,loopResult,loopPost,loopRun,loopState,loopMemory,loopGlobals,loopCode,loopOutcome⟩ :=
    crep_optimized_ceiling limit (compileProgExactHOLW panContext p) crep small bounded
      (some (.return (flattenHOL value))) crepPost loop loopContext live
      ⟨evaluated,related.1,related.2.1,related.2.2.1,related.2.2.2.1,related.2.2.2.2,
        by simp,by simp,by simp,by simp⟩
  change loopResult = some (.result ((flattenHOL value).map wlabWlocExact)) at loopOutcome
  subst loopResult
  rw [initialClock] at extraSmall
  exact ⟨extra,extraSmall,crepPost,loopPost,loopRun,postState,postCode,postExceptions,
    loopState,loopMemory,loopGlobals,loopCode⟩

/-- The same numerical composition for a final external-call outcome. -/
theorem pan_ffi_loop_bounded {width : Nat} [NeZero width] {F : Type}
    (p : ProgHOL width) (s post : PanSemStateFiniteExact width F) (event : HolFinalEvent)
    (crep : CrepSemHOLState width F) (panContext : PanToCrepContextExact width)
    (loop : LoopSemStateFiniteExact width F) (loopContext : CrepToLoopContextExact)
    (live : NumSet) (limit : Nat)
    (run : s.evaluateHOLFiniteState p = (some (.finalFfi event),post))
    (state : panToCrepStateRelFiniteExact s crep)
    (code : codeRelExactHOLW panContext s.code crep.code)
    (exceptions : panToCrepExcpRelFiniteExact panContext.eids s.eshapes)
    (locals : panToCrepLocalsRelFiniteExact panContext s.locals crep.locals)
    (localised : localisedProgHOL p = true)
    (related : CrepLoopRelated crep loop loopContext live)
    (small : sizeOf (compileProgExactHOLW panContext p) ≤ limit)
    (bounded : CrepCodeSize limit crep) :
    ∃ extra, extra ≤ workCeiling limit s.clock (sizeOf (compileProgExactHOLW panContext p)) ∧
      ∃ (crepPost : CrepSemHOLState width F) (loopPost : LoopSemStateFiniteExact width F),
      LoopSemStateFiniteExact.evaluate
        (ocompileHOLExact loopContext live (compileProgExactHOLW panContext p))
        {loop with clock := loop.clock + extra} =
          (some (.finalFfi event),loopPost) ∧
      panToCrepStateRelFiniteExact post crepPost ∧
      codeRelExactHOLW panContext post.code crepPost.code ∧
      panToCrepExcpRelFiniteExact panContext.eids post.eshapes ∧
      crepToLoopStateRelExact crepPost loopPost ∧
      crepToLoopMemRelHOLExact crepPost.memory loopPost.memory crepPost.memaddrs ∧
      crepToLoopGlobalsRelHOLExact crepPost.globals loopPost.globals ∧
      crepToLoopCodeRelExact loopContext crepPost.code loopPost.code := by
  obtain ⟨result,crepPost,initialClock,finalClock,evaluated,postState,postCode,postExceptions,outcome⟩ :=
    pan_crep_same_clock p s (some (.finalFfi event)) post crep panContext
      ⟨run,by simp,state,code,exceptions,locals,localised⟩
  change result = some (.finalFfi event) at outcome
  subst result
  obtain ⟨extra,extraSmall,loopResult,loopPost,loopRun,loopState,loopMemory,loopGlobals,loopCode,loopOutcome⟩ :=
    crep_optimized_ceiling limit (compileProgExactHOLW panContext p) crep small bounded
      (some (.finalFfi event)) crepPost loop loopContext live
      ⟨evaluated,related.1,related.2.1,related.2.2.1,related.2.2.2.1,related.2.2.2.2,
        by simp,by simp,by simp,by simp⟩
  change loopResult = some (.finalFfi event) at loopOutcome
  subst loopResult
  rw [initialClock] at extraSmall
  exact ⟨extra,extraSmall,crepPost,loopPost,loopRun,postState,postCode,postExceptions,
    loopState,loopMemory,loopGlobals,loopCode⟩

#print axioms pan_ffi_loop_bounded
#print axioms pan_return_loop_bounded
end InitECandidate.Runtime
