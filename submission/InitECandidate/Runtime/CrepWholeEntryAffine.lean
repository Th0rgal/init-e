import InitECandidate.Runtime.CrepWholeEntry
import InitECandidate.Runtime.CrepEntryAffine
import Flapjack.Pancake.CrepToLoop.Proofs.StateRelImpSemantics
import InitECandidate.Runtime.BaselineAffineFuelMono
import InitECandidate.Runtime.CrepAffine
namespace InitECandidate.Runtime
open Flapjack Flapjack.Basis.Pure.MlString Flapjack.Compiler.Encoders.Asm

/-- Quantitative whole-program entry bridge deriving the original compiler
context and code relations from the installed source/target procedure lists. -/
theorem crep_whole_entry_bounded_affine {width : Nat} [NeZero width] {F : Type}
    (s : CrepSemHOLState width F) (t : LoopSemStateFiniteExact width F)
    (entries : List (MlString × List Nat × CrepProgHOL width))
    (start : MlString) (label : Nat) (arch : AsmArchitecture) (body : CrepProgHOL width)
    (limit : Nat) (small : sizeOf (CrepProgHOL.call none start [] : CrepProgHOL width) ≤ limit)
    (bounded : CrepCodeSize limit (crepSimpMapcsHOL s))
    (state : crepToLoopStateRelExact s t)
    (memory : crepToLoopMemRelHOLExact s.memory t.memory s.memaddrs)
    (globals : crepToLoopGlobalsRelHOLExact s.globals t.globals)
    (distinct : (entries.map Prod.fst).Nodup)
    (sourceCode : s.code = alistToFmapCodeExact entries)
    (targetCode : t.code = sptFromAList (compileProgHOLExact arch entries))
    (locals : s.locals = HolFiniteMapExact.empty)
    (entry : holAlookup entries start = some ([],body))
    (lookup : (crepToLoopMakeFuncsExactHOL entries).lookup start = some (label,0))
    (result : Option (CrepResultHOLExact width)) (post : CrepSemHOLState width F)
    (run : evalCrepSemHOLProgExact s (.call none start []) = (result,post))
    (good : result ≠ some .error) :
    ∃ extra, extra ≤ ((5 * limit + 5) * s.clock + 2 * limit) ∧
      ∃ loopResult loopPost,
      LoopSemStateFiniteExact.evaluate (.call none (some label) [] none)
        {t with clock := t.clock + extra} = (loopResult,loopPost) ∧
      crepToLoopStateRelExact post loopPost ∧
      loopResult = Pancake.CrepToLoop.Proofs.NCompileCorrect.resultToLoop result := by
  let ctxt : CrepToLoopContextExact := mkCtxtExact arch HolFiniteMapExact.empty (crepToLoopMakeFuncsExactHOL entries) 0
  have code : crepToLoopCodeRel2Exact ctxt s.code t.code := by
    rw [sourceCode,targetCode]
    exact mkCtxtCodeImpCodeRel2Exact arch entries start body ⟨distinct,entry⟩
  have lab : findLabExact ctxt start = label := by
    simp [findLabExact,ctxt,mkCtxtExact,lookup]
  have distinctVars : crepToLoopDistinctVarsExact ctxt.vars := by
    intro x y n m hx
    simp [ctxt,mkCtxtExact,HolFiniteMapExact.empty] at hx
  have maxVars : crepToLoopCtxtMaxExact ctxt.vmax ctxt.vars := by
    intro v m hv
    simp [ctxt,mkCtxtExact,HolFiniteMapExact.empty] at hv
  have lookup' : (crepToLoopMakeFuncsExactHOL entries).lookup start = some (findLabExact ctxt start,0) := by
    rw [lab]; exact lookup
  obtain ⟨extra,extraSmall,loopResult,loopPost,evaluated,postState,same⟩ :=
    crep_entry_affine ctxt s.code t.code start s result post t entries label body limit small bounded
      code run ⟨state.2.2.2.1,state.2.1,state.1,state.2.2.1,state.2.2.2.2.1,
        state.2.2.2.2.2.1,state.2.2.2.2.2.2,memory,globals,locals,rfl,rfl⟩ lookup'
      ⟨lab,sourceCode,rfl,entry,distinctVars,maxVars⟩ good
  rw [lab] at evaluated
  exact ⟨extra,extraSmall,loopResult,loopPost,evaluated,postState,same⟩

#print axioms crep_whole_entry_bounded_affine
end InitECandidate.Runtime
