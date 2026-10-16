import Flapjack.Pancake.Proofs.PanGlobals.CompileCorrect.Assembly
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- The full global-lowering simulation preserves initial and remaining fuel. -/
theorem pan_globals_same_clock {width : Nat} {σ : Type} [NeZero width]
    (program : ProgHOL width) (source : PanSemStateFiniteExact width σ)
    (res : Option (PanSemResultExact width)) (context : PanGlobalsContextExact width)
    (target post : PanSemStateFiniteExact width σ)
    (h : panGlobalsStateRelHOLExact true context source target ∧
      evaluateHOLFiniteState source program = (res,post) ∧ res ≠ some .error) :
    ∃ targetPost, target.clock = source.clock ∧ targetPost.clock = post.clock ∧
      evaluateHOLFiniteState target (compileProgExactHOL context program) = (res,targetPost) ∧
      panGlobalsStateRelHOLExact (goodResHOL res) context post targetPost := by
  obtain ⟨final,run,related⟩ := PanGlobalsCompileCorrectAssembly.compileCorrectHOL program source res context target post h
  exact ⟨final,h.1.2.2.2.2.2.1.symm,related.2.2.2.2.2.1.symm,run,related⟩

#print axioms pan_globals_same_clock
end InitECandidate.Runtime
