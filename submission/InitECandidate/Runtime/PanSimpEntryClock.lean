import InitECandidate.Runtime.PanSimpClock
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- Updating both clocks retains the full simplifier code/state relation. -/
theorem pan_simp_relation_clock {width : Nat} [NeZero width] {F : Type}
    (source target : PanSemStateFiniteExact width F) (fuel : Nat)
    (related : PanSimp.stateRel source target target.code) :
    PanSimp.stateRel {source with clock := fuel} {target with clock := fuel} target.code := by
  refine ⟨?_,related.2.1,related.2.2⟩
  exact congrArg (fun state : PanSemStateFiniteExact width F => {state with clock := fuel}) related.1

/-- Original entry calls retain their source clock through simplification,
including final FFI and every original compiler state-relation guarantee. -/
theorem pan_simp_entry_same_clock {width : Nat} [NeZero width] {F : Type}
    (source target : PanSemStateFiniteExact width F) (start : MlS) (fuel : Nat)
    (related : PanSimp.stateRel source target target.code)
    (result : Option (PanSemResultExact width)) (post : PanSemStateFiniteExact width F)
    (run : evaluateHOLFiniteState {source with clock := fuel} (.call none start []) = (result,post))
    (good : result ≠ some .error) :
    ∃ targetPost, evaluateHOLFiniteState {target with clock := fuel} (.call none start []) = (result,targetPost) ∧
      targetPost.ffi = post.ffi ∧ targetPost.clock = post.clock ∧ PanSimp.stateRel post targetPost targetPost.code := by
  obtain ⟨targetPost,_,clock,targetRun,finalRelated⟩ := pan_simp_same_clock (.call none start [])
    {source with clock := fuel} result post {target with clock := fuel}
    ⟨run,good,pan_simp_relation_clock source target fuel related⟩
  have call : seqAssocHOL (.skip : ProgHOL width) (.call none start []) = .call none start [] := by
    simp [seqAssocHOL,smartSeqHOL]
  rw [call] at targetRun
  refine ⟨targetPost,targetRun,?_,clock,finalRelated⟩
  have ffi := congrArg (fun state : PanSemStateFiniteExact width F => state.ffi) finalRelated.1
  exact ffi

#print axioms pan_simp_relation_clock
#print axioms pan_simp_entry_same_clock
end InitECandidate.Runtime
