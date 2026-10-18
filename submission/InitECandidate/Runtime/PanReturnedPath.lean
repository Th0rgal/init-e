import InitECandidate.Runtime.PanEvaluationMetadata
import Flapjack.Pancake.Semantics.PanSem.EvaluateClock
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- If a sequence returns and its first part can only finish normally or with
an error, the first part finished normally and the tail returned. -/
theorem seq_returned_of_first {F : Type} {s post : PanSemStateFiniteExact 64 F} {a b : ProgHOL 64}
    {v : ValueHOL 64}
    (first : (evaluateHOLFiniteState s a).1 = none ∨ (evaluateHOLFiniteState s a).1 = some .error)
    (run : evaluateHOLFiniteState s (.seq a b) = (some (.returned v),post)) :
    ∃ mid, evaluateHOLFiniteState s a = (none,mid) ∧ evaluateHOLFiniteState mid b = (some (.returned v),post) := by
  rw [evaluateHOLFiniteState_seq_line780] at run
  cases h : evaluateHOLFiniteState s a with
  | mk r mid =>
    rw [h] at run first
    rcases first with e | e <;> subst e
    · exact ⟨mid,rfl,run⟩
    · simp at run

theorem dec_returned {F : Type} {s post : PanSemStateFiniteExact 64 F} {name : MlS} {shape : ShapeHOL}
    {initializer : ExpHOL 64} {body : ProgHOL 64} {v : ValueHOL 64}
    (run : evaluateHOLFiniteState s (.dec name shape initializer body) = (some (.returned v),post)) :
    ∃ value inner, evaluateHOLFiniteState (setVarHOLFinite name value s) body = (some (.returned v),inner) ∧
      post.globals = inner.globals := by
  rw [evaluateHOLFiniteState_dec_total] at run
  dsimp only at run
  split at run
  · simp at run
  · rename_i value _
    split at run
    · cases h : evaluateHOLFiniteState (setVarHOLFinite name value s) body with
      | mk r inner =>
        rw [h] at run
        simp only [Prod.mk.injEq] at run
        obtain ⟨e,p⟩ := run
        subst e
        exact ⟨value,inner,h,by rw [← p]⟩
    · simp at run

theorem decCall_returned {F : Type} {s post : PanSemStateFiniteExact 64 F} {name function : MlS}
    {shape : ShapeHOL} {arguments : List (ExpHOL 64)} {continuation : ProgHOL 64} {v : ValueHOL 64}
    (run : evaluateHOLFiniteState s (.decCall name shape function arguments continuation) = (some (.returned v),post)) :
    ∃ values body callee returnShape w bodyPost,
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) arguments = some values ∧
      lookupCodeHOLFinite s.code.lookup function values = some (body,callee,returnShape) ∧
      evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (some (.returned w),bodyPost) ∧
      ∃ resumed inner : PanSemStateFiniteExact 64 F, resumed.globals = bodyPost.globals ∧ resumed.code = bodyPost.code ∧
        resumed.memaddrs = bodyPost.memaddrs ∧ resumed.clock ≤ bodyPost.clock ∧
        evaluateHOLFiniteState resumed continuation = (some (.returned v),inner) ∧ post.globals = inner.globals := by
  rw [evaluateHOLFiniteState_decCall_total] at run
  cases args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) arguments with
  | none => rw [args] at run; simp at run
  | some values =>
    rw [args] at run
    dsimp only at run
    cases lookup : lookupCodeHOLFinite s.code.lookup function values with
    | none => rw [lookup] at run; simp at run
    | some installed =>
      obtain ⟨body,callee,returnShape⟩ := installed
      rw [lookup] at run
      dsimp only at run
      split at run
      · simp at run
      · cases bodyRun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with
        | mk r bodyPost =>
          rw [bodyRun] at run
          dsimp only [fixClockHOLFinite] at run
          rcases r with _ | (_ | _ | _ | _ | w | _ | _)
          all_goals first
            | (simp at run; done)
            | skip
          simp only [] at run
          split at run
          · obtain ⟨e,p⟩ := Prod.mk.inj run
            refine ⟨values,body,callee,returnShape,w,bodyPost,rfl,lookup,bodyRun,_,_,?g,?c,?m,?k,Prod.ext e rfl,?p⟩
            case p => rw [← p]
            case k =>
              change (if _ then _ else _) ≤ _
              split <;> omega
            all_goals rfl
          · simp at run

#print axioms seq_returned_of_first
#print axioms dec_returned
#print axioms decCall_returned

end InitECandidate.Runtime
