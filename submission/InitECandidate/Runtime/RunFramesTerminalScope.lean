import InitECandidate.Runtime.RunFramesFinish
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Terminal finalization may change go, so restore only the scoped done
    variable rather than requiring the entire local map to be unchanged. -/
theorem evaluate_runFrames_terminal_loop_body {F : Type}
    (state selected post : PanSemStateFiniteExact 64 F)
    (precheck : evaluateHOLFiniteState
      (setVarHOLFinite (ofString "done") (.val (.word 0)) state) runFramesPrecheck = (none,selected))
    (doneLocal : selected.locals.lookup (ofString "done") = some (.val (.word 1)))
    (finish : evaluateHOLFiniteState selected runFramesFinishBranch = (none,post)) :
    evaluateHOLFiniteState state runFramesLoopBody =
      (none,{post with locals := (HolFiniteMapExact.resVarEq post.locals
        (ofString "done",state.locals.lookup (ofString "done")))}) := by
  classical
  have branch : evaluateHOLFiniteState selected
      (.ite (.cmp .notEqual (.var .local (ofString "done")) (.const 0)) runFramesFinishBranch .skip) =
        (none,post) := by
    simp [evaluateHOLFiniteState_ite,evalHOLExact,doneLocal,
      Compiler.Encoders.Asm.wordCmpHOL,finish]
  rw [runFrames_loop_body_shape,evaluateHOLFiniteState_dec_total]
  simp only [evalHOLExact]
  have shapeOk : shapeEqHOL .one (shapeOfHOLExact (.val (.word (0 : BitVec 64)))) = true := by
    simp [shapeEqHOL,shapeOfHOLExact]
  rw [if_pos shapeOk]
  rw [evaluateHOLFiniteState_seq_line780,precheck]
  dsimp only
  rw [branch]

/-- Leaving the done scope preserves the cleared go flag used by the while
    exit rule, even when finalization changed the caller's other locals. -/
theorem runFrames_terminal_go_preserved {F : Type}
    (state post : PanSemStateFiniteExact 64 F)
    (goZero : post.locals.lookup (ofString "go") = some (.val (.word 0))) :
    (HolFiniteMapExact.resVarEq post.locals
      (ofString "done",state.locals.lookup (ofString "done"))).lookup (ofString "go") =
        some (.val (.word 0)) := by
  rw [restore_other_local post.locals (ofString "done") (ofString "go") _ (by decide)]
  exact goZero

#print axioms evaluate_runFrames_terminal_loop_body
#print axioms runFrames_terminal_go_preserved
end InitECandidate.Runtime
