import InitECandidate.Runtime.RunFramesConditions
import InitECandidate.Runtime.LocalScopeRestore
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The exact local environment in which the loop invokes op_dispatch. -/
def runFramesDispatchEntry {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pc : BitVec 64) : PanSemStateFiniteExact 64 F :=
  setVarHOLFinite (ofString "err") (.val (.word 0))
    (setVarHOLFinite (ofString "pc") (.val (.word pc)) state)

/-- A successful dispatch below the bytecode limit exits both temporary
    scopes, preserving its memory effects and restoring the caller locals. -/
theorem evaluate_runFrames_running_dispatch {F : Type}
    (state post : PanSemStateFiniteExact 64 F) (frame pc length : BitVec 64)
    (frameGlobal : state.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (pcDomain : state.memaddrs (frame + 0))
    (pcMemory : state.memory (frame + 0) = .word pc)
    (lengthDomain : state.memaddrs (frame + 56))
    (lengthMemory : state.memory (frame + 56) = .word length)
    (inside : pc.toNat < length.toNat)
    (dispatch : evaluateHOLFiniteState (runFramesDispatchEntry state pc) runFramesDispatchCall = (none,post))
    (locals : post.locals = (runFramesDispatchEntry state pc).locals) :
    evaluateHOLFiniteState state runFramesRunningDispatch = (none,{post with locals := state.locals}) := by
  classical
  let pcState := setVarHOLFinite (ofString "pc") (.val (.word pc)) state
  have frameAtPc : pcState.globals.lookup (ofString "ev") = some (.val (.word frame)) := frameGlobal
  have lengthAtPc := eval_fundingLoad pcState frame 56 length frameAtPc lengthDomain lengthMemory
  have pcLookup : pcState.locals.lookup (ofString "pc") = some (.val (.word pc)) := by
    simp [pcState,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have condition : evaluateHOLFiniteState pcState
      (.ite (.cmp .notLower (.var .local (ofString "pc")) (fundingLoad 56))
        (.assign .local (ofString "done") (.const 1))
        (.dec (ofString "err") .one (.const 0) runFramesDispatchCall)) =
      evaluateHOLFiniteState pcState (.dec (ofString "err") .one (.const 0) runFramesDispatchCall) := by
    have comparison : @evalHOLExact 64 F _ pcState.toExact
        (fun address => Classical.propDecidable (pcState.memaddrs address))
        (.cmp .notLower (.var .local (ofString "pc")) (fundingLoad 56)) =
          some (.val (.word 0)) := by
      simp only [evalHOLExact]
      rw [pcLookup,lengthAtPc]
      simp [Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def,Nat.not_le.mpr inside]
    rw [evaluateHOLFiniteState_ite,comparison]
    rfl
  have errScope := evaluate_scoped_body_preserving_locals pcState post (ofString "err") .one
    (.const 0) runFramesDispatchCall (.val (.word 0)) none (by simp [evalHOLExact])
    (by simp [shapeEqHOL,shapeOfHOLExact]) dispatch locals
  have pcScope := evaluate_scoped_body_preserving_locals state {post with locals := pcState.locals}
    (ofString "pc") .one (fundingLoad 0)
    (.ite (.cmp .notLower (.var .local (ofString "pc")) (fundingLoad 56))
      (.assign .local (ofString "done") (.const 1))
      (.dec (ofString "err") .one (.const 0) runFramesDispatchCall))
    (.val (.word pc)) none (eval_fundingLoad state frame 0 pc frameGlobal pcDomain pcMemory)
    (by simp [shapeEqHOL,shapeOfHOLExact]) (condition.trans errScope) rfl
  exact pcScope

/-- A successful running precheck leaves done zero, skips the finish branch,
    and restores the outer loop-body scope. All nonlocal effects survive. -/
theorem evaluate_runFrames_running_loop_body {F : Type}
    (state post : PanSemStateFiniteExact 64 F)
    (step : evaluateHOLFiniteState
      (setVarHOLFinite (ofString "done") (.val (.word 0)) state) runFramesPrecheck = (none,post))
    (locals : post.locals = (setVarHOLFinite (ofString "done") (.val (.word 0)) state).locals) :
    evaluateHOLFiniteState state runFramesLoopBody = (none,{post with locals := state.locals}) := by
  classical
  have doneZero : post.locals.lookup (ofString "done") = some (.val (.word (0#64))) := by
    rw [locals]
    simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have finish : evaluateHOLFiniteState post
      (.ite (.cmp .notEqual (.var .local (ofString "done")) (.const 0)) runFramesFinishBranch .skip) =
        (none,post) := by
    simp [evaluateHOLFiniteState_ite,evalHOLExact,toExact,doneZero,
      Compiler.Encoders.Asm.wordCmpHOL,evaluateHOLFiniteState_skip]
  rw [runFrames_loop_body_shape]
  apply evaluate_scoped_body_preserving_locals state post (ofString "done") .one (.const 0)
    _ (.val (.word 0)) none (by simp [evalHOLExact])
    (by simp [shapeEqHOL,shapeOfHOLExact]) _ locals
  rw [evaluateHOLFiniteState_seq_line780,step]
  exact finish

#print axioms evaluate_runFrames_running_loop_body
#print axioms evaluate_runFrames_running_dispatch
end InitECandidate.Runtime
