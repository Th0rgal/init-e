import InitECandidate.Runtime.RunFramesIteration
import InitECandidate.Runtime.LocalScopeUpdate
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A handled exception may change err inside its scope. Leaving the source
scopes restores both err and pc while preserving handler memory effects. -/
theorem evaluate_runFrames_changed_err_dispatch {F : Type}
    (state post : PanSemStateFiniteExact 64 F) (frame pc length error : BitVec 64)
    (frameGlobal : state.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (pcDomain : state.memaddrs (frame + 0))
    (pcMemory : state.memory (frame + 0) = .word pc)
    (lengthDomain : state.memaddrs (frame + 56))
    (lengthMemory : state.memory (frame + 56) = .word length)
    (inside : pc.toNat < length.toNat)
    (dispatch : evaluateHOLFiniteState (runFramesDispatchEntry state pc) runFramesDispatchCall = (none,post))
    (locals : post.locals = (setVarHOLFinite (ofString "err") (.val (.word error))
      (setVarHOLFinite (ofString "pc") (.val (.word pc)) state)).locals) :
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
  have errScope := evaluate_scoped_body_updated_local pcState post (ofString "err") .one
    (.const 0) runFramesDispatchCall (.val (.word 0)) (.val (.word error)) none (by simp [evalHOLExact])
    (by simp [shapeEqHOL,shapeOfHOLExact]) dispatch locals
  have pcScope := evaluate_scoped_body_preserving_locals state {post with locals := pcState.locals}
    (ofString "pc") .one (fundingLoad 0)
    (.ite (.cmp .notLower (.var .local (ofString "pc")) (fundingLoad 56))
      (.assign .local (ofString "done") (.const 1))
      (.dec (ofString "err") .one (.const 0) runFramesDispatchCall))
    (.val (.word pc)) none (eval_fundingLoad state frame 0 pc frameGlobal pcDomain pcMemory)
    (by simp [shapeEqHOL,shapeOfHOLExact]) (condition.trans errScope) rfl
  exact pcScope


theorem evaluate_runFrames_loop_changed_err_dispatch {F : Type}
    (state post : PanSemStateFiniteExact 64 F) (continuation frame pc length active error : BitVec 64)
    (contGlobal : state.globals.lookup (ofString "cur_cont") = some (.val (.word continuation)))
    (frameGlobal : state.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (pendingDomain : state.memaddrs (continuation + 32))
    (pendingMemory : state.memory (continuation + 32) = .word 0)
    (activeDomain : state.memaddrs (frame + 104))
    (activeMemory : state.memory (frame + 104) = .word active) (running : active ≠ 0)
    (pcDomain : state.memaddrs (frame + 0)) (pcMemory : state.memory (frame + 0) = .word pc)
    (lengthDomain : state.memaddrs (frame + 56)) (lengthMemory : state.memory (frame + 56) = .word length)
    (inside : pc.toNat < length.toNat)
    (dispatch : evaluateHOLFiniteState (runFramesLoopDispatchEntry state pc) runFramesDispatchCall = (none,post))
    (locals : post.locals = (setVarHOLFinite (ofString "err") (.val (.word error))
      (setVarHOLFinite (ofString "pc") (.val (.word pc))
        (setVarHOLFinite (ofString "done") (.val (.word 0)) state))).locals) :
    evaluateHOLFiniteState state runFramesLoopBody = (none,{post with locals := state.locals}) := by
  let entered := setVarHOLFinite (ofString "done") (.val (.word 0)) state
  have selected := evaluate_runFrames_running_precheck entered continuation frame active
    contGlobal frameGlobal pendingDomain pendingMemory activeDomain activeMemory running
  have dispatched := evaluate_runFrames_changed_err_dispatch entered post frame pc length error frameGlobal
    pcDomain pcMemory lengthDomain lengthMemory inside dispatch locals
  exact evaluate_runFrames_running_loop_body state {post with locals := entered.locals}
    (selected.trans dispatched) rfl

#print axioms evaluate_runFrames_loop_changed_err_dispatch
#print axioms evaluate_runFrames_changed_err_dispatch
end InitECandidate.Runtime
