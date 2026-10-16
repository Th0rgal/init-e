import InitECandidate.Runtime.RunFramesWhile
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Proofs.FrontendCodecComputation

/-- Finalization is the literal epilogue call followed by parent restoration
    for a top-level frame, or finish_child for a nested frame. -/
theorem runFrames_finish_shape : runFramesFinishBranch =
    .seq .skip (.seq (.call (some (none,none)) (ofString "frame_epilogue") [])
      (.ite (.cmp .equal (continuationLoad 16) (.const 0))
        (.seq (.assign .global (ofString "ev") (continuationLoad 0))
          (.seq (.assign .global (ofString "cur_cont") (continuationLoad 8))
            (.assign .local (ofString "go") (.const 0))))
        (.dec (ofString "err2") .one (.const 0)
          (.call (some (none,some (ofString "EvmErr",ofString "err2",
            .call (some (none,none)) (ofString "frame_exception") [.var .local (ofString "err2")])))
            (ofString "finish_child") [])))) := by
  simp only [runFramesFinishBranch,runFramesLoopBody,runFramesDecodedBody,Guest.guestFn_run_frames,
    declToHOLStructural,funDeclToHOLStructural,progToHOLStructural,expToHOLStructural,
    expListToHOLStructural,shapeToHOLStructural,List.map_cons,List.map_nil,Option.map_none,continuationLoad]
  rfl

/-- Assigning the source done flag preserves every other runtime field. -/
theorem evaluate_runFrames_set_done {F : Type} (state : PanSemStateFiniteExact 64 F)
    (old : BitVec 64)
    (doneLocal : state.locals.lookup (ofString "done") = some (.val (.word old))) :
    evaluateHOLFiniteState state (.assign .local (ofString "done") (.const 1)) =
      (none,setVarHOLFinite (ofString "done") (.val (.word 1)) state) := by
  classical
  simp [evaluateHOLFiniteState_assign,evalHOLExact,isValidValueHOLExact,
    lookupKvarHOLExact,toExact,doneLocal,shapeEqHOL,shapeOfHOLExact,setKvarHOLFinite]

/-- An inactive frame reaches finalization rather than invoking op_dispatch. -/
theorem evaluate_runFrames_inactive_precheck {F : Type} (state : PanSemStateFiniteExact 64 F)
    (continuation frame old : BitVec 64)
    (contGlobal : state.globals.lookup (ofString "cur_cont") = some (.val (.word continuation)))
    (frameGlobal : state.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (pendingDomain : state.memaddrs (continuation + 32))
    (pendingMemory : state.memory (continuation + 32) = .word 0)
    (activeDomain : state.memaddrs (frame + 104))
    (activeMemory : state.memory (frame + 104) = .word 0)
    (doneLocal : state.locals.lookup (ofString "done") = some (.val (.word old))) :
    evaluateHOLFiniteState state runFramesPrecheck =
      (none,setVarHOLFinite (ofString "done") (.val (.word 1)) state) := by
  unfold runFramesPrecheck
  rw [evaluate_loaded_word_ite state (continuationLoad 32) 0 0 .notEqual
    (eval_continuationLoad state continuation 32 0 contGlobal pendingDomain pendingMemory)]
  simp only [Compiler.Encoders.Asm.wordCmpHOL]
  rw [evaluate_loaded_word_ite state (fundingLoad 104) 0 0 .equal
    (eval_fundingLoad state frame 104 0 frameGlobal activeDomain activeMemory)]
  simp only [Compiler.Encoders.Asm.wordCmpHOL]
  exact evaluate_runFrames_set_done state old doneLocal

#print axioms runFrames_finish_shape
#print axioms evaluate_runFrames_set_done
#print axioms evaluate_runFrames_inactive_precheck
end InitECandidate.Runtime
