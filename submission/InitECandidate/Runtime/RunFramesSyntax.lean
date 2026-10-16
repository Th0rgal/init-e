import InitECandidate.Runtime.FrameHalt
import InitECandidate.Proofs.FrontendCodecComputation
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Proofs.FrontendCodecComputation

def runFramesDecodedBody : ProgHOL 64 :=
  match declToHOLStructural Guest.guestFn_run_frames with | .function fn => fn.body | _ => .skip

def runFramesLoopBody : ProgHOL 64 :=
  match runFramesDecodedBody with | .dec _ _ _ (.seq (.while _ body) _) => body | _ => .skip

def runFramesFinishBranch : ProgHOL 64 :=
  match runFramesLoopBody with | .dec _ _ _ (.seq _ (.ite _ finish _)) => finish | _ => .skip

def continuationLoad (offset : BitVec 64) : ExpHOL 64 :=
  .load .one (.op .add [.var .global (ofString "cur_cont"),.const offset])

def runFramesOpcodeExpression : ExpHOL 64 :=
  .loadByte (.op .add [fundingLoad 48,.var .local (ofString "pc")])

def runFramesExceptionHandler : MlS × MlS × ProgHOL 64 :=
  (ofString "EvmErr",ofString "err",.call (some (none,none)) (ofString "frame_exception") [.var .local (ofString "err")])

def runFramesDispatchCall : ProgHOL 64 :=
  .call (some (none,some runFramesExceptionHandler)) (ofString "op_dispatch") [runFramesOpcodeExpression]

def runFramesRunningDispatch : ProgHOL 64 :=
  .dec (ofString "pc") .one (fundingLoad 0)
    (.ite (.cmp .notLower (.var .local (ofString "pc")) (fundingLoad 56))
      (.assign .local (ofString "done") (.const 1))
      (.dec (ofString "err") .one (.const 0) runFramesDispatchCall))

def runFramesPrecheck : ProgHOL 64 :=
  .ite (.cmp .notEqual (continuationLoad 32) (.const 0))
    (.assign .local (ofString "done") (.const 1))
    (.ite (.cmp .equal (fundingLoad 104) (.const 0))
      (.assign .local (ofString "done") (.const 1)) runFramesRunningDispatch)

/-- The loop-body view is a literal node of the authoritative source function. -/
theorem source_runFrames_body : sourceFunctionBody Guest.guestFn_run_frames =
    .dec (ofString "go") .one (.const 1)
      (.seq (.while (.cmp .notEqual (.var .local (ofString "go")) (.const 0)) runFramesLoopBody)
        (.return (.const 0))) := by
  unfold sourceFunctionBody
  rw [declToHOL_eq]
  simp only [runFramesLoopBody,runFramesDecodedBody,Guest.guestFn_run_frames,
    declToHOLStructural,funDeclToHOLStructural,progToHOLStructural,expToHOLStructural,
    shapeToHOLStructural,expListToHOLStructural,List.map_cons,List.map_nil,Option.map_none]
  rfl

/-- Named parts expose the real loop body while retaining its full finish branch. -/
theorem runFrames_loop_body_shape : runFramesLoopBody =
    .dec (ofString "done") .one (.const 0)
      (.seq runFramesPrecheck (.ite (.cmp .notEqual (.var .local (ofString "done")) (.const 0))
        runFramesFinishBranch .skip)) := by
  simp only [runFramesLoopBody,runFramesDecodedBody,runFramesFinishBranch,Guest.guestFn_run_frames,
    declToHOLStructural,funDeclToHOLStructural,progToHOLStructural,expToHOLStructural,
    shapeToHOLStructural,expListToHOLStructural,List.map_cons,List.map_nil,Option.map_none,runFramesPrecheck,
    runFramesRunningDispatch,runFramesDispatchCall,runFramesOpcodeExpression,
    runFramesExceptionHandler,continuationLoad,fundingLoad]
  rfl

#print axioms source_runFrames_body
#print axioms runFrames_loop_body_shape
end InitECandidate.Runtime
