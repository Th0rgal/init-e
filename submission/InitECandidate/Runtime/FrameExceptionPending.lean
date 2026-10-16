import InitECandidate.Runtime.RunFramesFinish
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Proofs.FrontendCodecComputation

def frameExceptionPendingTail : ProgHOL 64 :=
  .seq (.store (.op .add [.var .global (ofString "cur_cont"),.const 32]) (.const 1))
    (.return (.const 0))

def frameExceptionWork : ProgHOL 64 :=
  .ite (.cmp .notEqual (.var .local (ofString "err")) (.const 1))
    (.seq (.call (some (none,none)) (ofString "frame_halt") [.var .local (ofString "err")])
      (.seq (.store (fundingAddress 120) (.var .global (ofString "evm_empty")))
        (.store (fundingAddress 128) (.const 0))))
    (.store (fundingAddress 160) (.var .local (ofString "err")))

/-- Every normally returning frame_exception branch reaches the pending flag. -/
theorem source_frameException_body : sourceFunctionBody Guest.guestFn_frame_exception =
    .seq (.call (some (none,none)) (ofString "refill_frame_state_gas") [])
      (.seq frameExceptionWork frameExceptionPendingTail) := by
  unfold sourceFunctionBody
  rw [declToHOL_eq]
  simp only [Guest.guestFn_frame_exception,declToHOLStructural,funDeclToHOLStructural,
    progToHOLStructural,expToHOLStructural,expListToHOLStructural,shapeToHOLStructural,
    List.map_cons,List.map_nil,Option.map_none,frameExceptionWork,frameExceptionPendingTail,fundingAddress]
  rfl

theorem evaluate_frameException_pending_tail {F : Type} (state : PanSemStateFiniteExact 64 F)
    (continuation : BitVec 64)
    (contGlobal : state.globals.lookup (ofString "cur_cont") = some (.val (.word continuation)))
    (domain : state.memaddrs (continuation + 32)) :
    evaluateHOLFiniteState state frameExceptionPendingTail =
      (some (.returned (.val (.word 0))),
        emptyLocalsHOLFinite (sourceWriteWord state (continuation + 32) 1)) := by
  have address : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.op .add [.var .global (ofString "cur_cont"),.const 32]) =
        some (.val (.word (continuation + 32))) := by
    simp [evalHOLExact,evalListHOLExact,contGlobal,wordOpHOL,wordOp,valueIsWord,valueWord]
  have store := evaluate_store_word state (continuation + 32) 1 _ (.const 1) address (by rfl) domain
  unfold frameExceptionPendingTail
  apply evaluate_seq_none store
  simp [evaluateHOLFiniteState_return,evalHOLExact,shapeOfHOLExact]

/-- A pending continuation selects finalization without reading the active
flag or opcode, including when gas exhaustion caused the pending condition. -/
theorem evaluate_runFrames_pending_precheck {F : Type} (state : PanSemStateFiniteExact 64 F)
    (continuation pending old : BitVec 64)
    (contGlobal : state.globals.lookup (ofString "cur_cont") = some (.val (.word continuation)))
    (domain : state.memaddrs (continuation + 32))
    (memory : state.memory (continuation + 32) = .word pending) (nonzero : pending ≠ 0)
    (doneLocal : state.locals.lookup (ofString "done") = some (.val (.word old))) :
    evaluateHOLFiniteState state runFramesPrecheck =
      (none,setVarHOLFinite (ofString "done") (.val (.word 1)) state) := by
  unfold runFramesPrecheck
  rw [evaluate_loaded_word_ite state (continuationLoad 32) pending 0 .notEqual
    (eval_continuationLoad state continuation 32 pending contGlobal domain memory)]
  have nonzeroLiteral : pending ≠ (0#64) := nonzero
  simpa [Compiler.Encoders.Asm.wordCmpHOL,nonzeroLiteral] using
    evaluate_runFrames_set_done state old doneLocal

/-- Compose the actual refill and error-work executions with the mandatory
pending store. The resulting flag forces finalization on the next iteration. -/
theorem evaluate_frameException_marks_pending {F : Type}
    (state refilled handled : PanSemStateFiniteExact 64 F) (continuation : BitVec 64)
    (refill : evaluateHOLFiniteState state
      (.call (some (none,none)) (ofString "refill_frame_state_gas") []) = (none,refilled))
    (work : evaluateHOLFiniteState refilled frameExceptionWork = (none,handled))
    (contGlobal : handled.globals.lookup (ofString "cur_cont") = some (.val (.word continuation)))
    (domain : handled.memaddrs (continuation + 32)) :
    ∃ post, evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_frame_exception) =
        (some (.returned (.val (.word 0))),post) ∧
      post.memory (continuation + 32) = .word 1 ∧ post.clock = handled.clock := by
  let post := emptyLocalsHOLFinite (sourceWriteWord handled (continuation + 32) 1)
  have tail := evaluate_frameException_pending_tail handled continuation contGlobal domain
  have body := evaluate_seq_none refill (evaluate_seq_none work tail)
  refine ⟨post,?_,?_,rfl⟩
  · rw [source_frameException_body]; exact body
  · simp [post,emptyLocalsHOLFinite,sourceWriteWord]

#print axioms evaluate_frameException_marks_pending
#print axioms source_frameException_body
#print axioms evaluate_frameException_pending_tail
#print axioms evaluate_runFrames_pending_precheck
end InitECandidate.Runtime
