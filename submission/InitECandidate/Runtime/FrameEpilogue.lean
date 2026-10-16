import InitECandidate.Runtime.RunFramesFinish
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Proofs.FrontendCodecComputation

/-- Epilogue for a successful frame does not restore a failed-frame snapshot. -/
theorem source_frameEpilogue_body : sourceFunctionBody Guest.guestFn_frame_epilogue =
    .seq (.ite (.cmp .notEqual (fundingLoad 160) (.const 0))
      (.call (some (none,none)) (ofString "state_restore") [continuationLoad 24]) .skip)
      (.return (.const 0)) := by
  unfold sourceFunctionBody
  rw [declToHOL_eq]
  simp only [Guest.guestFn_frame_epilogue,declToHOLStructural,funDeclToHOLStructural,
    progToHOLStructural,expToHOLStructural,expListToHOLStructural,shapeToHOLStructural,
    List.map_cons,List.map_nil,Option.map_none,fundingLoad,continuationLoad]
  rfl

theorem evaluate_frameEpilogue_success {F : Type} (state : PanSemStateFiniteExact 64 F)
    (frame : BitVec 64)
    (frameGlobal : state.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (domain : state.memaddrs (frame + 160))
    (memory : state.memory (frame + 160) = .word 0) :
    evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_frame_epilogue) =
      (some (.returned (.val (.word 0))),emptyLocalsHOLFinite state) := by
  rw [source_frameEpilogue_body,evaluateHOLFiniteState_seq_line780]
  rw [evaluate_loaded_word_ite state (fundingLoad 160) 0 0 .notEqual
    (eval_fundingLoad state frame 160 0 frameGlobal domain memory)]
  simp [Compiler.Encoders.Asm.wordCmpHOL,evaluateHOLFiniteState_skip,
    evaluateHOLFiniteState_return,evalHOLExact,shapeOfHOLExact]

#print axioms source_frameEpilogue_body
#print axioms evaluate_frameEpilogue_success
end InitECandidate.Runtime
