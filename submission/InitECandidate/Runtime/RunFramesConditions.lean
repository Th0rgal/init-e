import InitECandidate.Runtime.RunFramesSyntax
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem eval_continuationLoad {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer offset value : BitVec 64)
    (global : state.globals.lookup (ofString "cur_cont") = some (.val (.word pointer)))
    (domain : state.memaddrs (pointer + offset))
    (memory : state.memory (pointer + offset) = .word value) :
    @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) (continuationLoad offset) =
      some (.val (.word value)) := by
  classical
  simp [continuationLoad, evalHOLExact, evalListHOLExact, toExact, global,
    wordOpHOL, wordOp, valueIsWord, valueWord, isWfShapeExactHOL,
    memLoadHOLExact, domain, memory]

/-- A comparison between successfully loaded words only selects a branch. -/
theorem evaluate_loaded_word_ite {F : Type} (state : PanSemStateFiniteExact 64 F)
    (expression : ExpHOL 64) (value bound : BitVec 64) (operator : Cmp)
    (loaded : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) expression =
        some (.val (.word value))) (yes no : ProgHOL 64) :
    evaluateHOLFiniteState state (.ite (.cmp operator expression (.const bound)) yes no) =
      if Compiler.Encoders.Asm.wordCmpHOL operator value bound then
        evaluateHOLFiniteState state yes else evaluateHOLFiniteState state no := by
  classical
  cases flag : Compiler.Encoders.Asm.wordCmpHOL operator value bound <;>
    simp [evaluateHOLFiniteState_ite, evalHOLExact, loaded, flag]

/-- With no pending continuation and a live frame, the actual precheck reaches
    the source program's PC test and opcode dispatch. -/
theorem evaluate_runFrames_running_precheck {F : Type} (state : PanSemStateFiniteExact 64 F)
    (continuation frame active : BitVec 64)
    (contGlobal : state.globals.lookup (ofString "cur_cont") = some (.val (.word continuation)))
    (frameGlobal : state.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (pendingDomain : state.memaddrs (continuation + 32))
    (pendingMemory : state.memory (continuation + 32) = .word 0)
    (activeDomain : state.memaddrs (frame + 104))
    (activeMemory : state.memory (frame + 104) = .word active)
    (running : active ≠ 0) :
    evaluateHOLFiniteState state runFramesPrecheck =
      evaluateHOLFiniteState state runFramesRunningDispatch := by
  classical
  unfold runFramesPrecheck
  rw [evaluate_loaded_word_ite state (continuationLoad 32) 0 0 .notEqual
    (eval_continuationLoad state continuation 32 0 contGlobal pendingDomain pendingMemory)]
  simp only [Compiler.Encoders.Asm.wordCmpHOL]
  rw [evaluate_loaded_word_ite state (fundingLoad 104) active 0 .equal
    (eval_fundingLoad state frame 104 active frameGlobal activeDomain activeMemory)]
  have runningLiteral : active ≠ (0#64) := running
  simp [Compiler.Encoders.Asm.wordCmpHOL, runningLiteral]

#print axioms eval_continuationLoad
#print axioms evaluate_loaded_word_ite
#print axioms evaluate_runFrames_running_precheck
end InitECandidate.Runtime
