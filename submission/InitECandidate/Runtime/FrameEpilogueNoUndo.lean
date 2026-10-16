import InitECandidate.Runtime.FrameEpilogue
import InitECandidate.Runtime.StateRestoreDoneCall
import InitECandidate.Runtime.OriginalFrameEpilogueCode
import InitECandidate.Runtime.PanNoArgsLookup
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A failed-frame epilogue with no journal entries beyond its snapshot
executes the real restore call and returns after one body clock. -/
theorem evaluate_frameEpilogue_noUndo_body {F : Type} (state : PanSemStateFiniteExact 64 F)
    (frame continuation error count snapshot : BitVec 64)
    (code : state.code = originalRuntimeCode) (clock : state.clock ≠ 0)
    (frameGlobal : state.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (contGlobal : state.globals.lookup (ofString "cur_cont") = some (.val (.word continuation)))
    (countGlobal : state.globals.lookup (ofString "journal_n") = some (.val (.word count)))
    (errorDomain : state.memaddrs (frame + 160)) (errorMemory : state.memory (frame + 160) = .word error)
    (snapshotDomain : state.memaddrs (continuation + 24))
    (snapshotMemory : state.memory (continuation + 24) = .word snapshot)
    (failed : error ≠ 0) (done : count.toNat ≤ snapshot.toNat) :
    evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_frame_epilogue) =
      (some (.returned (.val (.word 0))),emptyLocalsHOLFinite {state with clock := state.clock - 1}) := by
  have arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) [continuationLoad 24] =
        some [.val (.word snapshot)] := by
    simp only [evalListHOLFinite,evalListHOLExact]
    rw [eval_continuationLoad state continuation 24 snapshot contGlobal snapshotDomain snapshotMemory]
  have restore := evaluate_stateRestore_done_call state (continuationLoad 24) count snapshot arguments code clock countGlobal done
  rw [source_frameEpilogue_body,evaluateHOLFiniteState_seq_line780]
  rw [evaluate_loaded_word_ite state (fundingLoad 160) error 0 .notEqual
    (eval_fundingLoad state frame 160 error frameGlobal errorDomain errorMemory)]
  have flag : Compiler.Encoders.Asm.wordCmpHOL .notEqual error 0 = true := by
    have failedLiteral : error ≠ (0#64) := failed
    simp [Compiler.Encoders.Asm.wordCmpHOL,failedLiteral]
  rw [if_pos flag,restore]
  simp [evaluateHOLFiniteState_return,evalHOLExact,shapeOfHOLExact]

/-- Including epilogue entry, a failed frame with no undo work costs two
clocks and preserves memory and caller bindings. -/
theorem evaluate_frameEpilogue_noUndo_call {F : Type} (state : PanSemStateFiniteExact 64 F)
    (frame continuation error count snapshot : BitVec 64)
    (code : state.code = originalRuntimeCode) (clock : 2 ≤ state.clock)
    (frameGlobal : state.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (contGlobal : state.globals.lookup (ofString "cur_cont") = some (.val (.word continuation)))
    (countGlobal : state.globals.lookup (ofString "journal_n") = some (.val (.word count)))
    (errorDomain : state.memaddrs (frame + 160)) (errorMemory : state.memory (frame + 160) = .word error)
    (snapshotDomain : state.memaddrs (continuation + 24))
    (snapshotMemory : state.memory (continuation + 24) = .word snapshot)
    (failed : error ≠ 0) (done : count.toNat ≤ snapshot.toNat) :
    evaluateHOLFiniteState state (.call (some (none,none)) (ofString "frame_epilogue") []) =
      (none,{state with clock := state.clock - 2}) := by
  let entry := callEntryStateHOLFinite state HolFiniteMapExact.empty
  have body := evaluate_frameEpilogue_noUndo_body entry frame continuation error count snapshot code
    (by change state.clock - 1 ≠ 0; omega) frameGlobal contGlobal countGlobal errorDomain errorMemory
    snapshotDomain snapshotMemory failed done
  have installed : state.code.lookup (ofString "frame_epilogue") =
      some ([],sourceFunctionBody Guest.guestFn_frame_epilogue,.one) := by
    rw [code]; exact originalRuntimeCode_frameEpilogue_lookup
  have lookup := pan_no_args_lookup state.code.lookup (ofString "frame_epilogue")
    (sourceFunctionBody Guest.guestFn_frame_epilogue) installed
  have call := evaluateHOLFiniteState_call_return_caller_locals state none (ofString "frame_epilogue") [] []
    (sourceFunctionBody Guest.guestFn_frame_epilogue) HolFiniteMapExact.empty .one (.val (.word 0))
    (emptyLocalsHOLFinite {entry with clock := entry.clock - 1})
    (by simp [evalListHOLFinite,evalListHOLExact]) lookup (by omega) body (by simp [shapeOfHOLExact,shapeEqHOL])
  simpa only [entry,callEntryStateHOLFinite,emptyLocalsHOLFinite,Nat.sub_sub] using call

#print axioms evaluate_frameEpilogue_noUndo_body
#print axioms evaluate_frameEpilogue_noUndo_call
end InitECandidate.Runtime
