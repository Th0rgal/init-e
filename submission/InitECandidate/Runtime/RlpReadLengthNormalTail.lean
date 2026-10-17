import InitECandidate.Runtime.RlpReadLengthStepAgreement
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Normal completion of an enabled reader loop exposes the actual byte read
and the remaining normal loop after its exact shift/or and index updates. -/
theorem rlpReadLength_loop_normal_tail {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer index value length : BitVec 64)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (valueLocal : state.locals.lookup (ofString "v") = some (.val (.word value)))
    (lengthLocal : state.locals.lookup (ofString "n") = some (.val (.word length)))
    (enabled : index.toNat < length.toNat)
    (run : evaluateHOLFiniteState state rlpReadLengthLoop = (none,post)) :
    ∃ byte : UInt8,
      @panMemLoadByteHOL 64 _ state.memory state.memaddrs
        (fun address => Classical.propDecidable (state.memaddrs address)) state.be (pointer + index) = some byte ∧
      evaluateHOLFiniteState (rlpReadLengthStepState (decClockHOLFinite state) index value byte) rlpReadLengthLoop = (none,post) := by
  have guard : evalHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))) = some (.val (.word 1)) := by
    simp [evalHOLFinite,evalHOLExact,indexLocal,lengthLocal,Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def,enabled]
  rw [source_rlpReadLength_loop,evaluateHOLFiniteState_while_total,guard] at run
  dsimp only at run
  by_cases zero : state.clock = 0
  · simp [zero] at run
  · rw [if_neg zero] at run
    cases loaded : @panMemLoadByteHOL 64 _ state.memory state.memaddrs
        (fun address => Classical.propDecidable (state.memaddrs address)) state.be (pointer + index) with
    | none =>
      have failed : evaluateHOLFiniteState (decClockHOLFinite state) rlpReadLengthStep = (some .error,decClockHOLFinite state) := by
        dsimp only [decClockHOLFinite]
        rw [source_rlpReadLength_step,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_assign]
        simp [evalHOLExact,evalListHOLExact,pointerLocal,indexLocal,valueLocal,wordShiftHOL,
          wordOpHOL,wordOp,valueIsWord,valueWord,loaded]
      rw [failed] at run
      simp [fixClockHOLFinite] at run
    | some byte =>
      have step := evaluate_rlpReadLength_step_loaded (decClockHOLFinite state) pointer index value pointerLocal indexLocal valueLocal byte loaded
      rw [step] at run
      refine ⟨byte,rfl,?_⟩
      rw [source_rlpReadLength_loop]
      simpa [rlpReadLengthStepState,fixClockHOLFinite,setVarHOLFinite] using run

#print axioms rlpReadLength_loop_normal_tail
end InitECandidate.Runtime
