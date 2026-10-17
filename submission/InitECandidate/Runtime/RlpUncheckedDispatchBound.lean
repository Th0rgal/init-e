import InitECandidate.Runtime.RlpUncheckedLongDispatchBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem evaluate_rlpUnchecked_short_dispatch_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer header : BitVec 64)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (headerLocal : state.locals.lookup (ofString "b") = some (.val (.word header)))
    (upper : header.toNat ≤ 255) (code : state.code = originalRuntimeCode) (ticks : 10 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state rlpUncheckedAfterSingle
    state.clock ≤ evaluated.2.clock + 10 ∧ evaluated.2.clock ≤ state.clock ∧
      evaluated.1 ≠ some .timeOut ∧ evaluated.1 ≠ none := by
  by_cases short : header.toNat ≤ 183
  · have guard : @evalHOLExact 64 F _ state.toExact
        (fun address => Classical.propDecidable (state.memaddrs address))
        (.cmp .notLower (.const 183) (.var .local (ofString "b"))) = some (.val (.word 1)) := by
      simp [evalHOLExact,headerLocal,Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def,short]
    have returned : evaluateHOLFiniteState state (.return (.op .sub [.op .add [.const 1,.var .local (ofString "b")],.const 128])) =
        (some (.returned (.val (.word ((1 + header) - 128)))),emptyLocalsHOLFinite state) := by
      simp [evaluateHOLFiniteState_return,evalHOLExact,evalListHOLExact,headerLocal,
        wordOpHOL,wordOp,valueIsWord,valueWord,shapeOfHOLExact]
    rw [source_rlpUnchecked_short_string,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,guard]
    simp only [show (1 : BitVec 64) ≠ 0 from by decide,if_false,returned]
    exact ⟨by change state.clock ≤ state.clock + 10; omega,by rfl,by simp,by simp⟩
  · have guard : @evalHOLExact 64 F _ state.toExact
        (fun address => Classical.propDecidable (state.memaddrs address))
        (.cmp .notLower (.const 183) (.var .local (ofString "b"))) = some (.val (.word 0)) := by
      simp [evalHOLExact,headerLocal,Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def,short]
    rw [source_rlpUnchecked_short_string,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,guard]
    simp only [if_true,evaluateHOLFiniteState_skip]
    exact evaluate_rlpUnchecked_long_dispatch_bounded state pointer header pointerLocal headerLocal (by omega) upper code ticks

#print axioms evaluate_rlpUnchecked_short_dispatch_bounded
theorem evaluate_rlpUnchecked_after_load_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer header : BitVec 64)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (headerLocal : state.locals.lookup (ofString "b") = some (.val (.word header)))
    (upper : header.toNat ≤ 255) (code : state.code = originalRuntimeCode) (ticks : 10 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state rlpUncheckedAfterByte
    state.clock ≤ evaluated.2.clock + 10 ∧ evaluated.2.clock ≤ state.clock ∧
      evaluated.1 ≠ some .timeOut ∧ evaluated.1 ≠ none := by
  by_cases short : header.toNat < 128
  · have guard : @evalHOLExact 64 F _ state.toExact
        (fun address => Classical.propDecidable (state.memaddrs address))
        (.cmp .lower (.var .local (ofString "b")) (.const 128)) = some (.val (.word 1)) := by
      simp [evalHOLExact,headerLocal,Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def,short]
    have returned : evaluateHOLFiniteState state (.return (.const 1)) =
        (some (.returned (.val (.word (1 : BitVec 64)))),emptyLocalsHOLFinite state) := by
      simp [evaluateHOLFiniteState_return,evalHOLExact,shapeOfHOLExact]
    rw [source_rlpUnchecked_single,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,guard]
    simp only [show (1 : BitVec 64) ≠ 0 from by decide,if_false,returned]
    exact ⟨by change state.clock ≤ state.clock + 10; omega,by rfl,by simp,by simp⟩
  · have guard : @evalHOLExact 64 F _ state.toExact
        (fun address => Classical.propDecidable (state.memaddrs address))
        (.cmp .lower (.var .local (ofString "b")) (.const 128)) = some (.val (.word 0)) := by
      simp [evalHOLExact,headerLocal,Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def,short]
    rw [source_rlpUnchecked_single,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,guard]
    simp only [if_true,evaluateHOLFiniteState_skip]
    exact evaluate_rlpUnchecked_short_dispatch_bounded state pointer header pointerLocal headerLocal upper code ticks

#print axioms evaluate_rlpUnchecked_after_load_bounded
end InitECandidate.Runtime
