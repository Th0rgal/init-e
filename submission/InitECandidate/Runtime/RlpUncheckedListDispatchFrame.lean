import InitECandidate.Runtime.RlpUncheckedLongFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The final original unchecked dispatch either returns a short-list size
without ticks or executes the at-most-eight-byte long-list length reader. -/
theorem evaluate_rlpUnchecked_list_dispatch_frame {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer header : BitVec 64)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (headerLocal : state.locals.lookup (ofString "b") = some (.val (.word header)))
    (code : state.code = originalRuntimeCode) :
    let evaluated := evaluateHOLFiniteState state rlpUncheckedAfterLong
    evaluated.2.memory = state.memory ∧ evaluated.2.globals = state.globals := by
  by_cases short : header.toNat ≤ 247
  · have guard : @evalHOLExact 64 F _ state.toExact
        (fun address => Classical.propDecidable (state.memaddrs address))
        (.cmp .notLower (.const 247) (.var .local (ofString "b"))) = some (.val (.word 1)) := by
      simp [evalHOLExact,headerLocal,Compiler.Encoders.Asm.wordCmpHOL,BitVec.le_def,short]
    have returned : evaluateHOLFiniteState state
        (.return (.op .sub [.op .add [.const 1,.var .local (ofString "b")],.const 192])) =
        (some (.returned (.val (.word ((1 + header) - 192)))),emptyLocalsHOLFinite state) := by
      simp [evaluateHOLFiniteState_return,evalHOLExact,evalListHOLExact,headerLocal,
        wordOpHOL,wordOp,valueIsWord,valueWord,shapeOfHOLExact]
    rw [source_rlpUnchecked_short_list,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,guard]
    simp only [show (1 : BitVec 64) ≠ 0 from by decide,if_false,returned]
    exact ⟨rfl,rfl⟩
  · have guard : @evalHOLExact 64 F _ state.toExact
        (fun address => Classical.propDecidable (state.memaddrs address))
        (.cmp .notLower (.const 247) (.var .local (ofString "b"))) = some (.val (.word 0)) := by
      simp [evalHOLExact,headerLocal,Compiler.Encoders.Asm.wordCmpHOL,BitVec.le_def,short]
    have bound := evaluate_rlpUnchecked_long_list_frame state pointer header pointerLocal headerLocal code
    rw [source_rlpUnchecked_short_list,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,guard]
    simp only [if_true,evaluateHOLFiniteState_skip]
    exact bound

#print axioms evaluate_rlpUnchecked_list_dispatch_frame
end InitECandidate.Runtime
