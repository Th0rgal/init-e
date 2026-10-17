import InitECandidate.Runtime.RlpValidationInitialization
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Restoring the original four validator local scopes preserves the globals
produced by the actual loop-and-return execution. -/
theorem evaluate_rlpValidation_initialized_loop_globals {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer length : BitVec 64) (result : Option (PanSemResultExact 64))
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (lengthLocal : state.locals.lookup (ofString "len") = some (.val (.word length)))
    (run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn__rlp_validate_items_body) = (result,post)) :
    ∃ output, evaluateHOLFiniteState (rlpValidationInitialState state pointer length) rlpValidationLoopAndReturn = (result,output) ∧
      post.globals = output.globals := by
  rw [source_rlpValidation_initialization] at run
  obtain ⟨out1,run1,restore1⟩ := evaluate_dec_word_result_scope state post (ofString "top") (.const 0) 0 _ result (by rfl) run
  let first := setVarHOLFinite (ofString "top") (.val (.word 0)) state
  have atPointer : first.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
    simpa [first,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "top" ≠ ofString "p" by decide] using pointerLocal
  obtain ⟨out2,run2,restore2⟩ := evaluate_dec_word_result_scope first out1 (ofString "pos") (.var .local (ofString "p")) pointer _ result
    (by simpa [evalHOLExact] using atPointer) run1
  let second := setVarHOLFinite (ofString "pos") (.val (.word pointer)) first
  have p : second.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
    simpa [second,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "pos" ≠ ofString "p" by decide] using atPointer
  have n : second.locals.lookup (ofString "len") = some (.val (.word length)) := by
    simpa [second,first,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "pos" ≠ ofString "len" by decide,show ofString "top" ≠ ofString "len" by decide] using lengthLocal
  have addition : @evalHOLExact 64 F _ second.toExact (fun address => Classical.propDecidable (second.memaddrs address))
      (.op .add [.var .local (ofString "p"),.var .local (ofString "len")]) = some (.val (.word (pointer + length))) := by
    simp [evalHOLExact,evalListHOLExact,p,n,wordOpHOL,wordOp,valueIsWord,valueWord]
  obtain ⟨out3,run3,restore3⟩ := evaluate_dec_word_result_scope second out2 (ofString "end")
    (.op .add [.var .local (ofString "p"),.var .local (ofString "len")]) (pointer + length) _ result addition run2
  obtain ⟨output,bodyRun,restore4⟩ := evaluate_dec_word_result_scope _ out3 (ofString "go") (.const 1) 1 _ result (by rfl) run3
  refine ⟨output,bodyRun,?_⟩
  rw [restore1,restore2,restore3,restore4]

#print axioms evaluate_rlpValidation_initialized_loop_globals
end InitECandidate.Runtime
