import InitECandidate.Runtime.RlpValidationIntervals
import InitECandidate.Runtime.PanDecWordResultScope
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def rlpValidationLoopAndReturn : ProgHOL 64 :=
  match sourceFunctionBody Guest.guestFn__rlp_validate_items_body with
  | .dec _ _ _ (.dec _ _ _ (.dec _ _ _ (.dec _ _ _ body))) => body
  | _ => .skip

theorem source_rlpValidation_initialization : sourceFunctionBody Guest.guestFn__rlp_validate_items_body =
    .dec (ofString "top") .one (.const 0)
      (.dec (ofString "pos") .one (.var .local (ofString "p"))
        (.dec (ofString "end") .one (.op .add [.var .local (ofString "p"),.var .local (ofString "len")])
          (.dec (ofString "go") .one (.const 1) rlpValidationLoopAndReturn))) := by
  simp only [rlpValidationLoopAndReturn,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem source_rlpValidation_loop_and_return : rlpValidationLoopAndReturn =
    .seq (.while (.cmp .notEqual (.var .local (ofString "go")) (.const 0)) rlpValidationStep)
      (.return (.const 0)) := by
  simp only [rlpValidationLoopAndReturn,rlpValidationStep,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

noncomputable def rlpValidationInitialState {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer length : BitVec 64) : PanSemStateFiniteExact 64 F :=
  setVarHOLFinite (ofString "go") (.val (.word 1))
    (setVarHOLFinite (ofString "end") (.val (.word (pointer + length)))
      (setVarHOLFinite (ofString "pos") (.val (.word pointer))
        (setVarHOLFinite (ofString "top") (.val (.word 0)) state)))

/-- The original local initializers establish an empty stack, the supplied
input interval and an enabled loop without changing clock or memory. -/
theorem rlpValidation_initial_state {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer length : BitVec 64) (noWrap : pointer.toNat + length.toNat < 2^64) :
    let initial := rlpValidationInitialState state pointer length
    initial.locals.lookup (ofString "top") = some (.val (.word 0)) ∧
      initial.locals.lookup (ofString "pos") = some (.val (.word pointer)) ∧
      initial.locals.lookup (ofString "end") = some (.val (.word (pointer + length))) ∧
      initial.locals.lookup (ofString "go") = some (.val (.word 1)) ∧
      RlpValidationStack initial.memory 0 [] ∧ RlpValidationIntervals pointer (pointer + length) [] ∧
      rlpValidationRank pointer (pointer + length) [] = 2 * length.toNat ∧
      initial.clock = state.clock ∧ initial.memory = state.memory := by
  have intervals := rlpValidation_intervals_initial pointer length noWrap
  refine ⟨?_,?_,?_,?_,.nil,intervals.1,intervals.2,rfl,rfl⟩
  all_goals simp [rlpValidationInitialState,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
    show ofString "go" ≠ ofString "top" by decide,show ofString "end" ≠ ofString "top" by decide,
    show ofString "pos" ≠ ofString "top" by decide,show ofString "go" ≠ ofString "pos" by decide,
    show ofString "end" ≠ ofString "pos" by decide,show ofString "go" ≠ ofString "end" by decide]

/-- Inverting the actual four declaration scopes exposes the real initialized
loop execution and preserves its clock/memory result through scope restoration. -/
theorem evaluate_rlpValidation_initialized_loop {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer length : BitVec 64) (result : Option (PanSemResultExact 64))
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (lengthLocal : state.locals.lookup (ofString "len") = some (.val (.word length)))
    (run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn__rlp_validate_items_body) = (result,post)) :
    ∃ output, evaluateHOLFiniteState (rlpValidationInitialState state pointer length) rlpValidationLoopAndReturn = (result,output) ∧
      post.clock = output.clock ∧ post.memory = output.memory := by
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
  refine ⟨output,bodyRun,?_,?_⟩
  · rw [restore1,restore2,restore3,restore4]
  · rw [restore1,restore2,restore3,restore4]

#print axioms rlpValidation_initial_state
#print axioms evaluate_rlpValidation_initialized_loop
end InitECandidate.Runtime
