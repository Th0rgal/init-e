import InitECandidate.Runtime.RlpItemShortCanonical
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def rlpItemShortReturn : ProgHOL 64 :=
  .return (.rstruct [.const 0,.op .add [.var .local (ofString "p"),.const 1],
    .var .local (ofString "n"),.op .add [.const 1,.var .local (ofString "n")]])

def rlpItemShortValue (pointer length : BitVec 64) : ValueHOL 64 :=
  .rStruct [.val (.word 0),.val (.word (pointer + 1)),.val (.word length),.val (.word (1 + length))]

theorem source_rlpItem_short_body : rlpItemShortBody =
    .seq (.ite (.cmp .lower (.op .sub [.var .local (ofString "len"),.const 1]) (.var .local (ofString "n")))
      (.call (some (none,none)) (ofString "rlp_fail") [.const 3]) .skip)
      (.seq rlpItemShortCanonical rlpItemShortReturn) := by
  simp only [rlpItemShortBody,rlpItemShortString,rlpItemShortCanonical,rlpItemAfterSingleByte,rlpItemAfterByte,
    rlpItemShortReturn,sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- Both short-string checks and the exact item return use at most one
source tick: every passing check leaves its entire state unchanged. -/
theorem evaluate_rlpItem_short_body {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer length : BitVec 64)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (lengthLocal : state.locals.lookup (ofString "n") = some (.val (.word length)))
    (code : state.code = originalRuntimeCode) (ticks : 1 ≤ state.clock) :
    ∃ result post, evaluateHOLFiniteState state rlpItemShortBody = (result,post) ∧
      state.clock ≤ post.clock + 1 ∧ post.clock ≤ state.clock ∧ result ≠ some .timeOut ∧ result ≠ none ∧
      (∀ value, result = some (.returned value) → value = rlpItemShortValue pointer length) ∧
      post.memory = state.memory ∧ post.globals = state.globals := by
  have returned : evaluateHOLFiniteState state rlpItemShortReturn =
      (some (.returned (rlpItemShortValue pointer length)),emptyLocalsHOLFinite state) := by
    simp [rlpItemShortReturn,rlpItemShortValue,evaluateHOLFiniteState_return,evalHOLExact,evalListHOLExact,
      pointerLocal,lengthLocal,wordOpHOL,wordOp,valueIsWord,valueWord,shapeOfHOLExact,sizeOfShapeWithContextHOL]
  have tail : ∃ result post, evaluateHOLFiniteState state (.seq rlpItemShortCanonical rlpItemShortReturn) = (result,post) ∧
      state.clock ≤ post.clock + 1 ∧ post.clock ≤ state.clock ∧ result ≠ some .timeOut ∧ result ≠ none ∧
      (∀ value, result = some (.returned value) → value = rlpItemShortValue pointer length) ∧
      post.memory = state.memory ∧ post.globals = state.globals := by
    obtain ⟨result,post,run,cost,remaining,noTimeout,normal,noReturn,memory,globals⟩ :=
      evaluate_rlpItem_short_canonical state length lengthLocal code ticks
    rw [evaluateHOLFiniteState_seq_line780,run]
    cases result with
    | none =>
      have same := normal rfl
      subst post
      dsimp only
      rw [returned]
      refine ⟨_,_,rfl,by change state.clock ≤ state.clock + 1; omega,by rfl,by simp,by simp,?_,rfl,rfl⟩
      intro value equal
      simpa using equal.symm
    | some stopped =>
      exact ⟨some stopped,post,rfl,cost,remaining,noTimeout,by simp,
        (by intro value equal; exact False.elim (noReturn value equal)),memory,globals⟩
  obtain ⟨result,post,run,cost,remaining,noTimeout,normal,noReturn,memory,globals⟩ :=
    evaluate_rlp_error_check state
      (.cmp .lower (.op .sub [.var .local (ofString "len"),.const 1]) (.var .local (ofString "n"))) 3 code ticks
  rw [source_rlpItem_short_body,evaluateHOLFiniteState_seq_line780,run]
  cases result with
  | none =>
    have same := normal rfl
    subst post
    exact tail
  | some stopped =>
    exact ⟨some stopped,post,rfl,cost,remaining,noTimeout,by simp,
      (by intro value equal; exact False.elim (noReturn value equal)),memory,globals⟩

#print axioms evaluate_rlpItem_short_body
end InitECandidate.Runtime
