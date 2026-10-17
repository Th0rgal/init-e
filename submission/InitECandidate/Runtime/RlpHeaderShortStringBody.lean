import InitECandidate.Runtime.RlpHeaderShortListDispatch
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def rlpHeaderShortStringBody : ProgHOL 64 :=
  match rlpHeaderShortStringBranch with | .dec _ _ _ body => body | _ => .skip

def rlpHeaderShortStringReturn : ProgHOL 64 :=
  .return (.rstruct [.const 1,.var .local (ofString "n"),.const 0])

def rlpHeaderShortStringValue (length : BitVec 64) : ValueHOL 64 :=
  .rStruct [.val (.word 1),.val (.word length),.val (.word 0)]

theorem source_rlpHeader_short_string_body : rlpHeaderShortStringBody =
    .seq (.ite (.cmp .lower (.op .sub [.var .local (ofString "len"),.const 1]) (.var .local (ofString "n")))
      (.call (some (none,none)) (ofString "rlp_fail") [.const 3]) .skip)
      (.seq rlpItemShortCanonical rlpHeaderShortStringReturn) := by
  simp only [rlpHeaderShortStringBody,rlpHeaderShortStringBranch,rlpHeaderAfterSingle,rlpHeaderAfterByte,
    rlpItemShortCanonical,rlpItemShortBody,rlpItemShortString,rlpItemAfterSingleByte,rlpItemAfterByte,
    rlpHeaderShortStringReturn,sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- Both short-string checks and the exact item return use at most one
source tick: every passing check leaves its entire state unchanged. -/
theorem evaluate_rlpHeader_short_string_body {F : Type} (state : PanSemStateFiniteExact 64 F)
    (length : BitVec 64)
    (lengthLocal : state.locals.lookup (ofString "n") = some (.val (.word length)))
    (code : state.code = originalRuntimeCode) (ticks : 1 ≤ state.clock) :
    ∃ result post, evaluateHOLFiniteState state rlpHeaderShortStringBody = (result,post) ∧
      state.clock ≤ post.clock + 1 ∧ post.clock ≤ state.clock ∧ result ≠ some .timeOut ∧ result ≠ none ∧
      (∀ value, result = some (.returned value) → value = rlpHeaderShortStringValue length) ∧
      post.memory = state.memory ∧ post.globals = state.globals := by
  have returned : evaluateHOLFiniteState state rlpHeaderShortStringReturn =
      (some (.returned (rlpHeaderShortStringValue length)),emptyLocalsHOLFinite state) := by
    simp [rlpHeaderShortStringReturn,rlpHeaderShortStringValue,evaluateHOLFiniteState_return,evalHOLExact,evalListHOLExact,
      lengthLocal,shapeOfHOLExact,sizeOfShapeWithContextHOL]
  have tail : ∃ result post, evaluateHOLFiniteState state (.seq rlpItemShortCanonical rlpHeaderShortStringReturn) = (result,post) ∧
      state.clock ≤ post.clock + 1 ∧ post.clock ≤ state.clock ∧ result ≠ some .timeOut ∧ result ≠ none ∧
      (∀ value, result = some (.returned value) → value = rlpHeaderShortStringValue length) ∧
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
  rw [source_rlpHeader_short_string_body,evaluateHOLFiniteState_seq_line780,run]
  cases result with
  | none =>
    have same := normal rfl
    subst post
    exact tail
  | some stopped =>
    exact ⟨some stopped,post,rfl,cost,remaining,noTimeout,by simp,
      (by intro value equal; exact False.elim (noReturn value equal)),memory,globals⟩

#print axioms evaluate_rlpHeader_short_string_body
end InitECandidate.Runtime
