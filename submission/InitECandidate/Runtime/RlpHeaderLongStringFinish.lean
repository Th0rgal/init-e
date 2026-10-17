import InitECandidate.Runtime.RlpHeaderShortListDispatch
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def rlpHeaderLongString : ProgHOL 64 := rlpHeaderLongStringBranch

def rlpHeaderLongStringBody : ProgHOL 64 :=
  match rlpHeaderLongString with | .dec _ _ _ body => body | _ => .skip

def rlpHeaderLongStringRead : ProgHOL 64 :=
  match rlpHeaderLongStringBody with | .seq _ body => body | _ => .skip

def rlpHeaderLongStringFinish : ProgHOL 64 :=
  match rlpHeaderLongStringRead with | .decCall _ _ _ _ body => body | _ => .skip

def rlpHeaderLongStringReturn : ProgHOL 64 :=
  .return (.rstruct [.op .add [.const 1,.var .local (ofString "ll")],.var .local (ofString "n"),.const 0])

def rlpHeaderLongStringValue (headerLength length : BitVec 64) : ValueHOL 64 :=
  .rStruct [.val (.word (1 + headerLength)),.val (.word length),.val (.word 0)]

theorem source_rlpHeader_long_string_finish : rlpHeaderLongStringFinish =
    rlpErrorChecks rlpItemLongChecks rlpHeaderLongStringReturn := by
  simp only [rlpHeaderLongStringFinish,rlpHeaderLongStringRead,rlpHeaderLongStringBody,rlpHeaderLongString,rlpHeaderLongStringBranch,
    rlpHeaderAfterShortString,rlpHeaderAfterSingle,
    rlpHeaderAfterByte,rlpItemLongChecks,rlpHeaderLongStringReturn,rlpErrorChecks,List.foldr,
    sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- The original long-string header validation and return take at most one tick,
including malformed lengths. Passing checks return the exact three-word header. -/
theorem evaluate_rlpHeader_long_string_finish {F : Type} (state : PanSemStateFiniteExact 64 F)
    (headerLength length : BitVec 64)
    (headerLocal : state.locals.lookup (ofString "ll") = some (.val (.word headerLength)))
    (lengthLocal : state.locals.lookup (ofString "n") = some (.val (.word length)))
    (code : state.code = originalRuntimeCode) (ticks : 1 ≤ state.clock) :
    ∃ result post, evaluateHOLFiniteState state rlpHeaderLongStringFinish = (result,post) ∧
      state.clock ≤ post.clock + 1 ∧ post.clock ≤ state.clock ∧ result ≠ some .timeOut ∧ result ≠ none ∧
      (∀ value, result = some (.returned value) → value = rlpHeaderLongStringValue headerLength length) ∧
      post.memory = state.memory ∧ post.globals = state.globals := by
  have returned : evaluateHOLFiniteState state rlpHeaderLongStringReturn =
      (some (.returned (rlpHeaderLongStringValue headerLength length)),emptyLocalsHOLFinite state) := by
    simp [rlpHeaderLongStringReturn,rlpHeaderLongStringValue,evaluateHOLFiniteState_return,evalHOLExact,evalListHOLExact,
      headerLocal,lengthLocal,wordOpHOL,wordOp,valueIsWord,valueWord,shapeOfHOLExact,sizeOfShapeWithContextHOL]
  obtain ⟨result,post,run,cases⟩ := evaluate_rlp_error_checks state rlpItemLongChecks rlpHeaderLongStringReturn code ticks
  rw [source_rlpHeader_long_string_finish]
  refine ⟨result,post,run,?_⟩
  rcases cases with normal | terminal
  · have same := Prod.mk.inj (normal.symm.trans returned)
    obtain ⟨rfl,rfl⟩ := same
    refine ⟨by change state.clock ≤ state.clock + 1; omega,by rfl,by simp,by simp,?_,rfl,rfl⟩
    intro value equal
    simpa using equal.symm
  · obtain ⟨cost,remaining,noTimeout,stopped,noReturn,memory,globals⟩ := terminal
    exact ⟨cost,remaining,noTimeout,stopped,(by intro value equal; exact False.elim (noReturn value equal)),memory,globals⟩

#print axioms evaluate_rlpHeader_long_string_finish
end InitECandidate.Runtime
