import InitECandidate.Runtime.RlpHeaderShortListContract
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def rlpHeaderLongList : ProgHOL 64 := rlpHeaderAfterShortList

def rlpHeaderLongListBody : ProgHOL 64 :=
  match rlpHeaderLongList with | .dec _ _ _ body => body | _ => .skip

def rlpHeaderLongListRead : ProgHOL 64 :=
  match rlpHeaderLongListBody with | .seq _ body => body | _ => .skip

def rlpHeaderLongListFinish : ProgHOL 64 :=
  match rlpHeaderLongListRead with | .decCall _ _ _ _ body => body | _ => .skip

def rlpHeaderLongListReturn : ProgHOL 64 :=
  .return (.rstruct [.op .add [.const 1,.var .local (ofString "ll")],.var .local (ofString "n"),.const 1])

def rlpHeaderLongListValue (headerLength length : BitVec 64) : ValueHOL 64 :=
  .rStruct [.val (.word (1 + headerLength)),.val (.word length),.val (.word 1)]

theorem source_rlpHeader_long_list_finish : rlpHeaderLongListFinish =
    rlpErrorChecks rlpItemLongChecks rlpHeaderLongListReturn := by
  simp only [rlpHeaderLongListFinish,rlpHeaderLongListRead,rlpHeaderLongListBody,rlpHeaderLongList,
    rlpHeaderAfterShortList,rlpHeaderAfterLongString,rlpHeaderAfterShortString,rlpHeaderAfterSingle,
    rlpHeaderAfterByte,rlpItemLongChecks,rlpHeaderLongListReturn,rlpErrorChecks,List.foldr,
    sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- The original long-list header validation and return take at most one tick,
including malformed lengths. Passing checks return the exact three-word header. -/
theorem evaluate_rlpHeader_long_list_finish {F : Type} (state : PanSemStateFiniteExact 64 F)
    (headerLength length : BitVec 64)
    (headerLocal : state.locals.lookup (ofString "ll") = some (.val (.word headerLength)))
    (lengthLocal : state.locals.lookup (ofString "n") = some (.val (.word length)))
    (code : state.code = originalRuntimeCode) (ticks : 1 ≤ state.clock) :
    ∃ result post, evaluateHOLFiniteState state rlpHeaderLongListFinish = (result,post) ∧
      state.clock ≤ post.clock + 1 ∧ post.clock ≤ state.clock ∧ result ≠ some .timeOut ∧ result ≠ none ∧
      (∀ value, result = some (.returned value) → value = rlpHeaderLongListValue headerLength length) ∧
      post.memory = state.memory ∧ post.globals = state.globals := by
  have returned : evaluateHOLFiniteState state rlpHeaderLongListReturn =
      (some (.returned (rlpHeaderLongListValue headerLength length)),emptyLocalsHOLFinite state) := by
    simp [rlpHeaderLongListReturn,rlpHeaderLongListValue,evaluateHOLFiniteState_return,evalHOLExact,evalListHOLExact,
      headerLocal,lengthLocal,wordOpHOL,wordOp,valueIsWord,valueWord,shapeOfHOLExact,sizeOfShapeWithContextHOL]
  obtain ⟨result,post,run,cases⟩ := evaluate_rlp_error_checks state rlpItemLongChecks rlpHeaderLongListReturn code ticks
  rw [source_rlpHeader_long_list_finish]
  refine ⟨result,post,run,?_⟩
  rcases cases with normal | terminal
  · have same := Prod.mk.inj (normal.symm.trans returned)
    obtain ⟨rfl,rfl⟩ := same
    refine ⟨by change state.clock ≤ state.clock + 1; omega,by rfl,by simp,by simp,?_,rfl,rfl⟩
    intro value equal
    simpa using equal.symm
  · obtain ⟨cost,remaining,noTimeout,stopped,noReturn,memory,globals⟩ := terminal
    exact ⟨cost,remaining,noTimeout,stopped,(by intro value equal; exact False.elim (noReturn value equal)),memory,globals⟩

#print axioms evaluate_rlpHeader_long_list_finish
end InitECandidate.Runtime
