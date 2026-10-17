import InitECandidate.Runtime.RlpItemShortString
import InitECandidate.Runtime.RlpErrorChecks
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def rlpItemLongString : ProgHOL 64 :=
  match rlpItemAfterShortString with
  | .seq (.ite _ body _) _ => body
  | _ => .skip

def rlpItemLongBody : ProgHOL 64 :=
  match rlpItemLongString with
  | .dec _ _ _ body => body
  | _ => .skip

def rlpItemLongFinish : ProgHOL 64 :=
  match rlpItemLongBody with
  | .seq _ (.decCall _ _ _ _ body) => body
  | _ => .skip

def rlpItemLongChecks : List (ExpHOL 64 × BitVec 64) :=
  [(.cmp .notLower (.const 55) (.var .local (ofString "n")),5),
   (.cmp .lower (.op .sub [.op .sub [.var .local (ofString "len"),.const 1],.var .local (ofString "ll")])
     (.var .local (ofString "n")),3)]

def rlpItemLongReturn : ProgHOL 64 :=
  .return (.rstruct [.const 0,.op .add [.var .local (ofString "p"),.const 1,.var .local (ofString "ll")],
    .var .local (ofString "n"),.op .add [.const 1,.var .local (ofString "ll"),.var .local (ofString "n")]])

def rlpItemLongValue (pointer headerLength length : BitVec 64) : ValueHOL 64 :=
  .rStruct [.val (.word 0),.val (.word (pointer + (1 + headerLength))),
    .val (.word length),.val (.word (1 + (headerLength + length)))]

theorem source_rlpItem_long_finish : rlpItemLongFinish = rlpErrorChecks rlpItemLongChecks rlpItemLongReturn := by
  simp only [rlpItemLongFinish,rlpItemLongBody,rlpItemLongString,rlpItemAfterShortString,rlpItemAfterSingleByte,
    rlpItemAfterByte,rlpItemLongChecks,rlpItemLongReturn,rlpErrorChecks,List.foldr,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- The original long-string validation and return take at most one tick,
including malformed lengths. Passing checks return the exact four-word item. -/
theorem evaluate_rlpItem_long_finish {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer headerLength length : BitVec 64)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (headerLocal : state.locals.lookup (ofString "ll") = some (.val (.word headerLength)))
    (lengthLocal : state.locals.lookup (ofString "n") = some (.val (.word length)))
    (code : state.code = originalRuntimeCode) (ticks : 1 ≤ state.clock) :
    ∃ result post, evaluateHOLFiniteState state rlpItemLongFinish = (result,post) ∧
      state.clock ≤ post.clock + 1 ∧ post.clock ≤ state.clock ∧ result ≠ some .timeOut ∧ result ≠ none ∧
      (∀ value, result = some (.returned value) → value = rlpItemLongValue pointer headerLength length) ∧
      post.memory = state.memory ∧ post.globals = state.globals := by
  have returned : evaluateHOLFiniteState state rlpItemLongReturn =
      (some (.returned (rlpItemLongValue pointer headerLength length)),emptyLocalsHOLFinite state) := by
    simp [rlpItemLongReturn,rlpItemLongValue,evaluateHOLFiniteState_return,evalHOLExact,evalListHOLExact,
      pointerLocal,headerLocal,lengthLocal,wordOpHOL,wordOp,valueIsWord,valueWord,shapeOfHOLExact,sizeOfShapeWithContextHOL]
  obtain ⟨result,post,run,cases⟩ := evaluate_rlp_error_checks state rlpItemLongChecks rlpItemLongReturn code ticks
  rw [source_rlpItem_long_finish]
  refine ⟨result,post,run,?_⟩
  rcases cases with normal | terminal
  · have same := Prod.mk.inj (normal.symm.trans returned)
    obtain ⟨rfl,rfl⟩ := same
    refine ⟨by change state.clock ≤ state.clock + 1; omega,by rfl,by simp,by simp,?_,rfl,rfl⟩
    intro value equal
    simpa using equal.symm
  · obtain ⟨cost,remaining,noTimeout,stopped,noReturn,memory,globals⟩ := terminal
    exact ⟨cost,remaining,noTimeout,stopped,(by intro value equal; exact False.elim (noReturn value equal)),memory,globals⟩

#print axioms evaluate_rlpItem_long_finish
end InitECandidate.Runtime
