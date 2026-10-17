import InitECandidate.Runtime.RlpItemShortBody
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def rlpItemAfterShortString : ProgHOL 64 :=
  match rlpItemAfterSingleByte with
  | .seq _ body => body
  | _ => .skip

theorem source_rlpItem_short_string : rlpItemShortString =
    .dec (ofString "n") .one (.op .sub [.var .local (ofString "b"),.const 128]) rlpItemShortBody := by
  simp only [rlpItemShortString,rlpItemShortBody,rlpItemAfterSingleByte,rlpItemAfterByte,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem source_rlpItem_short_dispatch : rlpItemAfterSingleByte =
    .seq (.ite (.cmp .notLower (.const 183) (.var .local (ofString "b"))) rlpItemShortString .skip)
      rlpItemAfterShortString := by
  simp only [rlpItemAfterShortString,rlpItemShortString,rlpItemAfterSingleByte,rlpItemAfterByte,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- The actual short-string declaration restores the caller's old n binding
on all outcomes while retaining the exact return and one-tick bound. -/
theorem evaluate_rlpItem_short_string {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer header : BitVec 64)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (headerLocal : state.locals.lookup (ofString "b") = some (.val (.word header)))
    (code : state.code = originalRuntimeCode) (ticks : 1 ≤ state.clock) :
    ∃ result post, evaluateHOLFiniteState state rlpItemShortString = (result,post) ∧
      state.clock ≤ post.clock + 1 ∧ post.clock ≤ state.clock ∧ result ≠ some .timeOut ∧ result ≠ none ∧
      (∀ value, result = some (.returned value) → value = rlpItemShortValue pointer (header - 128)) ∧
      post.memory = state.memory ∧ post.globals = state.globals := by
  let entered := setVarHOLFinite (ofString "n") (.val (.word (header - 128))) state
  have atPointer : entered.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
    simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "n" ≠ ofString "p" by decide] using pointerLocal
  have atLength : entered.locals.lookup (ofString "n") = some (.val (.word (header - 128))) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  obtain ⟨result,post,run,cost,remaining,noTimeout,terminal,returned,memory,globals⟩ :=
    evaluate_rlpItem_short_body entered pointer (header - 128) atPointer atLength code ticks
  have initializer : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.op .sub [.var .local (ofString "b"),.const 128]) = some (.val (.word (header - 128))) := by
    simp [evalHOLExact,evalListHOLExact,headerLocal,wordOpHOL,wordOp,valueIsWord,valueWord]
  refine ⟨result,{post with locals := HolFiniteMapExact.resVarEq post.locals (ofString "n",state.locals.lookup (ofString "n"))},?_,cost,remaining,noTimeout,terminal,returned,memory,globals⟩
  rw [source_rlpItem_short_string,evaluateHOLFiniteState_dec_total]
  simp only [initializer,shapeOfHOLExact,shapeEqHOL,if_true]
  change (let result := evaluateHOLFiniteState entered rlpItemShortBody; _) = _
  rw [run]

/-- The real header comparisons select the complete short-string case and
its terminal result prevents every later long/list branch from executing. -/
theorem evaluate_rlpItem_short_after_load {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer header : BitVec 64)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (headerLocal : state.locals.lookup (ofString "b") = some (.val (.word header)))
    (lower : 128 ≤ header.toNat) (upper : header.toNat ≤ 183)
    (code : state.code = originalRuntimeCode) (ticks : 1 ≤ state.clock) :
    ∃ result post, evaluateHOLFiniteState state rlpItemAfterByte = (result,post) ∧
      state.clock ≤ post.clock + 1 ∧ post.clock ≤ state.clock ∧ result ≠ some .timeOut ∧ result ≠ none ∧
      (∀ value, result = some (.returned value) → value = rlpItemShortValue pointer (header - 128)) ∧
      post.memory = state.memory ∧ post.globals = state.globals := by
  have first : evaluateHOLFiniteState state
      (.ite (.cmp .lower (.var .local (ofString "b")) (.const 128))
        (.return (.rstruct [.const 0,.var .local (ofString "p"),.const 1,.const 1])) .skip) = (none,state) := by
    rw [evaluateHOLFiniteState_ite]
    simp [evalHOLExact,headerLocal,Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def,Nat.not_lt.mpr lower,evaluateHOLFiniteState_skip]
  have guard : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.cmp .notLower (.const 183) (.var .local (ofString "b"))) = some (.val (.word 1)) := by
    simp [evalHOLExact,headerLocal,Compiler.Encoders.Asm.wordCmpHOL,BitVec.le_def,upper]
  obtain ⟨result,post,run,cost,remaining,noTimeout,terminal,returned,memory,globals⟩ :=
    evaluate_rlpItem_short_string state pointer header pointerLocal headerLocal code ticks
  rw [source_rlpItem_single_byte,evaluateHOLFiniteState_seq_line780,first]
  dsimp only
  rw [source_rlpItem_short_dispatch,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,guard]
  simp only [show (1 : BitVec 64) ≠ 0 from by decide,if_false]
  rw [run]
  cases result with
  | none => exact False.elim (terminal rfl)
  | some stopped => exact ⟨some stopped,post,rfl,cost,remaining,noTimeout,terminal,returned,memory,globals⟩

#print axioms evaluate_rlpItem_short_string
#print axioms evaluate_rlpItem_short_after_load
end InitECandidate.Runtime
