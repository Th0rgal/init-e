import InitECandidate.Runtime.RlpItemLongReadBound
import InitECandidate.Runtime.RlpHeaderLengthBounds
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem source_rlpItem_long_body : rlpItemLongBody =
    .seq (.ite (.cmp .lower (.op .sub [.var .local (ofString "len"),.const 1]) (.var .local (ofString "ll")))
      (.call (some (none,none)) (ofString "rlp_fail") [.const 3]) .skip) rlpItemLongRead := by
  simp only [rlpItemLongBody,rlpItemLongRead,rlpItemLongString,rlpItemAfterShortString,
    rlpItemAfterSingleByte,rlpItemAfterByte,sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem source_rlpItem_long_string : rlpItemLongString =
    .dec (ofString "ll") .one (.op .sub [.var .local (ofString "b"),.const 183]) rlpItemLongBody := by
  simp only [rlpItemLongString,rlpItemLongBody,rlpItemAfterShortString,rlpItemAfterSingleByte,
    rlpItemAfterByte,sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- The outer length-of-length availability check adds no ticks on its
passing path and exits within one tick on every other evaluated outcome. -/
theorem evaluate_rlpItem_long_body_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer headerLength : BitVec 64)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (headerLocal : state.locals.lookup (ofString "ll") = some (.val (.word headerLength)))
    (code : state.code = originalRuntimeCode) (ticks : headerLength.toNat + 3 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state rlpItemLongBody
    state.clock ≤ evaluated.2.clock + (headerLength.toNat + 3) ∧
      evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  obtain ⟨result,post,run,cost,remaining,noTimeout,normal,_,_,_⟩ := evaluate_rlp_error_check state
    (.cmp .lower (.op .sub [.var .local (ofString "len"),.const 1]) (.var .local (ofString "ll"))) 3 code (by omega)
  rw [source_rlpItem_long_body,evaluateHOLFiniteState_seq_line780,run]
  cases result with
  | none =>
    have same := normal rfl
    subst post
    exact evaluate_rlpItem_long_read_bounded state pointer headerLength pointerLocal headerLocal code ticks
  | some stopped =>
    exact ⟨by change state.clock ≤ post.clock + (headerLength.toNat + 3); omega,remaining,noTimeout⟩

/-- The real long-string declaration has a uniform eleven-tick bound on
headers 184..191, including missing payload bytes and canonicality errors. -/
theorem evaluate_rlpItem_long_string_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer header : BitVec 64)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (headerLocal : state.locals.lookup (ofString "b") = some (.val (.word header)))
    (lower : 183 < header.toNat) (upper : header.toNat ≤ 191)
    (code : state.code = originalRuntimeCode) (ticks : 11 ≤ state.clock) :
    ∃ result post, evaluateHOLFiniteState state rlpItemLongString = (result,post) ∧
      state.clock ≤ post.clock + 11 ∧ post.clock ≤ state.clock ∧ result ≠ some .timeOut := by
  have sizeBound := (rlp_long_string_length_bytes header lower upper).2
  let entered := setVarHOLFinite (ofString "ll") (.val (.word (header - 183))) state
  have atPointer : entered.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
    simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "ll" ≠ ofString "p" by decide] using pointerLocal
  have atLength : entered.locals.lookup (ofString "ll") = some (.val (.word (header - 183))) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have bound := evaluate_rlpItem_long_body_bounded entered pointer (header - 183) atPointer atLength code
    (by change (header - 183).toNat + 3 ≤ state.clock; omega)
  generalize bodyRun : evaluateHOLFiniteState entered rlpItemLongBody = evaluated at bound
  obtain ⟨result,post⟩ := evaluated
  obtain ⟨cost,remaining,noTimeout⟩ := bound
  dsimp only at cost remaining noTimeout
  have initializer : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.op .sub [.var .local (ofString "b"),.const 183]) = some (.val (.word (header - 183))) := by
    simp [evalHOLExact,evalListHOLExact,headerLocal,wordOpHOL,wordOp,valueIsWord,valueWord]
  let final := {post with locals := HolFiniteMapExact.resVarEq post.locals (ofString "ll",state.locals.lookup (ofString "ll"))}
  have entryClock : entered.clock = state.clock := rfl
  refine ⟨result,final,?_,by change state.clock ≤ post.clock + 11; omega,remaining,noTimeout⟩
  rw [source_rlpItem_long_string,evaluateHOLFiniteState_dec_total]
  simp only [initializer,shapeOfHOLExact,shapeEqHOL,if_true]
  change (let result := evaluateHOLFiniteState entered rlpItemLongBody; _) = _
  rw [bodyRun]

#print axioms evaluate_rlpItem_long_body_bounded
#print axioms evaluate_rlpItem_long_string_bounded
end InitECandidate.Runtime
