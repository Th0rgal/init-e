import InitECandidate.Runtime.RlpHeaderLongStringBodyContract
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem source_rlpHeader_long_string : rlpHeaderLongString =
    .dec (ofString "ll") .one (.op .sub [.var .local (ofString "b"),.const 183]) rlpHeaderLongStringBody := by
  simp only [rlpHeaderLongString,rlpHeaderLongStringBranch,rlpHeaderLongStringBody,
    rlpHeaderAfterShortString,rlpHeaderAfterSingle,rlpHeaderAfterByte,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- The real long-string header declaration has a uniform eleven-tick bound on
headers 184..191, including missing payload bytes and canonicality errors. -/
theorem evaluate_rlpHeader_long_string_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer header : BitVec 64)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (headerLocal : state.locals.lookup (ofString "b") = some (.val (.word header)))
    (lower : 183 < header.toNat) (upper : header.toNat ≤ 191)
    (code : state.code = originalRuntimeCode) (ticks : 11 ≤ state.clock) :
    ∃ result post, evaluateHOLFiniteState state rlpHeaderLongString = (result,post) ∧
      state.clock ≤ post.clock + 11 ∧ post.clock ≤ state.clock ∧ result ≠ some .timeOut := by
  have sizeBound := (rlp_header_length_bytes header 183 lower upper).2
  let entered := setVarHOLFinite (ofString "ll") (.val (.word (header - 183))) state
  have atPointer : entered.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
    simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "ll" ≠ ofString "p" by decide] using pointerLocal
  have atLength : entered.locals.lookup (ofString "ll") = some (.val (.word (header - 183))) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have bound := evaluate_rlpHeader_long_string_body_bounded entered pointer (header - 183) atPointer atLength code
    (by change (header - 183).toNat + 3 ≤ state.clock; omega)
  generalize bodyRun : evaluateHOLFiniteState entered rlpHeaderLongStringBody = evaluated at bound
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
  rw [source_rlpHeader_long_string,evaluateHOLFiniteState_dec_total]
  simp only [initializer,shapeOfHOLExact,shapeEqHOL,if_true]
  change (let result := evaluateHOLFiniteState entered rlpHeaderLongStringBody; _) = _
  rw [bodyRun]

/-- Neither failure nor successful parsing falls through the original long
string declaration, so later RLP list branches cannot execute. -/
theorem evaluate_rlpHeader_long_string_terminal {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer header : BitVec 64)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (headerLocal : state.locals.lookup (ofString "b") = some (.val (.word header)))
    (lower : 183 < header.toNat) (upper : header.toNat ≤ 191)
    (code : state.code = originalRuntimeCode) (ticks : 11 ≤ state.clock) :
    (evaluateHOLFiniteState state rlpHeaderLongString).1 ≠ none := by
  intro normal
  cases run : evaluateHOLFiniteState state rlpHeaderLongString with
  | mk result post =>
    rw [run] at normal
    change result = none at normal
    subst result
    have initializer : @evalHOLExact 64 F _ state.toExact
        (fun address => Classical.propDecidable (state.memaddrs address))
        (.op .sub [.var .local (ofString "b"),.const 183]) = some (.val (.word (header - 183))) := by
      simp [evalHOLExact,evalListHOLExact,headerLocal,wordOpHOL,wordOp,valueIsWord,valueWord]
    rw [source_rlpHeader_long_string] at run
    obtain ⟨output,bodyRun,_⟩ := evaluate_dec_word_result_scope state post (ofString "ll")
      (.op .sub [.var .local (ofString "b"),.const 183]) (header - 183) rlpHeaderLongStringBody none initializer run
    let entered := setVarHOLFinite (ofString "ll") (.val (.word (header - 183))) state
    have atPointer : entered.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
      simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
        show ofString "ll" ≠ ofString "p" by decide] using pointerLocal
    have atLength : entered.locals.lookup (ofString "ll") = some (.val (.word (header - 183))) := by
      simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
    have sizeBound := (rlp_header_length_bytes header 183 lower upper).2
    have terminal := evaluate_rlpHeader_long_string_body_terminal entered pointer (header - 183) atPointer atLength code
      (by change (header - 183).toNat + 3 ≤ state.clock; omega)
    rw [bodyRun] at terminal
    exact terminal rfl

/-- Successful evaluation of the original long-string header branch consumes a
positive prefix bounded by the input, with a strictly smaller payload. -/
theorem rlpHeader_long_string_return_contract {F : Type} (state final : PanSemStateFiniteExact 64 F)
    (pointer header total : BitVec 64) (value : ValueHOL 64)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (headerLocal : state.locals.lookup (ofString "b") = some (.val (.word header)))
    (totalLocal : state.locals.lookup (ofString "len") = some (.val (.word total)))
    (lower : 183 < header.toNat) (upper : header.toNat ≤ 191)
    (nonzero : total ≠ 0) (code : state.code = originalRuntimeCode) (ticks : 10 ≤ state.clock)
    (run : evaluateHOLFiniteState state rlpHeaderLongString = (some (.returned value),final)) :
    ∃ payload : BitVec 64, value = rlpHeaderLongStringValue (header - 183) payload ∧ payload.toNat < total.toNat ∧
      0 < (1 + ((header - 183) + payload)).toNat ∧
      (1 + ((header - 183) + payload)).toNat ≤ total.toNat := by
  have sizeBound := (rlp_header_length_bytes header 183 lower upper).2
  have initializer : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.op .sub [.var .local (ofString "b"),.const 183]) = some (.val (.word (header - 183))) := by
    simp [evalHOLExact,evalListHOLExact,headerLocal,wordOpHOL,wordOp,valueIsWord,valueWord]
  rw [source_rlpHeader_long_string] at run
  obtain ⟨output,bodyRun,_⟩ := evaluate_dec_word_result_scope state final (ofString "ll")
    (.op .sub [.var .local (ofString "b"),.const 183]) (header - 183) rlpHeaderLongStringBody
    (some (.returned value)) initializer run
  let entered := setVarHOLFinite (ofString "ll") (.val (.word (header - 183))) state
  have atPointer : entered.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
    simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "ll" ≠ ofString "p" by decide] using pointerLocal
  have atLength : entered.locals.lookup (ofString "ll") = some (.val (.word (header - 183))) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have atTotal : entered.locals.lookup (ofString "len") = some (.val (.word total)) := by
    simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "ll" ≠ ofString "len" by decide] using totalLocal
  exact rlpHeader_long_string_body_return_contract entered output pointer (header - 183) total value
    atPointer atLength atTotal nonzero code (by change (header - 183).toNat + 2 ≤ state.clock; omega) bodyRun

#print axioms evaluate_rlpHeader_long_string_bounded
#print axioms evaluate_rlpHeader_long_string_terminal
#print axioms rlpHeader_long_string_return_contract
end InitECandidate.Runtime
