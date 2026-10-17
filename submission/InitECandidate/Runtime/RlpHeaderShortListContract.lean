import InitECandidate.Runtime.RlpHeaderShortList
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Exact original short-list header declaration contract, including malformed
inputs, read-only behavior and the bounds of every successful returned item. -/
theorem evaluate_rlpHeader_short_list_contract {F : Type} (state : PanSemStateFiniteExact 64 F)
    (header total : BitVec 64)
    (headerLocal : state.locals.lookup (ofString "b") = some (.val (.word header)))
    (totalLocal : state.locals.lookup (ofString "len") = some (.val (.word total)))
    (lower : 192 ≤ header.toNat) (upper : header.toNat ≤ 247)
    (nonzero : total ≠ 0) (code : state.code = originalRuntimeCode) (ticks : 1 ≤ state.clock) :
    ∃ result post, evaluateHOLFiniteState state rlpHeaderShortList = (result,post) ∧
      state.clock ≤ post.clock + 1 ∧ post.clock ≤ state.clock ∧ result ≠ some .timeOut ∧ result ≠ none ∧
      (∀ value, result = some (.returned value) →
        value = rlpHeaderShortListValue (header - 192) ∧
        (header - 192).toNat < total.toNat ∧ 0 < (1 + (header - 192)).toNat ∧
        (1 + (header - 192)).toNat ≤ total.toNat) ∧
      post.memory = state.memory ∧ post.globals = state.globals := by
  let entered := setVarHOLFinite (ofString "n") (.val (.word (header - 192))) state
  have atLength : entered.locals.lookup (ofString "n") = some (.val (.word (header - 192))) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  obtain ⟨result,output,bodyRun,cost,remaining,noTimeout,terminal,returned,memory,globals⟩ :=
    evaluate_rlpHeader_short_list_body entered (header - 192) atLength code ticks
  have initializer : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.op .sub [.var .local (ofString "b"),.const 192]) = some (.val (.word (header - 192))) := by
    simp [evalHOLExact,evalListHOLExact,headerLocal,wordOpHOL,wordOp,valueIsWord,valueWord]
  let post := {output with locals := HolFiniteMapExact.resVarEq output.locals (ofString "n",state.locals.lookup (ofString "n"))}
  have run : evaluateHOLFiniteState state rlpHeaderShortList = (result,post) := by
    rw [source_rlpHeader_short_list,evaluateHOLFiniteState_dec_total]
    simp only [initializer,shapeOfHOLExact,shapeEqHOL,if_true]
    change (let result := evaluateHOLFiniteState entered rlpHeaderShortListBody; _) = _
    rw [bodyRun]
  refine ⟨result,post,run,cost,remaining,noTimeout,terminal,?_,memory,globals⟩
  intro value equal
  exact ⟨returned value equal,rlpHeader_short_list_scoped_progress state post header total value
    headerLocal totalLocal lower upper nonzero code
    (by rw [run]; exact congrArg (fun result => (result,post)) equal)⟩

def rlpHeaderAfterShortList : ProgHOL 64 :=
  match rlpHeaderAfterLongString with | .seq _ body => body | _ => .skip

theorem source_rlpHeader_short_list_dispatch : rlpHeaderAfterLongString =
    .seq (.ite (.cmp .notLower (.const 247) (.var .local (ofString "b"))) rlpHeaderShortList .skip)
      rlpHeaderAfterShortList := by
  simp only [rlpHeaderAfterShortList,rlpHeaderShortList,rlpHeaderAfterLongString,rlpHeaderAfterShortString,
    rlpHeaderAfterSingle,rlpHeaderAfterByte,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- The real list-header dispatch selects the short-list contract and cannot
fall through into long-list parsing, including on malformed input. -/
theorem evaluate_rlpHeader_short_list_dispatch {F : Type} (state : PanSemStateFiniteExact 64 F)
    (header total : BitVec 64)
    (headerLocal : state.locals.lookup (ofString "b") = some (.val (.word header)))
    (totalLocal : state.locals.lookup (ofString "len") = some (.val (.word total)))
    (lower : 192 ≤ header.toNat) (upper : header.toNat ≤ 247)
    (nonzero : total ≠ 0) (code : state.code = originalRuntimeCode) (ticks : 1 ≤ state.clock) :
    evaluateHOLFiniteState state rlpHeaderAfterLongString = evaluateHOLFiniteState state rlpHeaderShortList := by
  have guard : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.cmp .notLower (.const 247) (.var .local (ofString "b"))) = some (.val (.word 1)) := by
    simp [evalHOLExact,headerLocal,Compiler.Encoders.Asm.wordCmpHOL,BitVec.le_def,upper]
  obtain ⟨result,post,run,_,_,_,terminal,_⟩ := evaluate_rlpHeader_short_list_contract state header total
    headerLocal totalLocal lower upper nonzero code ticks
  rw [source_rlpHeader_short_list_dispatch,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,guard]
  simp only [show (1 : BitVec 64) ≠ 0 from by decide,if_false]
  rw [run]
  cases result with
  | none => exact False.elim (terminal rfl)
  | some stopped => rfl

#print axioms evaluate_rlpHeader_short_list_dispatch
#print axioms evaluate_rlpHeader_short_list_contract
end InitECandidate.Runtime
