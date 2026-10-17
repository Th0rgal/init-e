import InitECandidate.Runtime.RlpHeaderShortStringProgress
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Exact original short-string header declaration contract, including malformed
inputs, read-only behavior and the bounds of every successful returned item. -/
theorem evaluate_rlpHeader_short_string_contract {F : Type} (state : PanSemStateFiniteExact 64 F)
    (header total : BitVec 64)
    (headerLocal : state.locals.lookup (ofString "b") = some (.val (.word header)))
    (totalLocal : state.locals.lookup (ofString "len") = some (.val (.word total)))
    (lower : 128 ≤ header.toNat) (upper : header.toNat ≤ 183)
    (nonzero : total ≠ 0) (code : state.code = originalRuntimeCode) (ticks : 1 ≤ state.clock) :
    ∃ result post, evaluateHOLFiniteState state rlpHeaderShortStringBranch = (result,post) ∧
      state.clock ≤ post.clock + 1 ∧ post.clock ≤ state.clock ∧ result ≠ some .timeOut ∧ result ≠ none ∧
      (∀ value, result = some (.returned value) →
        value = rlpHeaderShortStringValue (header - 128) ∧
        (header - 128).toNat < total.toNat ∧ 0 < (1 + (header - 128)).toNat ∧
        (1 + (header - 128)).toNat ≤ total.toNat) ∧
      post.memory = state.memory ∧ post.globals = state.globals := by
  let entered := setVarHOLFinite (ofString "n") (.val (.word (header - 128))) state
  have atLength : entered.locals.lookup (ofString "n") = some (.val (.word (header - 128))) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  obtain ⟨result,output,bodyRun,cost,remaining,noTimeout,terminal,returned,memory,globals⟩ :=
    evaluate_rlpHeader_short_string_body entered (header - 128) atLength code ticks
  have initializer : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.op .sub [.var .local (ofString "b"),.const 128]) = some (.val (.word (header - 128))) := by
    simp [evalHOLExact,evalListHOLExact,headerLocal,wordOpHOL,wordOp,valueIsWord,valueWord]
  let post := {output with locals := HolFiniteMapExact.resVarEq output.locals (ofString "n",state.locals.lookup (ofString "n"))}
  have run : evaluateHOLFiniteState state rlpHeaderShortStringBranch = (result,post) := by
    rw [source_rlpHeader_short_string,evaluateHOLFiniteState_dec_total]
    simp only [initializer,shapeOfHOLExact,shapeEqHOL,if_true]
    change (let result := evaluateHOLFiniteState entered rlpHeaderShortStringBody; _) = _
    rw [bodyRun]
  refine ⟨result,post,run,cost,remaining,noTimeout,terminal,?_,memory,globals⟩
  intro value equal
  exact ⟨returned value equal,rlpHeader_short_string_scoped_progress state post header total value
    headerLocal totalLocal lower upper nonzero code
    (by rw [run]; exact congrArg (fun result => (result,post)) equal)⟩

#print axioms evaluate_rlpHeader_short_string_contract
end InitECandidate.Runtime
