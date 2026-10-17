import InitECandidate.Runtime.CommonPrefixLoopBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def commonPrefixAfterMin : ProgHOL 64 :=
  match sourceFunctionBody Guest.guestFn_common_prefix_length with
  | .decCall _ _ _ _ body => body
  | _ => .skip

theorem source_commonPrefix_after_min : commonPrefixAfterMin =
    .dec (ofString "i") .one (.const 0)
      (.seq commonPrefixLoop (.return (.var .local (ofString "n")))) := by
  simp only [commonPrefixAfterMin,commonPrefixLoop,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- The whole comparison continuation after min has a bounded returned word,
including early mismatch, final return, and declaration-local restoration. -/
theorem evaluate_commonPrefix_after_min {F : Type} (state : PanSemStateFiniteExact 64 F)
    (length : BitVec 64)
    (lengthLocal : state.locals.lookup (ofString "n") = some (.val (.word length)))
    (ticks : length.toNat ≤ state.clock) :
    ∃ result post, evaluateHOLFiniteState state commonPrefixAfterMin = (result,post) ∧
      state.clock ≤ post.clock + length.toNat ∧ post.clock ≤ state.clock ∧ result ≠ some .timeOut ∧
      (∀ value, result = some (.returned value) → ∃ found : BitVec 64,
        value = .val (.word found) ∧ found.toNat ≤ length.toNat) := by
  let entered := setVarHOLFinite (ofString "i") (.val (.word (0 : BitVec 64))) state
  have atIndex : entered.locals.lookup (ofString "i") = some (.val (.word (0 : BitVec 64))) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have atLength : entered.locals.lookup (ofString "n") = some (.val (.word length)) := by
    simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "i" ≠ ofString "n" by decide] using lengthLocal
  obtain ⟨result,middle,loop,cost,remaining,noTimeout,done,returned⟩ :=
    evaluate_commonPrefix_loop_bounded entered 0 length atIndex atLength (Nat.zero_le _)
      (by simpa [entered,setVarHOLFinite] using ticks)
  have sequence : ∃ result post,
      evaluateHOLFiniteState entered (.seq commonPrefixLoop (.return (.var .local (ofString "n")))) = (result,post) ∧
      state.clock ≤ post.clock + length.toNat ∧ post.clock ≤ state.clock ∧ result ≠ some .timeOut ∧
      (∀ value, result = some (.returned value) → ∃ found : BitVec 64,
        value = .val (.word found) ∧ found.toNat ≤ length.toNat) := by
    rw [evaluateHOLFiniteState_seq_line780,loop]
    cases result with
    | none =>
      have atN := (done rfl).2
      have finish : evaluateHOLFiniteState middle (.return (.var .local (ofString "n"))) =
          (some (.returned (.val (.word length))),emptyLocalsHOLFinite middle) := by
        simp [evaluateHOLFiniteState_return,evalHOLExact,atN,shapeOfHOLExact]
      dsimp only
      rw [finish]
      refine ⟨_,_,rfl,cost,remaining,by simp,?_⟩
      intro value equal
      have same := PanSemResultExact.returned.inj (Option.some.inj equal)
      exact ⟨length,same.symm,Nat.le_refl _⟩
    | some result => exact ⟨_,_,rfl,cost,remaining,noTimeout,returned⟩
  obtain ⟨result,output,sequenceRun,cost,remaining,noTimeout,returned⟩ := sequence
  refine ⟨result,{output with locals := HolFiniteMapExact.resVarEq output.locals (ofString "i",state.locals.lookup (ofString "i"))},?_,cost,remaining,noTimeout,returned⟩
  rw [source_commonPrefix_after_min,evaluateHOLFiniteState_dec_total]
  simp only [evalHOLExact,shapeOfHOLExact,shapeEqHOL,if_true]
  change (let result := evaluateHOLFiniteState entered (.seq commonPrefixLoop (.return (.var .local (ofString "n")))); _) = _
  rw [sequenceRun]

#print axioms source_commonPrefix_after_min
#print axioms evaluate_commonPrefix_after_min
end InitECandidate.Runtime
