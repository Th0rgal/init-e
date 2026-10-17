import InitECandidate.Runtime.CommonPrefixAfterMin
import InitECandidate.Runtime.MinCall
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem source_commonPrefix_body : sourceFunctionBody Guest.guestFn_common_prefix_length =
    .decCall (ofString "n") .one (ofString "min")
      [.var .local (ofString "al"),.var .local (ofString "bl")] commonPrefixAfterMin := by
  simp only [commonPrefixAfterMin,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- The complete original prefix function bounds every returned word by both
input lengths; the min call adds one source tick to the byte-loop bound. -/
theorem evaluate_commonPrefix_body_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (left right : BitVec 64)
    (leftLocal : state.locals.lookup (ofString "al") = some (.val (.word left)))
    (rightLocal : state.locals.lookup (ofString "bl") = some (.val (.word right)))
    (installed : state.code.lookup (ofString "min") = some minCodeEntry)
    (ticks : (wordMin left right).toNat + 1 ≤ state.clock) :
    ∃ result post, evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_common_prefix_length) = (result,post) ∧
      state.clock ≤ post.clock + (wordMin left right).toNat + 1 ∧ post.clock ≤ state.clock ∧ result ≠ some .timeOut ∧
      (∀ value, result = some (.returned value) → ∃ found : BitVec 64,
        value = .val (.word found) ∧ found.toNat ≤ left.toNat ∧ found.toNat ≤ right.toNat) := by
  have args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      [.var .local (ofString "al"),.var .local (ofString "bl")] = some [.val (.word left),.val (.word right)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,leftLocal,rightLocal]
  let entered := setVarHOLFinite (ofString "n") (.val (.word (wordMin left right))) {state with clock := state.clock - 1}
  have atLength : entered.locals.lookup (ofString "n") = some (.val (.word (wordMin left right))) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have enteredClock : entered.clock = state.clock - 1 := rfl
  obtain ⟨result,output,run,cost,remaining,noTimeout,returned⟩ := evaluate_commonPrefix_after_min
    entered (wordMin left right) atLength (by rw [enteredClock]; omega)
  have minLeft : (wordMin left right).toNat ≤ left.toNat := by
    unfold wordMin
    split <;> simp_all
  have minRight : (wordMin left right).toNat ≤ right.toNat := by
    exact BitVec.le_def.mp (wordMin_le_right left right)
  refine ⟨result,{output with locals := HolFiniteMapExact.resVarEq output.locals (ofString "n",state.locals.lookup (ofString "n"))},?_,?_,?_,noTimeout,?_⟩
  · rw [source_commonPrefix_body,evaluate_min_decCall state (ofString "n") _ commonPrefixAfterMin left right installed args (by omega)]
    change ((evaluateHOLFiniteState entered commonPrefixAfterMin).1,
      {(evaluateHOLFiniteState entered commonPrefixAfterMin).2 with locals := HolFiniteMapExact.resVarEq (evaluateHOLFiniteState entered commonPrefixAfterMin).2.locals (ofString "n",state.locals.lookup (ofString "n"))}) = _
    rw [run]
  · change state.clock ≤ output.clock + (wordMin left right).toNat + 1
    rw [enteredClock] at cost
    omega
  · change output.clock ≤ state.clock
    rw [enteredClock] at remaining
    omega
  · intro value equal
    obtain ⟨found,same,bound⟩ := returned value equal
    exact ⟨found,same,by omega,by omega⟩

#print axioms source_commonPrefix_body
#print axioms evaluate_commonPrefix_body_bounded
end InitECandidate.Runtime
