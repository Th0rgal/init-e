import InitECandidate.Runtime.KeccakAbsorbLoopLocal
import InitECandidate.Runtime.KeccakFCallBound
import InitECandidate.Runtime.PanEvaluationMetadata
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def keccakAbsorbAfterLoops : ProgHOL 64 :=
  .seq (.call (some (none,none)) (ofString "keccak_f1600") [.var .local (ofString "stp")]) (.return (.const 0))

theorem source_keccakAbsorb_body : sourceFunctionBody Guest.guestFn_keccak_absorb_block =
    .dec (ofString "i") .one (.const 0) (.seq keccakAbsorbChoice keccakAbsorbAfterLoops) := by
  simp only [keccakAbsorbChoice,keccakAbsorbAfterLoops,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- The actual permutation-and-return suffix consumes one call-entry tick,
including exceptional external outcomes. -/
theorem evaluate_keccakAbsorb_after_loops {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer : BitVec 64) (localState : state.locals.lookup (ofString "stp") = some (.val (.word pointer)))
    (code : state.code = originalRuntimeCode) (ticks : state.clock ≠ 0) :
    ∃ result post, evaluateHOLFiniteState state keccakAbsorbAfterLoops = (result,post) ∧
      post.clock = state.clock - 1 ∧ result ≠ some .timeOut := by
  let call : ProgHOL 64 := .call (some (none,none)) (ofString "keccak_f1600") [.var .local (ofString "stp")]
  have args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      [.var .local (ofString "stp")] = some [.val (.word pointer)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,localState]
  have clock := evaluate_keccakF1600_call_clock state _ pointer code args
  have noTimeout := evaluate_keccakF1600_call_no_timeout state _ pointer ticks code args
  cases callRun : evaluateHOLFiniteState state call with
  | mk result post =>
    change (evaluateHOLFiniteState state call).2.clock = state.clock - 1 at clock
    change (evaluateHOLFiniteState state call).1 ≠ some .timeOut at noTimeout
    rw [callRun] at clock noTimeout
    unfold keccakAbsorbAfterLoops
    change ∃ result post, evaluateHOLFiniteState state (.seq call (.return (.const 0))) = _ ∧ _
    rw [evaluateHOLFiniteState_seq_line780,callRun]
    cases result with
    | none =>
      simp only [evaluateHOLFiniteState_return,evalHOLExact,shapeOfHOLExact]
      exact ⟨_,_,rfl,clock,by simp⟩
    | some result => exact ⟨_,_,rfl,clock,noTimeout⟩

/-- The full original absorption body costs at most eighteen ticks: seventeen
store-loop iterations and one permutation call. Memory errors are included. -/
theorem evaluate_keccakAbsorb_body_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer : BitVec 64) (localState : state.locals.lookup (ofString "stp") = some (.val (.word pointer)))
    (code : state.code = originalRuntimeCode) (ticks : 18 ≤ state.clock) :
    ∃ result post, evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_keccak_absorb_block) = (result,post) ∧
      state.clock ≤ post.clock + 18 ∧ post.clock ≤ state.clock ∧ result ≠ some .timeOut := by
  let entered := setVarHOLFinite (ofString "i") (.val (.word (0 : BitVec 64))) state
  have initial : entered.locals.lookup (ofString "i") = some (.val (.word (0 : BitVec 64))) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have atState : entered.locals.lookup (ofString "stp") = some (.val (.word pointer)) := by
    simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "i" ≠ ofString "stp" from by decide] using localState
  obtain ⟨result,middle,run,cost,remaining,noTimeout,kept,_⟩ := evaluate_keccakAbsorb_loop_choice_local entered initial
    (ofString "stp") (by decide) (by change 17 ≤ state.clock; omega)
  have sequence : ∃ result post, evaluateHOLFiniteState entered (.seq keccakAbsorbChoice keccakAbsorbAfterLoops) = (result,post) ∧
      state.clock ≤ post.clock + 18 ∧ post.clock ≤ state.clock ∧ result ≠ some .timeOut := by
    rw [evaluateHOLFiniteState_seq_line780,run]
    cases result with
    | none =>
      have stp : middle.locals.lookup (ofString "stp") = some (.val (.word pointer)) := (kept rfl).trans atState
      have metadata := evaluateHOLFiniteState_metadata entered keccakAbsorbChoice
      rw [run] at metadata
      obtain ⟨finalResult,post,tail,clock,tailNoTimeout⟩ := evaluate_keccakAbsorb_after_loops middle pointer stp (metadata.1.trans code)
        (by change state.clock ≤ middle.clock + 17 at cost; omega)
      exact ⟨finalResult,post,tail,(by change state.clock ≤ middle.clock + 17 at cost; omega),
        (by change middle.clock ≤ state.clock at remaining; omega),tailNoTimeout⟩
    | some result =>
      exact ⟨some result,middle,rfl,(by change state.clock ≤ middle.clock + 17 at cost; omega),remaining,noTimeout⟩
  obtain ⟨result,post,sequenceRun,total,remaining,noTimeout⟩ := sequence
  have full : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_keccak_absorb_block) =
      (result,{post with locals := HolFiniteMapExact.resVarEq post.locals (ofString "i",state.locals.lookup (ofString "i"))}) := by
    rw [source_keccakAbsorb_body,evaluateHOLFiniteState_dec_total]
    simp only [evalHOLExact,shapeOfHOLExact,shapeEqHOL,if_true]
    change (let output := evaluateHOLFiniteState entered (.seq keccakAbsorbChoice keccakAbsorbAfterLoops); _) = _
    rw [sequenceRun]
  exact ⟨result,_,full,total,remaining,noTimeout⟩

#print axioms source_keccakAbsorb_body
#print axioms evaluate_keccakAbsorb_after_loops
#print axioms evaluate_keccakAbsorb_body_bounded
end InitECandidate.Runtime
