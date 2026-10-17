import InitECandidate.Runtime.RlpValidationLoopBound
import InitECandidate.Runtime.RlpValidationInitialWitness
import InitECandidate.Runtime.PanSequenceReturnBound
import InitECandidate.Runtime.StraightLineNoTimeout
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The complete original item-validator body has an explicit input-length
clock bound, including initialization, nested lists, failures and return-zero. -/
theorem evaluate_rlpValidation_body_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer length scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (lengthLocal : state.locals.lookup (ofString "len") = some (.val (.word length)))
    (noWrap : pointer.toNat + length.toNat < 2^64) (lengthBound : length.toNat ≤ inputLimit)
    (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (budget : (2 * length.toNat + 1) * 15 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn__rlp_validate_items_body)
    state.clock ≤ evaluated.2.clock + (2 * length.toNat + 1) * 15 ∧ evaluated.2.clock ≤ state.clock ∧
      evaluated.1 ≠ some .timeOut ∧ evaluated.1 ≠ none := by
  obtain ⟨valid,rank,_⟩ := rlpValidation_initial_witness state pointer length scratch frame ceiling inputLimit
    noWrap lengthBound scratchGlobal frameGlobal code orderedFrame scratchBelow arena
  let initial := rlpValidationInitialState state pointer length
  have witnessRank : valid.rank = 2 * length.toNat + 1 := by
    unfold RlpValidationLoopWitness.rank
    rw [rank]
  have initialClock : initial.clock = state.clock := rfl
  obtain ⟨loopResult,loopPost,loopRun,cost,remaining,noTimeout,_⟩ := evaluate_rlpValidation_loop_bounded
    frame ceiling inputLimit limitBound framePositive initial valid (by rw [witnessRank]; exact budget)
  have sequence := evaluate_sequence_return_zero initial rlpValidationLoop
  have safe := evaluate_sequence_no_timeout initial rlpValidationLoop (.return (.const 0))
    (by rw [loopRun]; exact noTimeout)
    (fun next => evaluate_straightLine_no_timeout (.return (.const 0)) (by rfl) next)
  cases run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn__rlp_validate_items_body) with
  | mk result post =>
    obtain ⟨output,bodyRun,clock,_⟩ := evaluate_rlpValidation_initialized_loop state post pointer length result pointerLocal lengthLocal run
    rw [source_rlpValidation_loop_and_return] at bodyRun
    change evaluateHOLFiniteState initial (.seq rlpValidationLoop (.return (.const 0))) = (result,output) at bodyRun
    rw [bodyRun,loopRun] at sequence
    rw [bodyRun] at safe
    dsimp only at sequence safe cost remaining ⊢
    rw [witnessRank] at cost
    exact ⟨by omega,by omega,safe,sequence.2⟩

#print axioms evaluate_rlpValidation_body_bounded
end InitECandidate.Runtime
