import InitECandidate.Runtime.RlpValidationInitialGlobalScope
import InitECandidate.Runtime.RlpValidationInitialWitness
import InitECandidate.Runtime.RlpValidationLoopFrame
import InitECandidate.Runtime.RlpValidationLoopNoReturn
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Successful original validator body execution retains frame_mem_ptr; no
callee or loop can bypass the checked normal loop exit and final return-zero. -/
theorem rlpValidation_body_returned_frame {F : Type} (state post : PanSemStateFiniteExact 64 F)
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
    (budget : (2 * length.toNat + 1) * 15 ≤ state.clock)
    (value : ValueHOL 64)
    (run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn__rlp_validate_items_body) = (some (.returned value),post)) :
    post.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)) := by
  obtain ⟨valid,rank,_⟩ := rlpValidation_initial_witness state pointer length scratch frame ceiling inputLimit
    noWrap lengthBound scratchGlobal frameGlobal code orderedFrame scratchBelow arena
  let initial := rlpValidationInitialState state pointer length
  have witnessRank : valid.rank = 2 * length.toNat + 1 := by unfold RlpValidationLoopWitness.rank; rw [rank]
  obtain ⟨loopResult,loopPost,loopRun,_,_,_,done⟩ := evaluate_rlpValidation_loop_frame_bounded frame ceiling inputLimit
    limitBound framePositive initial valid (by rw [witnessRank]; exact budget)
  obtain ⟨output,bodyRun,globals⟩ := evaluate_rlpValidation_initialized_loop_globals state post pointer length
    (some (.returned value)) pointerLocal lengthLocal run
  rw [source_rlpValidation_loop_and_return] at bodyRun
  change evaluateHOLFiniteState initial (.seq rlpValidationLoop (.return (.const 0))) = (some (.returned value),output) at bodyRun
  rw [evaluateHOLFiniteState_seq_line780,loopRun] at bodyRun
  cases loopResult with
  | none =>
    have actual : evaluateHOLFiniteState loopPost (.return (.const 0)) =
        (some (.returned (.val (.word 0))),emptyLocalsHOLFinite loopPost) := by
      simp [evaluateHOLFiniteState_return,evalHOLExact,shapeOfHOLExact]
    have same := (Prod.mk.inj (bodyRun.symm.trans actual)).2
    rw [globals,same]
    exact (done rfl).2
  | some result =>
    have impossible := evaluate_rlpValidation_loop_no_return initial value
    rw [loopRun] at impossible
    exact False.elim (impossible (Prod.mk.inj bodyRun).1)

#print axioms rlpValidation_body_returned_frame
end InitECandidate.Runtime
