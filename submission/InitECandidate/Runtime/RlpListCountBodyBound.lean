import InitECandidate.Runtime.RlpListCountInitialization
import InitECandidate.Runtime.PanSeqStraightBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Complete original list-count body has a finite input-quadratic source-clock
bound, including initialization, nested validation, early errors and return. -/
theorem evaluate_rlpListCount_body_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
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
    (budget : length.toNat * ((2 * length.toNat + 1) * 15 + 19) ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_rlp_list_count)
    state.clock ≤ evaluated.2.clock + (length.toNat * ((2 * length.toNat + 1) * 15 + 19)) ∧ evaluated.2.clock ≤ state.clock ∧
      evaluated.1 ≠ some .timeOut ∧ evaluated.1 ≠ none := by
  obtain ⟨valid,offsetZero,_⟩ := rlpListCount_initial_witness state pointer length scratch frame ceiling pointerLocal lengthLocal
    scratchGlobal frameGlobal code arena
  let initial := rlpListCountInitialState state
  have initialClock : initial.clock = state.clock := rfl
  have initialOffset : valid.offset.toNat = 0 := by rw [offsetZero]; rfl
  obtain ⟨result,loopPost,loopRun,cost,remaining,noTimeout,done,_⟩ := evaluate_rlpListCount_loop_bounded initial pointer length scratch frame
    ceiling inputLimit valid noWrap lengthBound limitBound orderedFrame framePositive scratchBelow
    (by simpa only [initialOffset,Nat.sub_zero,initialClock] using budget)
  let returning : ProgHOL 64 := .return (.var .local (ofString "count"))
  have sequenceBound := evaluate_sequence_straight_bounded initial rlpListCountLoop returning
    (length.toNat * ((2 * length.toNat + 1) * 15 + 19)) (by
      rw [loopRun]
      exact ⟨by simpa only [initialOffset,Nat.sub_zero] using cost,remaining,noTimeout⟩) (by rfl)
  have terminal : (evaluateHOLFiniteState initial (.seq rlpListCountLoop returning)).1 ≠ none := by
    rw [evaluateHOLFiniteState_seq_line780,loopRun]
    cases result with
    | none =>
      obtain ⟨count,_,atCount,_,_,_⟩ := done rfl
      have actual : evaluateHOLFiniteState loopPost returning =
          (some (.returned (.val (.word count))),emptyLocalsHOLFinite loopPost) := by
        simp [returning,evaluateHOLFiniteState_return,evalHOLExact,atCount,shapeOfHOLExact]
      change (evaluateHOLFiniteState loopPost returning).1 ≠ none
      rw [actual]
      simp
    | some result => simp
  cases run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_rlp_list_count) with
  | mk finalResult post =>
    obtain ⟨output,bodyRun,clock,_⟩ := evaluate_rlpListCount_initialized_loop state post finalResult run
    rw [source_rlpListCount_loop_and_return] at bodyRun
    change evaluateHOLFiniteState initial (.seq rlpListCountLoop returning) = (finalResult,output) at bodyRun
    rw [bodyRun] at sequenceBound terminal
    dsimp only at sequenceBound terminal ⊢
    exact ⟨by omega,by omega,sequenceBound.2.2,terminal⟩

#print axioms evaluate_rlpListCount_body_bounded
end InitECandidate.Runtime
