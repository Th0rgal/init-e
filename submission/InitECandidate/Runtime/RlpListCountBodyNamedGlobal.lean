import InitECandidate.Runtime.RlpListCountLoopNamedGlobal
import InitECandidate.Runtime.RlpListCountBodyBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The original list-count function returns an input-bounded word and retains
scratch/frame globals through initialization, all iterations and final return. -/
theorem rlpListCount_body_returned_named_global {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (watched : MlS) (different : ofString "scratch_ptr" ≠ watched)
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
    (budget : length.toNat * ((2 * length.toNat + 1) * 15 + 19) ≤ state.clock)
    (value : ValueHOL 64)
    (run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_rlp_list_count) = (some (.returned value),post)) :
    post.globals.lookup watched = state.globals.lookup watched := by
  obtain ⟨valid,offsetZero,_⟩ := rlpListCount_initial_witness state pointer length scratch frame ceiling pointerLocal lengthLocal
    scratchGlobal frameGlobal code arena
  let initial := rlpListCountInitialState state
  have initialClock : initial.clock = state.clock := rfl
  have initialOffset : valid.offset.toNat = 0 := by rw [offsetZero]; rfl
  obtain ⟨result,loopPost,loopRun,_,_,_,done,noReturn⟩ := evaluate_rlpListCount_loop_named_global_bounded initial watched different pointer length scratch frame
    ceiling inputLimit valid noWrap lengthBound limitBound orderedFrame framePositive scratchBelow
    (by simpa only [initialOffset,Nat.sub_zero,initialClock] using budget)
  obtain ⟨output,bodyRun,_,globals⟩ := evaluate_rlpListCount_initialized_loop state post (some (.returned value)) run
  rw [source_rlpListCount_loop_and_return] at bodyRun
  change evaluateHOLFiniteState initial (.seq rlpListCountLoop (.return (.var .local (ofString "count")))) =
    (some (.returned value),output) at bodyRun
  rw [evaluateHOLFiniteState_seq_line780,loopRun] at bodyRun
  cases result with
  | none =>
    obtain ⟨count,_,atCount,bounded,scratchPost,framePost,saved⟩ := done rfl
    have actual : evaluateHOLFiniteState loopPost (.return (.var .local (ofString "count"))) =
        (some (.returned (.val (.word count))),emptyLocalsHOLFinite loopPost) := by
      simp [evaluateHOLFiniteState_return,evalHOLExact,atCount,shapeOfHOLExact]
    have equal := Prod.mk.inj (bodyRun.symm.trans actual)
    rw [globals,equal.2]
    exact saved
  | some result => exact False.elim (noReturn value (Prod.mk.inj bodyRun).1)

#print axioms rlpListCount_body_returned_named_global
end InitECandidate.Runtime
