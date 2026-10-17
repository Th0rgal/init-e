import InitECandidate.Runtime.RlpItemTotalValidationBelow
import InitECandidate.Runtime.RlpItemTotalProgress
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Successful original item-total continuation retains scratch and frame
globals through validation and its final computed-size return. -/
theorem rlpItemTotal_continuation_returned_below {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer length header payload kind scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (headerLocal : state.locals.lookup (ofString "h") = some
      (.rStruct [.val (.word header),.val (.word payload),.val (.word kind)]))
    (valid : RlpHeaderSizedProgress (.rStruct [.val (.word header),.val (.word payload),.val (.word kind)]) length)
    (noWrap : pointer.toNat + length.toNat < 2^64) (lengthBound : length.toNat ≤ inputLimit)
    (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (budget : (2 * length.toNat + 1) * 15 + 5 ≤ state.clock)
    (value : ValueHOL 64)
    (run : evaluateHOLFiniteState state rlpItemTotalContinuation = (some (.returned value),post)) (address : BitVec 64) (below : address.toNat < frame.toNat) :
    post.memory address = state.memory address := by
  have scope := rlpItemTotal_validation_scope state header payload kind headerLocal
  rw [source_rlpItemTotal_continuation,evaluateHOLFiniteState_seq_line780] at run
  cases branchRun : evaluateHOLFiniteState state rlpItemTotalValidation with
  | mk result next =>
    rw [branchRun] at run scope
    cases result with
    | none =>
      have globals := rlpItemTotal_validation_normal_below state next pointer length header payload kind scratch frame ceiling inputLimit
        pointerLocal headerLocal valid noWrap lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive
        scratchBelow arena budget branchRun address below
      have locals := scope.1 rfl
      have atHeader : next.locals.lookup (ofString "h") = some
          (.rStruct [.val (.word header),.val (.word payload),.val (.word kind)]) := by
        rw [locals]; exact headerLocal
      have actual : evaluateHOLFiniteState next rlpItemTotalReturn =
          (some (.returned (.val (.word (header + payload)))),emptyLocalsHOLFinite next) := by
        rw [source_rlpItemTotal_return]
        simp [evaluateHOLFiniteState_return,evalHOLExact,evalListHOLExact,atHeader,
          wordOpHOL,wordOp,valueIsWord,valueWord,shapeOfHOLExact]
      have same := (Prod.mk.inj (run.symm.trans actual)).2
      rw [same]
      exact globals
    | some result => exact False.elim (scope.2 value (Prod.mk.inj run).1)

#print axioms rlpItemTotal_continuation_returned_below
end InitECandidate.Runtime
