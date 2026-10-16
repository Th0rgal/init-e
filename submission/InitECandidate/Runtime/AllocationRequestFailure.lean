import InitECandidate.Runtime.AllocationSource
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The allocator's actual unsigned guard detects an excessive request. -/
theorem eval_allocationRequestCheck_failure {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer size : BitVec 64)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (sizeLocal : state.locals.lookup (ofString "n") = some (.val (.word size)))
    (request : ((33806089496 : BitVec 64) - pointer).toNat < size.toNat) :
    @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) allocationRequestCheck =
        some (.val (.word 1)) := by
  have flag : Compiler.Encoders.Asm.wordCmpHOL .lower ((33806089496 : BitVec 64) - pointer) size = true := by
    change decide (((33806089496 : BitVec 64) - pointer).toNat < size.toNat) = true
    exact decide_eq_true request
  simp [allocationRequestCheck,evalHOLExact,evalListHOLExact,pointerLocal,sizeLocal,
    wordOpHOL,wordOp,valueIsWord,valueWord]
  exact flag

/-- A failed request selects the original trap call with code one. This lemma
only selects the call; termination of that call is established separately. -/
theorem evaluate_allocationRequest_failure_selected {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer size : BitVec 64)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (sizeLocal : state.locals.lookup (ofString "n") = some (.val (.word size)))
    (request : ((33806089496 : BitVec 64) - pointer).toNat < size.toNat) :
    evaluateHOLFiniteState state
      (.ite allocationRequestCheck (.call (some (none,none)) (ofString "trap_with") [.const 1]) .skip) =
    evaluateHOLFiniteState state (.call (some (none,none)) (ofString "trap_with") [.const 1]) := by
  rw [evaluateHOLFiniteState_ite,eval_allocationRequestCheck_failure state pointer size pointerLocal sizeLocal request]
  simp

#print axioms eval_allocationRequestCheck_failure
#print axioms evaluate_allocationRequest_failure_selected
end InitECandidate.Runtime
