import InitECandidate.Runtime.AuthorizationsLoopReturnHeap
import InitECandidate.Runtime.AuthorizationsLoopReturnHeapBound
import InitECandidate.Runtime.AuthorizationsLoopHeapFrontier
import InitECandidate.Runtime.NamedGlobalFrame
import InitECandidate.Runtime.TxScalarU256HeapInputPrefix
import InitECandidate.Runtime.TxScalarWordHeapInputPrefix
import InitECandidate.Runtime.TxFixedBytesHeapInputPrefix
import InitECandidate.Runtime.TxScalarU256HeapIndependentOuterPrefix
import InitECandidate.Runtime.TxScalarWordHeapIndependentOuterPrefix
import InitECandidate.Runtime.TxFixedBytesHeapIndependentOuterPrefix
import InitECandidate.Runtime.AuthorizationsLoopHeapWitness
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem authorization_loop_returned_heap_frontier {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (array count records input inputLength scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (valid : AuthorizationsHeapLoopWitness state array count records input inputLength scratch frame ceiling)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat) (scratchBelow : scratch.toNat ≤ ceiling)
    (arrayFits : array.toNat + count.toNat * 16 ≤ 2^64) (arrayAbove : ceiling ≤ array.toNat)
    (arrayBeforeRecords : array.toNat + count.toNat * 16 ≤ records.toNat)
    (countLimit : inputLimit * 16 < 2^64)
    (inputBeforeFrame : input.toNat + inputLength.toNat ≤ frame.toNat)
    (budget : (count.toNat - valid.index.toNat) *
      (authorizationStepCost inputLength.toNat inputLength.toNat + 1) ≤ state.clock)
    (value : ValueHOL 64)
    (run : evaluateHOLFiniteState state authorizationLoopAndReturn = (some (.returned value),post)) :
    ∃ heap : BitVec 64,
      post.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)) ∧
      heap.toNat = valid.heap.toNat + 96 * (count.toNat - valid.index.toNat) ∧
      heap.toNat ≤ 33806089496 ∧ heap.toNat % 8 = 0 := by
  obtain ⟨result,middle,loopRun,_,_,_,done,noReturn⟩ := evaluate_authorizations_loop_heap_frontier_bounded state
    array count records input inputLength scratch frame ceiling inputLimit valid inputBound limitBound orderedFrame framePositive
    scratchBelow arrayFits arrayAbove arrayBeforeRecords countLimit inputBeforeFrame budget
  rw [source_authorization_loop_and_return,evaluateHOLFiniteState_seq_line780,loopRun] at run
  cases result with
  | some result =>
    dsimp only at run
    have equal := (Prod.mk.inj run).1
    exact False.elim (noReturn value equal)
  | none =>
    dsimp only at run
    obtain ⟨next,_,heapNat⟩ := done rfl
    have globals : ∀ watched, post.globals.lookup watched = middle.globals.lookup watched := by
      intro watched
      have retained := evaluate_avoidsGlobalAssignment watched
        (.return (.rstruct [.var .local (ofString "recs"),.rfield 1 (.var .local (ofString "lst"))])) (by rfl) middle
      rw [run] at retained
      exact retained
    exact ⟨next.heap,(globals _).trans next.heapGlobal,heapNat,next.heapBound,next.heapAligned⟩

#print axioms authorization_loop_returned_heap_frontier
end InitECandidate.Runtime
