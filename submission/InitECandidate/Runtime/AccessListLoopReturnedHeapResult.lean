import InitECandidate.Runtime.AccessListHeapLoopWitness
import InitECandidate.Runtime.AccessListLoopReturnHeapBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A successful outer traversal returns precisely the records pointer and list count. -/
theorem access_loop_returned_heap_result {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (array count records input inputLength scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (valid : AccessHeapLoopWitness state array count records input inputLength scratch frame ceiling)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat) (scratchBelow : scratch.toNat ≤ ceiling)
    (arrayAbove : ceiling ≤ array.toNat)
    (arrayBeforeRecords : array.toNat + count.toNat * 16 ≤ records.toNat)
    (countLimit : inputLimit * 32 < 2^64)
    (inputBeforeFrame : input.toNat + inputLength.toNat ≤ frame.toNat ∨ (ceiling % 8 = 0 ∧ ceiling ≤ input.toNat))
    (budget : (count.toNat - valid.index.toNat) *
      (accessStepCost inputLength.toNat inputLength.toNat + 1) ≤ state.clock)
    (value : ValueHOL 64)
    (run : evaluateHOLFiniteState state accessLoopAndReturn = (some (.returned value),post)) :
    ∃ middle : PanSemStateFiniteExact 64 F,
      evaluateHOLFiniteState state accessLoop = (none,middle) ∧
      value = .rStruct [.val (.word records),.val (.word count)] ∧
      post = emptyLocalsHOLFinite middle := by
  obtain ⟨result,middle,loopRun,_,_,_,done,noReturn⟩ := evaluate_access_loop_heap_bounded state array count records input inputLength scratch frame
    ceiling inputLimit valid inputBound limitBound orderedFrame framePositive scratchBelow arrayAbove arrayBeforeRecords countLimit inputBeforeFrame budget
  rw [source_access_loop_and_return,evaluateHOLFiniteState_seq_line780,loopRun] at run
  cases result with
  | some result =>
    have same := (Prod.mk.inj run).1
    exact False.elim (noReturn value same)
  | none =>
    obtain ⟨next,finished⟩ := done rfl
    dsimp only at run
    rw [evaluateHOLFiniteState_return] at run
    have expression : @evalHOLExact 64 F _ middle.toExact
        (fun address => Classical.propDecidable (middle.memaddrs address))
        (.rstruct [.var .local (ofString "recs"),.rfield 1 (.var .local (ofString "lst"))]) =
        some (.rStruct [.val (.word records),.val (.word count)]) := by
      simp [evalHOLExact,evalListHOLExact,next.recordsLocal,next.listLocal]
    rw [expression] at run
    dsimp only at run
    split at run
    · have equal := Prod.mk.inj run
      have returned := Option.some.inj equal.1
      have valueEq := PanSemResultExact.returned.inj returned
      exact ⟨middle,loopRun,valueEq.symm,equal.2.symm⟩
    · cases run

#print axioms access_loop_returned_heap_result
end InitECandidate.Runtime
