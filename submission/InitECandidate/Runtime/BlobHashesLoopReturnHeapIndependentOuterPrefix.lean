import InitECandidate.Runtime.BlobHashesLoopHeapIndependentOuterPrefix
import InitECandidate.Runtime.ReadOnlyMemory
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem blobHashes_loop_returned_heap_independent_outer_prefix {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (array count buffer input inputLength scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (valid : BlobHashesLoopWitness state array count buffer input inputLength scratch frame ceiling)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat) (scratchBelow : scratch.toNat ≤ ceiling)
    (arrayAbove : ceiling ≤ array.toNat)
    (arrayBeforeBuffer : array.toNat + count.toNat * 16 ≤ buffer.toNat)
    (aligned : buffer.toNat % 8 = 0) (fits : buffer.toNat + count.toNat * 32 ≤ 2^64)
    (watchedArray watchedCount watchedInput watchedLength : BitVec 64)
    (watchedValid : RlpSliceInputPrefix state watchedArray watchedInput watchedLength watchedCount.toNat)
    (watchedAbove : ceiling ≤ watchedArray.toNat)
    (watchedBeforeBuffer : watchedArray.toNat + watchedCount.toNat * 16 ≤ buffer.toNat)
    (budget : (count.toNat - valid.index.toNat) *
      (inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92651) ≤ state.clock)
    (value : ValueHOL 64)
    (run : evaluateHOLFiniteState state blobHashesLoopAndReturn = (some (.returned value),post)) :
    RlpSliceInputPrefix post watchedArray watchedInput watchedLength watchedCount.toNat := by
  obtain ⟨result,middle,loopRun,_,_,_,done,noReturn⟩ := evaluate_blobHashes_loop_heap_independent_outer_prefix_bounded state
    array count buffer input inputLength scratch frame ceiling inputLimit valid inputBound limitBound orderedFrame framePositive
    scratchBelow arrayAbove arrayBeforeBuffer aligned fits watchedArray watchedCount watchedInput watchedLength watchedValid watchedAbove watchedBeforeBuffer budget
  rw [source_blobHashes_loop_and_return,evaluateHOLFiniteState_seq_line780,loopRun] at run
  cases result with
  | some result =>
    dsimp only at run
    have equal := (Prod.mk.inj run).1
    exact False.elim (noReturn value equal)
  | none =>
    dsimp only at run
    obtain ⟨next,_,retained⟩ := done rfl
    have memory := evaluate_readOnly_memory
      (.return (.rstruct [.var .local (ofString "buf"),.rfield 1 (.var .local (ofString "lst"))])) (by rfl) middle
    have metadata := evaluateHOLFiniteState_metadata middle
      (.return (.rstruct [.var .local (ofString "buf"),.rfield 1 (.var .local (ofString "lst"))]))
    rw [run] at memory metadata
    intro slot inside
    obtain ⟨p,n,item⟩ := retained slot inside
    exact ⟨p,n,item.after_frame middle post watchedArray slot p n watchedInput watchedLength metadata.2.1 (congrFun memory _) (congrFun memory _)⟩

#print axioms blobHashes_loop_returned_heap_independent_outer_prefix
end InitECandidate.Runtime
