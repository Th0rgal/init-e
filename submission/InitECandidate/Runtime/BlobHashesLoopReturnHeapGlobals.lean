import InitECandidate.Runtime.BlobHashesLoopHeapBound
import InitECandidate.Runtime.NamedGlobalFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem blobHashes_loop_returned_heap_globals {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (array count buffer input inputLength scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (valid : BlobHashesLoopWitness state array count buffer input inputLength scratch frame ceiling)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat) (scratchBelow : scratch.toNat ≤ ceiling)
    (arrayAbove : ceiling ≤ array.toNat)
    (arrayBeforeBuffer : array.toNat + count.toNat * 16 ≤ buffer.toNat)
    (aligned : buffer.toNat % 8 = 0) (fits : buffer.toNat + count.toNat * 32 ≤ 2^64)
    (budget : (count.toNat - valid.index.toNat) *
      (inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92651) ≤ state.clock)
    (value : ValueHOL 64)
    (run : evaluateHOLFiniteState state blobHashesLoopAndReturn = (some (.returned value),post)) :
    post.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)) ∧
      post.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)) := by
  obtain ⟨result,middle,loopRun,_,_,_,done,noReturn⟩ := evaluate_blobHashes_loop_heap_bounded state
    array count buffer input inputLength scratch frame ceiling inputLimit valid inputBound limitBound orderedFrame framePositive
    scratchBelow arrayAbove arrayBeforeBuffer aligned fits budget
  rw [source_blobHashes_loop_and_return,evaluateHOLFiniteState_seq_line780,loopRun] at run
  cases result with
  | some result =>
    dsimp only at run
    have equal := (Prod.mk.inj run).1
    exact False.elim (noReturn value equal)
  | none =>
    dsimp only at run
    obtain ⟨next,_⟩ := done rfl
    have globals : ∀ watched, post.globals.lookup watched = middle.globals.lookup watched := by
      intro watched
      have retained := evaluate_avoidsGlobalAssignment watched
        (.return (.rstruct [.var .local (ofString "buf"),.rfield 1 (.var .local (ofString "lst"))])) (by rfl) middle
      rw [run] at retained
      exact retained
    exact ⟨(globals _).trans next.scratchGlobal,(globals _).trans next.frameGlobal⟩

#print axioms blobHashes_loop_returned_heap_globals
end InitECandidate.Runtime
