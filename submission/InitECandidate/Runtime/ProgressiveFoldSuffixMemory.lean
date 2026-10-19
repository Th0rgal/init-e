import InitECandidate.Runtime.ProgressiveFoldLoopMemory
import InitECandidate.Runtime.ProgressiveFinishMemory
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem progressiveFold_suffix_returned_memory {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer accelerator roots acc initial out mark watched : BitVec 64) (value : ValueHOL 64)
    (atPointer : state.globals.lookup (ofString "sha_st") = some (.val (.word pointer)))
    (atAccel : state.globals.lookup (ofString "sha_accel") = some (.val (.word accelerator)))
    (atRoots : state.locals.lookup (ofString "roots") = some (.val (.word roots)))
    (atAcc : state.locals.lookup (ofString "acc") = some (.val (.word acc)))
    (atK : state.locals.lookup (ofString "k") = some (.val (.word initial)))
    (atOut : state.locals.lookup (ofString "out") = some (.val (.word out)))
    (atMark : state.locals.lookup (ofString "mark") = some (.val (.word mark)))
    (outAligned : out.toNat % 8 = 0) (outFits : out.toNat + 32 ≤ 33806089496)
    (outOutside : watched.toNat < out.toNat ∨ out.toNat + 32 ≤ watched.toNat)
    (small : initial.toNat ≤ 4 * 134217712)
    (accAligned : acc.toNat % 8 = 0) (accFits : acc.toNat + 32 ≤ 33806089496)
    (accBefore : watched.toNat < acc.toNat) (accelAligned : accelerator.toNat % 8 = 0)
    (accelFits : accelerator.toNat + 96 ≤ 33806089496) (pointerFits : pointer.toNat + 64 ≤ 33806089496)
    (accelOutside : watched.toNat < accelerator.toNat ∨ accelerator.toNat + 96 ≤ watched.toNat)
    (pointerOutside : watched.toNat < pointer.toNat ∨ pointer.toNat + 64 ≤ watched.toNat)
    (code : state.code = originalRuntimeCode) (budget : progressiveFoldCost + 16 ≤ state.clock)
    (run : evaluateHOLFiniteState state (progressiveAt 8) = (some (.returned value),post)) :
    post.memory watched = state.memory watched := by
  have loopBudget : initial.toNat * 137 ≤ state.clock := by clear run; unfold progressiveFoldCost at budget; omega
  rw [source_progressive_fold] at run
  obtain ⟨middle,normal,tail⟩ := seq_returned_of_nonreturning_first
    (fun v => evaluate_noDirectReturnWhile progressiveFoldLoop (by decide) state v) run
  have frame := progressiveFold_loop_normal_memory state middle pointer accelerator roots acc initial watched
    atPointer atAccel atRoots atAcc atK accAligned accFits accBefore accelAligned accelFits pointerFits
    accelOutside pointerOutside code loopBudget normal
  have clocks := runBounded_progressive_fold state initial atK small code ((Nat.le_add_right _ 16).trans budget)
  have meta' := evaluateHOLFiniteState_metadata state progressiveFoldLoop
  unfold RunBounded at clocks
  rw [normal] at clocks meta'
  have keep (key : MlS) (supported : avoidsLocal key progressiveFoldLoop = true) :
      middle.locals.lookup key = state.locals.lookup key := by
    have locals := evaluate_avoidsLocal_flowing key progressiveFoldLoop supported state (by rw [normal]; exact Or.inl rfl)
    simpa only [normal] using locals
  have finishBudget : 16 ≤ middle.clock := by
    have credit := clocks.1
    dsimp only at credit
    omega
  have suffix := progressiveFinish_returned_memory middle post acc out mark watched value
    ((keep _ (by decide)).trans atAcc) ((keep _ (by decide)).trans atOut) ((keep _ (by decide)).trans atMark)
    outAligned outFits outOutside (meta'.1.trans code) finishBudget tail
  exact suffix.trans frame

#print axioms progressiveFold_suffix_returned_memory
end InitECandidate.Runtime
