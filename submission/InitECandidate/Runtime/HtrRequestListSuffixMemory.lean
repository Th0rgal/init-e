import InitECandidate.Runtime.HtrRequestListLoopMemory
import InitECandidate.Runtime.HtrRequestListLoopGlobals
import InitECandidate.Runtime.HtrRequestListHashMemory
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem htrRequestList_suffix_returned_memory {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (sha accelerator zeroHashes chunk kind pointer size roots heap count out mark watched : BitVec 64) (value : ValueHOL 64)
    (layout : ListHashMemoryLayout state sha accelerator zeroHashes chunk heap out watched)
    (valid : HtrRequestListState kind pointer size roots heap count state count.toNat)
    (atOut : state.locals.lookup (ofString "out") = some (.val (.word out)))
    (atMark : state.locals.lookup (ofString "mark") = some (.val (.word mark)))
    (small : count.toNat ≤ 134217712)
    (rootsAligned : roots.toNat % 8 = 0) (rootsFits : roots.toNat + count.toNat * 32 ≤ 33806089496)
    (rootsBefore : watched.toNat < roots.toNat)
    (budget : htrRequestListSuffixCost count ≤ state.clock)
    (run : evaluateHOLFiniteState state (htrRequestListAt 3) = (some (.returned value),post)) :
    post.memory watched = state.memory watched := by
  have firstBudget : count.toNat * (htrRequestStepCost + 1) ≤ state.clock := by
    change count.toNat * (htrRequestStepCost + 1) + (htrPlistChunksCost + 2) ≤ state.clock at budget
    omega
  rw [source_htrRequestList_loop] at run
  obtain ⟨middle,normal,last⟩ := seq_returned_of_nonreturning_first
    (fun v => evaluate_noDirectReturnWhile (.while htrRequestListCondition htrRequestListStep) (by decide) state v) run
  have frame := htrRequestList_loop_normal_memory sha accelerator zeroHashes kind pointer size roots heap count watched
    small rootsAligned rootsFits rootsBefore layout.heapAligned layout.heapFits layout.heapBefore layout.accelAligned layout.accelFits
    layout.shaFits layout.accelOutside layout.shaOutside state middle count.toNat layout.code valid layout.atSha layout.atAccel layout.atZero
    firstBudget normal
  have globals := htrRequestList_loop_normal_globals state middle kind pointer size roots heap count count.toNat small layout.heapFits
    layout.code valid firstBudget normal
  have metadata := evaluateHOLFiniteState_metadata state (.while htrRequestListCondition htrRequestListStep)
  rw [normal] at metadata
  have keep (key : MlS) (different : key ≠ ofString "i") : middle.locals.lookup key = state.locals.lookup key := by
    have avoids : avoidsLocal key (.while htrRequestListCondition htrRequestListStep) = true := by
      simp [avoidsLocal,htrRequestListStep,htrRequestListBranch,Ne.symm different]
    have kept := evaluate_avoidsLocal_flowing key (.while htrRequestListCondition htrRequestListStep) avoids state
      (by rw [normal]; exact Or.inl rfl)
    simpa only [normal] using kept
  have bounded := runBounded_htrRequestList_loop state kind pointer size roots heap count count.toNat small layout.heapFits layout.code valid firstBudget
  unfold RunBounded at bounded
  rw [normal] at bounded
  have enough : htrPlistChunksCost + 2 ≤ middle.clock := by
    have spent : state.clock ≤ middle.clock + count.toNat * (htrRequestStepCost + 1) := bounded.1
    change count.toNat * (htrRequestStepCost + 1) + (htrPlistChunksCost + 2) ≤ state.clock at budget
    omega
  have tail := htrRequestList_hash_returned_memory middle post sha accelerator zeroHashes chunk roots count heap out mark watched value
    (layout.transfer globals metadata.1) ((keep _ (by decide)).trans valid.rootsLocal) ((keep _ (by decide)).trans valid.countLocal)
    ((keep _ (by decide)).trans atOut) ((keep _ (by decide)).trans atMark) small enough last
  exact tail.trans frame

#print axioms htrRequestList_suffix_returned_memory
end InitECandidate.Runtime
