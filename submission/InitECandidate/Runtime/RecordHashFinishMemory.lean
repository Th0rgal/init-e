import InitECandidate.Runtime.RecordHashMemoryContext
import InitECandidate.Runtime.HtrWithdrawalMerkleMemory
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem recordHash_finish_returned_memory {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (sha accelerator zeroHashes input roots heap out mark watched count : BitVec 64) (value : ValueHOL 64)
    (ctx : RecordHashMemoryContext state sha accelerator zeroHashes input roots heap out mark watched count)
    (small : count.toNat ≤ 134217712) (budget : recordHashCost [] ≤ state.clock)
    (run : evaluateHOLFiniteState state (recordHashFinish count) = (some (.returned value),post)) :
    post.memory watched = state.memory watched := by
  let arguments : List (ExpHOL 64) :=
    [.var .local (ofString "ch"),.const count,.const count,.var .local (ofString "out")]
  have args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments =
      some [.val (.word roots),.val (.word count),.val (.word count),.val (.word out)] := by
    rw [evalListHOLFinite_eq_toExact]
    simp [arguments,evalListHOLExact,evalHOLExact,ctx.atRoots,ctx.atOut]
  have firstBudget : merkleBodyCost + 1 ≤ state.clock := (Nat.le_add_right _ 1).trans budget
  change evaluateHOLFiniteState state (.seq (.call (some (none,none)) (ofString "merkleize") arguments)
    (.seq (.call (some (none,none)) (ofString "heap_release") [.var .local (ofString "mark")]) (.return (.const 0)))) = _ at run
  obtain ⟨middle,normal,tail⟩ := seq_returned_of_nonreturning_first
    (fun v => evaluate_discard_call_no_return state (ofString "merkleize") arguments v) run
  have frame := merkleize_call_normal_memory state middle arguments sha accelerator heap zeroHashes count out count roots watched
    args ctx.atSha ctx.atAccel ctx.atZero ctx.atHeap ctx.heapFits small ctx.outAligned ctx.outFits ctx.outOutside ctx.heapAligned ctx.heapBefore
    ctx.accelAligned ctx.accelFits ctx.shaFits ctx.accelOutside ctx.shaOutside ctx.code firstBudget normal
  have keepMark : middle.locals.lookup (ofString "mark") = some (.val (.word mark)) := by
    have kept := evaluate_avoidsLocal_flowing (ofString "mark") (.call (some (none,none)) (ofString "merkleize") arguments)
      rfl state (by rw [normal]; exact Or.inl rfl)
    rw [normal] at kept
    exact kept.trans ctx.atMark
  have metadata := evaluateHOLFiniteState_metadata state (.call (some (none,none)) (ofString "merkleize") arguments)
  rw [normal] at metadata
  obtain ⟨released,releaseRun,finishRun⟩ := seq_returned_of_nonreturning_first
    (fun v => evaluate_discard_call_no_return middle (ofString "heap_release") [.var .local (ofString "mark")] v) tail
  have releaseFrame := heapRelease_call_normal_memory middle released (.var .local (ofString "mark")) mark
    (metadata.1.trans ctx.code) (by simp [evalListHOLExact,evalHOLExact,keepMark]) releaseRun
  obtain ⟨finishMemory,_,_,_⟩ := return_const_state released post 0 value finishRun
  rw [finishMemory,releaseFrame]
  exact frame

#print axioms recordHash_finish_returned_memory
end InitECandidate.Runtime
