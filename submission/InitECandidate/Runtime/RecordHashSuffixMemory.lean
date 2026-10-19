import InitECandidate.Runtime.RecordHashFinishMemory
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem recordHash_step_runBounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (step : RecordHashStep) (small : step.Small) (input roots out heap : BitVec 64)
    (locals : RecordHashLocals state input roots out)
    (hh : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (cap : heap.toNat ≤ 33806089496) (code : state.code = originalRuntimeCode) (budget : step.cost ≤ state.clock) :
    RunBounded state (.call (some (none,none)) step.function step.arguments) step.cost := by
  have tail : RecordHashBound .skip 0 := by
    intro F s e ch o h ls heap fits installed enough
    exact RunBounded.ofProg (ProgBounded.straight _ rfl) installed enough
  have combined := recordHash_step_bound step small .skip 0 tail state input roots out heap locals hh cap code (by simpa using budget)
  have same : evaluateHOLFiniteState state (.seq (.call (some (none,none)) step.function step.arguments) .skip) =
      evaluateHOLFiniteState state (.call (some (none,none)) step.function step.arguments) := by
    rw [evaluateHOLFiniteState_seq_line780]
    cases run : evaluateHOLFiniteState state (.call (some (none,none)) step.function step.arguments) with
    | mk result post => cases result <;> simp only [evaluateHOLFiniteState_skip]
  unfold RunBounded at combined ⊢
  simpa only [same,Nat.add_zero] using combined

/-- Complete fixed-record suffixes preserve an earlier cell outside their output,
temporary heap and SHA workspaces. -/
theorem recordHash_suffix_returned_memory {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (sha accelerator zeroHashes input roots heap out mark watched count : BitVec 64) (value : ValueHOL 64)
    (steps : List RecordHashStep) (fits : ∀ step ∈ steps, step.Fits count)
    (ctx : RecordHashMemoryContext state sha accelerator zeroHashes input roots heap out mark watched count)
    (small : count.toNat ≤ 134217712) (budget : recordHashCost steps ≤ state.clock)
    (run : evaluateHOLFiniteState state (recordHashSuffix steps count) = (some (.returned value),post)) :
    post.memory watched = state.memory watched := by
  induction steps generalizing state with
  | nil => exact recordHash_finish_returned_memory state post sha accelerator zeroHashes input roots heap out mark watched count value ctx small budget run
  | cons step rest ih =>
    have fit := fits step (by simp)
    have firstBudget : step.cost ≤ state.clock := (Nat.le_add_right _ _).trans budget
    change evaluateHOLFiniteState state
      (.seq (.call (some (none,none)) step.function step.arguments) (recordHashSuffix rest count)) = _ at run
    obtain ⟨middle,normal,last⟩ := seq_returned_of_nonreturning_first
      (fun v => evaluate_discard_call_no_return state step.function step.arguments v) run
    have frame := recordHash_step_normal_memory state middle sha accelerator zeroHashes input roots heap out mark watched count
      ctx step fit firstBudget normal
    have metadata := evaluateHOLFiniteState_metadata state (.call (some (none,none)) step.function step.arguments)
    rw [normal] at metadata
    have bounded := recordHash_step_runBounded state step fit.1 input roots out heap
      ⟨ctx.atInput,ctx.atRoots,ctx.atOut⟩ ctx.atHeap ctx.heapFits ctx.code firstBudget
    unfold RunBounded at bounded
    rw [normal] at bounded
    have remaining : recordHashCost rest ≤ middle.clock := by
      have spent : state.clock ≤ middle.clock + step.cost := bounded.1
      change step.cost + recordHashCost rest ≤ state.clock at budget
      omega
    have tail := ih middle (fun s mem => fits s (by simp [mem])) (ctx.after_call frame.2.2 frame.2.1 metadata.1) remaining last
    exact tail.trans frame.1

#print axioms recordHash_step_runBounded
#print axioms recordHash_suffix_returned_memory
end InitECandidate.Runtime
