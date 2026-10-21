import InitECandidate.Runtime.SSAQuantitativeCost

namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend Flapjack.WordSemStateFiniteExact
set_option maxHeartbeats 4000000

/-- Clock-zero loop continuation: derive both timeout runs and their full
flushed frame from the reached body states. The body allowance includes only
actually executed reconciliation; no recursive or setup charge is added. -/
theorem ssa_loop_timeout_cost {C F : Type}
    (SP TP : WordLangProgHOL (BitVec 64) → Nat)
    (names exits targetNames targetExits : Spt Unit)
    (body finalBody : WordLangProgHOL (BitVec 64))
    (source sourceEntry sourcePost target targetEntry targetPost : WordSemStateFiniteExact 64 C F)
    (result : Option (WordSemResult 64)) (backedgeWork : Nat)
    (sourceCut : cutState (names,.ln) source = some sourceEntry)
    (targetCut : cutState (targetNames,.ln) target = some targetEntry)
    (sourceRun : evaluate body sourceEntry = (result,sourcePost))
    (targetRun : evaluate finalBody targetEntry = (result,targetPost))
    (continuing : wordSemContLoop result = true)
    (zero : sourcePost.clock = 0)
    (frame : Flapjack.WordAlloc.wordStateEqRel sourcePost targetPost)
    (bodyCost : wordExecutionCost (fun p _ => TP p) finalBody targetEntry ≤
      wordExecutionCost (fun p _ => SP p) body sourceEntry + backedgeWork)
    (headCost : TP (.loop targetNames finalBody targetExits) + backedgeWork ≤
      SP (.loop names body exits)) :
    evaluate (.loop names body exits) source = (some .timeOut,flushState true sourcePost) ∧
    evaluate (.loop targetNames finalBody targetExits) target =
      (some .timeOut,flushState true targetPost) ∧
    Flapjack.WordAlloc.wordStateEqRel (flushState true sourcePost) (flushState true targetPost) ∧
    (flushState true sourcePost).locals = (flushState true targetPost).locals ∧
    wordExecutionCost (fun p _ => TP p) (.loop targetNames finalBody targetExits) target ≤
      wordExecutionCost (fun p _ => SP p) (.loop names body exits) source := by
  have targetZero : targetPost.clock = 0 := by
    have h := frame
    simp_all only [Flapjack.WordAlloc.wordStateEqRel]
  have flushed : Flapjack.WordAlloc.wordStateEqRel (flushState true sourcePost)
      (flushState true targetPost) ∧
      (flushState true sourcePost).locals = (flushState true targetPost).locals := by
    simp_all only [Flapjack.WordAlloc.wordStateEqRel,flushState,and_true]
  have sourceLoop := WordToWord.evaluate_loop_run names exits body source sourceEntry
    sourceCut result sourcePost sourceRun
  have targetLoop := WordToWord.evaluate_loop_run targetNames targetExits finalBody target
    targetEntry targetCut result targetPost targetRun
  refine ⟨?_,?_,flushed.1,flushed.2,?_⟩
  · simpa only [continuing,if_true,zero] using sourceLoop
  · simpa only [continuing,if_true,targetZero] using targetLoop
  · rw [pure_loop_cost_run SP names exits body source sourceEntry sourcePost result sourceCut sourceRun]
    rw [pure_loop_cost_run TP targetNames targetExits finalBody target targetEntry targetPost
      result targetCut targetRun]
    simp only [continuing,if_true,zero,targetZero,Nat.add_zero]
    omega

#print axioms ssa_loop_timeout_cost
end InitECandidate.Runtime.FineCost
