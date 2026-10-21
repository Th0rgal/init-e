import InitECandidate.Runtime.SourceCostLoopLiveTransferG
import InitECandidate.Runtime.SourceCostLoopCallPassG
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.LoopSemStateFiniteExact

variable {L : LeafPrice}

/-- The real liveness compiler (shrink then mark) is nonamplifying for
completed callee results. Its initial and final states are the original states. -/
theorem LoopWorkG.live_comp {F : Type} {s post : LoopSemStateFiniteExact 64 F}
    {p : HolLoopProg 64} {r : LoopResultExact 64} {w : Nat}
    (work : LoopWorkG L s p (some r, post) w) (nonerror : r ≠ .error)
    (noBreak : ∀ n, r ≠ .break n) (noContinue : ∀ n, r ≠ .continue n) :
    ∃ w', LoopWorkG L s (compHOL p) (some r, post) w' ∧ w' ≤ w := by
  have input : sptSubspt (sptInter s.locals (shrinkHOL [] p .ln).2) s.locals := by
    intro key member
    obtain ⟨present, needed⟩ := (live_mem_interG s.locals _ key).mp member
    refine ⟨present, ?_⟩
    rw [sptLookup_sptInter,
      if_pos (show (sptLookup key (shrinkHOL [] p .ln).2).isSome = true from needed)]
  obtain ⟨targetLocals, w', run, bound, related⟩ :=
    work.live_paid (by simpa using nonerror) [] s.locals .ln input
  have same : targetLocals = post.locals := by
    cases r with
    | «break» n => exact False.elim (noBreak n rfl)
    | «continue» n => exact False.elim (noContinue n rfl)
    | error => exact False.elim (nonerror rfl)
    | result values => exact related
    | exception value => exact related
    | timeOut => exact related
    | finalFfi value => exact related
  rw [same] at run
  refine ⟨w', ?_, bound⟩
  simpa only [compHOL] using run.mark_all

/-- Exact quantitative interface for the pinned optimiseHOL pipeline. The
coefficient is ONE: actual call rewriting, liveness and marking do not multiply
callee costs at recursive call depth. All original terminal-result guards are
retained. -/
theorem loop_optimise_executed_workG (F : Type) (q : HolLoopProg 64)
    (s : LoopSemStateFiniteExact 64 F) (r : LoopResultExact 64)
    (post : LoopSemStateFiniteExact 64 F) (w : Nat)
    (work : LoopWorkG L s q (some r, post) w) (nonerror : r ≠ .error)
    (noBreak : ∀ n, r ≠ .break n) (noContinue : ∀ n, r ≠ .continue n) :
    ∃ w', LoopWorkG L s (optimiseHOL q) (some r, post) w' ∧ w' ≤ w := by
  have known : labelsInHOL .ln s.locals := by
    intro name label found
    simp [sptLookup] at found
  obtain ⟨w1, called, firstBound⟩ := work.call_comp .ln known (by simpa using nonerror)
  obtain ⟨w2, live, secondBound⟩ := called.live_comp nonerror noBreak noContinue
  exact ⟨w2, by simpa only [optimiseHOL] using live, Nat.le_trans secondBound firstBound⟩

#print axioms LoopWorkG.live_comp
#print axioms loop_optimise_executed_workG
end InitECandidate.Runtime.FineCost
