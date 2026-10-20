import InitECandidate.Runtime.SourceCostSharpCrepControl
import InitECandidate.Runtime.SourceCostSharpCrepSimp
import InitECandidate.Runtime.SourceCostLoopSource
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.PanLang Flapjack.LoopSemStateFiniteExact Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect

/-- Sharp end-to-end statement transfer: source -> pan_to_crep -> simp_prog
-> crep_to_loop (installed optimiser discharged), with factor one at every
stage. Loop work is at most the sharp score of the SAME canonical source
events: 10 per statement, 5 per expression, 5 per moved word, 12 per memory
word, 4 per frame slot, plus 45 per replayed word of a certified multiword
load. Preprocessing (pan_simp/structs/globals) is separate. -/
theorem source_loop_sharp_work {F : Type}
    {s post : PanSemStateFiniteExact 64 F}
    {p : ProgHOL 64} {r : Option (PanSemResultExact 64)} {events : List WorkEvent}
    (run : StatementRun s p r post events) (t : CrepSemHOLState 64 F)
    (context : PanToCrepContextExact 64) (resultOk : r ≠ some .error)
    (rel : SourceCrepRel context s t) (localised : localisedProgHOL p = true)
    (checked : sharpSitesProg sharpReplayBound p = true)
    (codeChecked : ∀ function shapes body returnShape,
      s.code.lookup function = some (shapes, body, returnShape) →
        sharpSitesProg sharpReplayBound body = true)
    (u : LoopSemStateFiniteExact 64 F) (loopContext : CrepToLoopContextExact) (live : NumSet)
    (loopRel : CrepLoopRel loopContext live (crepSimpMapcsHOL t) u) :
    ∃ extra wl,
      LoopWork { u with clock := u.clock + extra }
        (compileHOLExact loopContext live (crepSimpProgHOL (compileProgExactHOLW context p)))
        (evaluate (compileHOLExact loopContext live (crepSimpProgHOL (compileProgExactHOLW context p)))
          { u with clock := u.clock + extra }) wl ∧
      wl ≤ sharpScore events ∧
      LoopRunRel loopContext live
        (evalCrepSemHOLProgExact (crepSimpMapcsHOL t) (crepSimpProgHOL (compileProgExactHOLW context p)))
        (evaluate (compileHOLExact loopContext live (crepSimpProgHOL (compileProgExactHOLW context p)))
          { u with clock := u.clock + extra }) := by
  obtain ⟨w, crepWork, crepBound⟩ := source_crep_executed_work_sharp run t context resultOk rel
    localised checked codeChecked
  obtain ⟨r1, t1, crepRun, _, _, _, resultRel⟩ := compiled_source_run t context run.sound
    resultOk rel.state rel.code rel.exceptions rel.locals localised
  have ok : (evalCrepSemHOLProgExact t (compileProgExactHOLW context p)).1 ≠ some .error := by
    rw [crepRun]; exact resultRel_not_error resultRel
  obtain ⟨ws, simpWork, simpBound⟩ := crep_simp_work_sharp crepWork ok
  have simpOk : (evalCrepSemHOLProgExact (crepSimpMapcsHOL t)
      (crepSimpProgHOL (compileProgExactHOLW context p))).1 ≠ some .error := by
    rw [crepArithSimpProgCorrect _ t r1 t1 crepRun (resultRel_not_error resultRel)]
    exact resultRel_not_error resultRel
  obtain ⟨extra, wl, work, bound, runRel⟩ :=
    crep_loop_installed_sharp_work simpWork u loopContext live simpOk loopRel
  exact ⟨extra, wl, work, by omega, runRel⟩

/-- The sharp score as an explicit dot product over the canonical event
vector plus the replay count, which is `k - 1` for every `memory k` and every
`globalAccess k`. -/
theorem sharpScore_eq (ev : List WorkEvent) :
    sharpScore ev = 10 * (executionWork ev).statements + 5 * (executionWork ev).expressions +
      5 * (executionWork ev).movedWords + 12 * (executionWork ev).memoryAccesses +
      4 * (executionWork ev).frameSlots + 40 * (executionWork ev).globalAccesses +
      17 * (executionWork ev).globalWords + 45 * replayUnits ev := by
  simp only [sharpScore, sharpSourceScore, sharpSourceWeights, Work.score, sharpReplayBound]
  omega

/-- Calibration: an event vector with the u256_add Seq-free counts (9 statements,
44 expressions, 102 moved words, 4 frame slots, 4 scalar operations, no memory
accesses, no replay) is priced at 836 Loop units. -/
theorem sharpScore_u256_add_counts (ev : List WorkEvent)
    (statements : (executionWork ev).statements = 9) (expressions : (executionWork ev).expressions = 44)
    (moved : (executionWork ev).movedWords = 102) (memory : (executionWork ev).memoryAccesses = 0)
    (frames : (executionWork ev).frameSlots = 4) (globals : (executionWork ev).globalAccesses = 0)
    (globalWords : (executionWork ev).globalWords = 0) (replay : replayUnits ev = 0) :
    sharpScore ev = 836 := by
  rw [sharpScore_eq, statements, expressions, moved, memory, frames, globals, globalWords, replay]

#print axioms source_loop_sharp_work
#print axioms sharpScore_eq
#print axioms sharpScore_u256_add_counts
end InitECandidate.Runtime.FineCost
