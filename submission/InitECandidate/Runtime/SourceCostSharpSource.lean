import InitECandidate.Runtime.SourceCostSharpCrepControl
import InitECandidate.Runtime.SourceCostSharpCrepSimp
import InitECandidate.Runtime.SourceCostLoopSource
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.PanLang Flapjack.LoopSemStateFiniteExact Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect

/-- Sharp end-to-end statement transfer: source -> pan_to_crep -> simp_prog
-> crep_to_loop (installed optimiser discharged), with factor one at every
stage. Loop work is at most the sharp score of the SAME canonical source
events: their native-price payloads plus 14 per moved word, 142 per stored
word and 37 per shared-memory operation. Preprocessing
(pan_simp/structs/globals) is separate. -/
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
          { u with clock := u.clock + extra }) ∧
      (evaluate (compileHOLExact loopContext live (crepSimpProgHOL (compileProgExactHOLW context p)))
          { u with clock := u.clock + extra }).1 ≠ some .error := by
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
  refine ⟨extra, wl, work, by omega, runRel, ?_⟩
  rw [runRel.2.2.2.2.1]
  revert simpOk
  generalize (evalCrepSemHOLProgExact (crepSimpMapcsHOL t) (crepSimpProgHOL (compileProgExactHOLW context p))).1 = cr
  intro h
  rcases cr with _ | (_ | _ | _ | _ | _ | _ | _) <;> simp_all [resultToLoop]

/-- The sharp score as an explicit dot product over the canonical event vector. -/
theorem sharpScore_eq (ev : List WorkEvent) :
    sharpScore ev = (executionWork ev).nativeCost + 14 * (executionWork ev).movedWords +
      142 * (executionWork ev).memoryAccesses + 37 * (executionWork ev).nativeEvents +
      128 * (executionWork ev).globalAccesses + 156 * (executionWork ev).globalWords := by
  simp only [sharpScore, sharpSourceScore, sharpSourceWeights, Work.score]
  omega

#print axioms source_loop_sharp_work
#print axioms sharpScore_eq
end InitECandidate.Runtime.FineCost
