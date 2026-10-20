import InitECandidate.Runtime.SourceCostCrepWork
import InitECandidate.Runtime.GuestBulkLoadApplicability
import InitECandidate.Runtime.PanCostTotal
import Flapjack.Pancake.Proofs.PanToCrep.PcCompileCorrect.Assembly
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- Pan-to-Crep executed-work coefficients for source events. Expression and
moved-word coefficients cover the compiler-aware lowering allowance (six times
the four/one local vector); statement, memory and frame coefficients pay the
Crep statements emitted per executed source statement and per moved word.
These are Crep work units, not native instruction counts. -/
def sourceCrepWeights : Work :=
  { statements := 8, expressions := 24, movedWords := 8, memoryAccesses := 8, frameSlots := 8 }

theorem score_statement_cons (coeff : Work) (rest : List WorkEvent) :
    coeff.score (executionWork (.statement :: rest)) =
      coeff.statements + coeff.score (executionWork rest) := by
  rw [executionWork_score_cons]
  simp [WorkEvent.units, Work.score]

theorem score_append (coeff : Work) (left right : List WorkEvent) :
    coeff.score (executionWork (left ++ right)) =
      coeff.score (executionWork left) + coeff.score (executionWork right) :=
  executionWork_score_append coeff left right

theorem scalar_weights_le_crep (work : Work) :
    6 * scalarLoweringWeights.score work ≤ sourceCrepWeights.score work := by
  simp only [Work.score, scalarLoweringWeights, sourceCrepWeights]
  omega

/-- Compiled expression work is paid by the source expression's own events,
for every successful expression of the checked guest load-site form. -/
theorem compiled_expression_crep_work {F : Type} (s : PanSemStateFiniteExact 64 F)
    (context : PanToCrepContextExact 64)
    (targetLocals : HolFiniteMapExact Nat (HolWordLab 64))
    (related : panToCrepLocalsRelFiniteExact context s.locals targetLocals)
    (expression : ExpHOL 64) (value : ValueHOL 64)
    (evaluated : expressionValue s expression = some value)
    (checked : bulkLoadSitesExp expression = true) :
    crepListWork (compileExpExactHOLW context expression).1 ≤
      expressionCost sourceCrepWeights s expression := by
  have present := expression_success_locals_present s expression value evaluated
  have layout := scopedWidthsFit_of_related_present s context targetLocals related expression present
  have supported := bulk_sites_imply_supported s expression checked
  have sourceBound := bounded_bulk_lowering_cost_bound s context expression layout supported
  have lowering := pan_lowering_work_bound context expression
  have weights := scalar_weights_le_crep (executionWork (expressionEvents s expression))
  unfold flattenedExpressionWork at lowering
  unfold expressionCost at sourceBound ⊢
  omega

/-- The pinned Pan-to-Crep correctness theorem, specialized to an exact source
evaluation. All original state, code, exception and locals premises remain. -/
theorem compiled_source_run {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {p : ProgHOL 64} {r : Option (PanSemResultExact 64)}
    (t : CrepSemHOLState 64 F) (context : PanToCrepContextExact 64)
    (run : evaluateHOLFiniteState s p = (r, post)) (result : r ≠ some .error)
    (state : panToCrepStateRelFiniteExact s t) (code : codeRelExactHOLW context s.code t.code)
    (exceptions : panToCrepExcpRelFiniteExact context.eids s.eshapes)
    (locals : panToCrepLocalsRelFiniteExact context s.locals t.locals)
    (localised : localisedProgHOL p = true) :
    ∃ r1 t1, evalCrepSemHOLProgExact t (compileProgExactHOLW context p) = (r1, t1) ∧
      panToCrepStateRelFiniteExact post t1 ∧ codeRelExactHOLW context post.code t1.code ∧
      panToCrepExcpRelFiniteExact context.eids post.eshapes ∧
      pcCompileCorrectResultRel context post t1 r r1 :=
  (pcCompileCorrectAt_iff_HOL p s).mpr (pcCompileCorrect_all p s) r post t context run result
    state code exceptions locals localised

theorem resultRel_some_ne_none {F : Type} {context : PanToCrepContextExact 64}
    {post : PanSemStateFiniteExact 64 F} {t1 : CrepSemHOLState 64 F}
    {r : PanSemResultExact 64} {r1 : Option (CrepResultHOLExact 64)}
    (rel : pcCompileCorrectResultRel context post t1 (some r) r1) : r1 ≠ none := by
  intro hn
  subst hn
  cases r with
  | exception eid v =>
      simp only [pcCompileCorrectResultRel] at rel
      split at rel
      · exact rel
      · exact absurd rel.1 (by simp)
  | _ => simp [pcCompileCorrectResultRel] at rel

theorem resultRel_not_continue {F : Type} {context : PanToCrepContextExact 64}
    {post : PanSemStateFiniteExact 64 F} {t1 : CrepSemHOLState 64 F}
    {r : PanSemResultExact 64} {r1 : Option (CrepResultHOLExact 64)}
    (notContinue : r ≠ .continue)
    (rel : pcCompileCorrectResultRel context post t1 (some r) r1) :
    r1 ≠ some (.continue 0) := by
  intro hn
  subst hn
  cases r with
  | exception eid v =>
      simp only [pcCompileCorrectResultRel] at rel
      split at rel
      · exact rel
      · exact absurd rel.1 (by simp)
  | «continue» => exact notContinue rfl
  | _ => simp [pcCompileCorrectResultRel] at rel

/-- A successful word guard compiles to one Crep expression with that word. -/
theorem compiled_guard {F : Type} {s : PanSemStateFiniteExact 64 F}
    {t : CrepSemHOLState 64 F} {context : PanToCrepContextExact 64}
    {condition : ExpHOL 64} {word : BitVec 64}
    (evaluated : expressionValue s condition = some (.val (.word word)))
    (state : panToCrepStateRelFiniteExact s t) (code : codeRelExactHOLW context s.code t.code)
    (locals : panToCrepLocalsRelFiniteExact context s.locals t.locals)
    (localised : localisedExpHOL condition = true) :
    ∃ ce shape, compileExpExactHOLW context condition = ([ce], shape) ∧
      evalCrepSemHOLExp t ce = some (.word word) := by
  classical
  rcases hc : compileExpExactHOLW context condition with ⟨es, sh⟩
  obtain ⟨hes, _, _, _⟩ :=
    @compileExpValRelHOL 64 F _ s
      (fun address => Classical.propDecidable (s.memaddrs address)) context t
      (fun address => Classical.propDecidable (t.memaddrs address))
      condition (.val (.word word)) es sh evaluated state code locals localised hc
  obtain ⟨ce, hce⟩ : ∃ ce, es = [ce] := by
    rcases es with _ | ⟨ce, _ | ⟨_, _⟩⟩
    · simp [flattenHOL] at hes
    · exact ⟨ce, rfl⟩
    · simp [flattenHOL] at hes
  subst hce
  exact ⟨ce, sh, rfl, by simpa [flattenHOL] using hes⟩

theorem decClock_state_rel {F : Type} {s : PanSemStateFiniteExact 64 F}
    {t : CrepSemHOLState 64 F} (state : panToCrepStateRelFiniteExact s t) :
    panToCrepStateRelFiniteExact (decClockHOLFinite s) (decClockCrepSemHOL t) := by
  have hclk : s.clock = t.clock := state.2.2.2.2.2.1
  simpa [panToCrepStateRelFiniteExact, PanSemStateFiniteExact.decClockHOLFinite,
    decClockCrepSemHOL, hclk] using state

#print axioms compiled_expression_crep_work
#print axioms compiled_source_run
#print axioms resultRel_some_ne_none
#print axioms resultRel_not_continue
#print axioms compiled_guard
#print axioms decClock_state_rel
end InitECandidate.Runtime.FineCost
