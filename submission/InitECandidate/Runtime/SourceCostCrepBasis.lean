import InitECandidate.Runtime.SourceCostCrepWork
import InitECandidate.Runtime.PanReadPresence
import InitECandidate.Runtime.PanCostTotal
import Flapjack.Pancake.Proofs.PanToCrep.PcCompileCorrect.Assembly
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

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

/-- Premises of the pinned Pan-to-Crep simulation, unchanged. -/
structure SourceCrepRel {F : Type} (context : PanToCrepContextExact 64)
    (s : PanSemStateFiniteExact 64 F) (t : CrepSemHOLState 64 F) : Prop where
  state : panToCrepStateRelFiniteExact s t
  code : codeRelExactHOLW context s.code t.code
  exceptions : panToCrepExcpRelFiniteExact context.eids s.eshapes
  locals : panToCrepLocalsRelFiniteExact context s.locals t.locals

theorem updateListEq_cons_eq {α β : Type} [DecidableEq α]
    (m : HolFiniteMapExact α β) (e : α × β) (l : List (α × β)) :
    m.updateListEq (e :: l) = (m.updateEq e).updateListEq l := by
  apply HolFiniteMapExact.ext
  funext k
  rfl

/-- A localised call has no global destination, so it emits no global event. -/
theorem callGlobalEvents_localised {F : Type} {info : Option (Option (VarKind × MlStringHOL) ×
      Option (MlStringHOL × MlStringHOL × ProgHOL 64))} {function : MlStringHOL}
    {arguments : List (ExpHOL 64)} (localised : localisedProgHOL (.call info function arguments) = true)
    (s : PanSemStateFiniteExact 64 F) : callGlobalEvents s info = [] := by
  rcases info with _ | ⟨_ | ⟨kind, name⟩, handler⟩
  · rfl
  · rfl
  · cases kind
    · rfl
    · rcases handler with _ | ⟨a, b, h⟩ <;>
        first
        | simp only [localisedProgHOL, Bool.and_false, Bool.false_eq_true] at localised
        | simp_all [localisedProgHOL]
        | (unfold localisedProgHOL at localised; simp at localised)

#print axioms compiled_source_run
#print axioms callGlobalEvents_localised
#print axioms resultRel_some_ne_none
#print axioms resultRel_not_continue
#print axioms compiled_guard
#print axioms decClock_state_rel
end InitECandidate.Runtime.FineCost
