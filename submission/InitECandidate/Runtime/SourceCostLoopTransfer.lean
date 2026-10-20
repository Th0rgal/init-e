import InitECandidate.Runtime.SourceCostLoopLeaf
import Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect.Assembly
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.LoopSemStateFiniteExact Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect

/-- The five original `crep_to_loop` simulation relations, unchanged. -/
structure CrepLoopRel {F : Type} (context : CrepToLoopContextExact) (live : NumSet)
    (t : CrepSemHOLState 64 F) (u : LoopSemStateFiniteExact 64 F) : Prop where
  state : crepToLoopStateRelExact t u
  memory : crepToLoopMemRelHOLExact t.memory u.memory t.memaddrs
  globals : crepToLoopGlobalsRelHOLExact t.globals u.globals
  code : crepToLoopCodeRelExact context t.code u.code
  locals : crepToLoopLocalsRelExact context live t.locals u.locals

/-- The original `ncompile_correct` conclusion for a fixed Loop run. -/
def LoopRunRel {F : Type} (context : CrepToLoopContextExact) (live : NumSet)
    (crepRun : Option (CrepResultHOLExact 64) × CrepSemHOLState 64 F)
    (loopRun : Option (LoopResultExact 64) × LoopSemStateFiniteExact 64 F) : Prop :=
  crepToLoopStateRelExact crepRun.2 loopRun.2 ∧
  crepToLoopMemRelHOLExact crepRun.2.memory loopRun.2.memory crepRun.2.memaddrs ∧
  crepToLoopGlobalsRelHOLExact crepRun.2.globals loopRun.2.globals ∧
  crepToLoopCodeRelExact context crepRun.2.code loopRun.2.code ∧
  loopRun.1 = resultToLoop crepRun.1 ∧
  localsResultRel context live crepRun.1 crepRun.2 loopRun.2

/-- Executed Crep work transfers to the compiled Loop run, at a clock
extension for which all original simulation conclusions hold. -/
def LoopPaid {F : Type} (context : CrepToLoopContextExact) (live : NumSet)
    (t : CrepSemHOLState 64 F) (u : LoopSemStateFiniteExact 64 F) (p : CrepProgHOL 64)
    (w : Nat) : Prop :=
  ∃ extra wl,
    LoopWork { u with clock := u.clock + extra } (compileHOLExact context live p)
      (evaluate (compileHOLExact context live p) { u with clock := u.clock + extra }) wl ∧
    wl ≤ 6 * w ∧
    LoopRunRel context live (evalCrepSemHOLProgExact t p)
      (evaluate (compileHOLExact context live p) { u with clock := u.clock + extra })

/-- Leaves: the pinned `ncompile_correct` supplies the run and relations; the
state-uniform compiled-code bound supplies the work. -/
theorem leaf_loop_paid {F : Type} {context : CrepToLoopContextExact} {live : NumSet}
    {t : CrepSemHOLState 64 F} {u : LoopSemStateFiniteExact 64 F} {p : CrepProgHOL 64}
    {w : Nat} (leaf : crepLeafWork p = some w)
    (ok : (evalCrepSemHOLProgExact t p).1 ≠ some .error)
    (rel : CrepLoopRel context live t u) : LoopPaid context live t u p w := by
  obtain ⟨extra, res1, t1, run, hs, hm, hg, hc, hr, hl⟩ :=
    crepToLoop_ncompile_correct p t _ _ u context live
      ⟨rfl, ok, rel.state, rel.memory, rel.globals, rel.code, rel.locals⟩
  obtain ⟨wl, work, bound⟩ := loopBounded_leaf_compile context live p w leaf F
    { u with clock := u.clock + extra }
  refine ⟨extra, wl, work, bound, ?_⟩
  rw [run]
  exact ⟨hs, hm, hg, hc, hr, hl⟩

theorem crepLeafWork_of_rule_skip : crepLeafWork (.skip : CrepProgHOL 64) = some 1 := rfl

/-- Crep statements covered by the checked Crep-to-Loop transfer. -/
def crepLoopCovered : CrepProgHOL 64 → Bool
  | .seq first second => crepLoopCovered first && crepLoopCovered second
  | p => (crepLeafWork p).isSome

theorem rels_of_run {F : Type} {context : CrepToLoopContextExact} {live : NumSet}
    {crepRun : Option (CrepResultHOLExact 64) × CrepSemHOLState 64 F}
    {loopRun : Option (LoopResultExact 64) × LoopSemStateFiniteExact 64 F}
    (rel : LoopRunRel context live crepRun loopRun) (normal : crepRun.1 = none) :
    loopRun.1 = none ∧ CrepLoopRel context live crepRun.2 loopRun.2 := by
  obtain ⟨hs, hm, hg, hc, hr, hl⟩ := rel
  rw [normal] at hr hl
  exact ⟨hr, ⟨hs, hm, hg, hc, hl⟩⟩

/-- Crep-to-Loop executed-work transfer, by induction on executed Crep work.
Premises are exactly the original `ncompile_correct` premises. -/
theorem crep_loop_executed_work {F : Type} {t : CrepSemHOLState 64 F} {p : CrepProgHOL 64}
    {w : Nat} (work : CrepWork t p w) :
    ∀ (u : LoopSemStateFiniteExact 64 F) (context : CrepToLoopContextExact) (live : NumSet),
      (evalCrepSemHOLProgExact t p).1 ≠ some .error → CrepLoopRel context live t u →
      crepLoopCovered p = true → LoopPaid context live t u p w := by
  induction work with
  | @seqNext t first second middle firstWork secondWork one run two ihOne ihTwo =>
    intro u context live ok rel covered
    simp only [crepLoopCovered, Bool.and_eq_true] at covered
    have okSeq := ok
    rw [evalCrepSemHOLProgExact_seq_holShape, run] at okSeq
    simp only [if_true] at okSeq
    obtain ⟨e1, w1, work1, bound1, rel1⟩ := ihOne u context live (by rw [run]; simp) rel
      covered.1
    rw [run] at rel1
    obtain ⟨norm1, mid⟩ := rels_of_run rel1 rfl
    rcases hrun1 : evaluate (compileHOLExact context live first)
        { u with clock := u.clock + e1 } with ⟨r1, u1⟩
    rw [hrun1] at work1 norm1 mid
    simp only at norm1 mid
    subst norm1
    obtain ⟨e2, w2, work2, bound2, rel2⟩ := ihTwo u1 context live okSeq mid covered.2
    have lifted := LoopWork.add_clock work1 e2 (by simp)
    simp only [] at lifted
    have combined := LoopWork.seqNext lifted work2
    have state : ({ u with clock := u.clock + (e1 + e2) } : LoopSemStateFiniteExact 64 F) =
        { ({ u with clock := u.clock + e1 } : LoopSemStateFiniteExact 64 F) with
          clock := u.clock + e1 + e2 } := by
      simp [Nat.add_assoc]
    refine ⟨e1 + e2, w1 + w2, ?_, by omega, ?_⟩
    · rw [state]
      have sound := LoopWork.sound combined
      simp only [compileHOLExact] at sound ⊢
      rw [sound]
      exact combined
    · have sound := LoopWork.sound combined
      rw [state]
      simp only [compileHOLExact] at sound ⊢
      rw [sound, evalCrepSemHOLProgExact_seq_holShape, run]
      simp only [if_true]
      exact rel2
  | @seqStop t first second result middle firstWork one run ihOne =>
    intro u context live ok rel covered
    simp only [crepLoopCovered, Bool.and_eq_true] at covered
    obtain ⟨e1, w1, work1, bound1, rel1⟩ := ihOne u context live (by
      have okSeq := ok
      rw [evalCrepSemHOLProgExact_seq_holShape, run] at okSeq
      rw [run]; simpa using okSeq) rel covered.1
    rw [run] at rel1
    rcases hrun1 : evaluate (compileHOLExact context live first)
        { u with clock := u.clock + e1 } with ⟨r1, u1⟩
    rw [hrun1] at work1 rel1
    have notNone : r1 ≠ none := by
      obtain ⟨_, _, _, _, hr, _⟩ := rel1
      simp only at hr
      rw [hr]
      cases result <;> simp [resultToLoop]
    obtain ⟨r1', rfl⟩ := Option.ne_none_iff_exists'.mp notNone
    have combined := LoopWork.seqStop (second := compileHOLExact context live second) work1
    refine ⟨e1, w1, ?_, by omega, ?_⟩
    · have sound := LoopWork.sound combined
      simp only [compileHOLExact] at sound ⊢
      rw [sound]
      exact combined
    · have sound := LoopWork.sound combined
      simp only [compileHOLExact] at sound ⊢
      rw [sound, evalCrepSemHOLProgExact_seq_holShape, run]
      simp only [reduceCtorEq, if_false]
      exact rel1
  | _ =>
    intro u context live ok rel covered
    first
      | exact leaf_loop_paid rfl ok rel
      | (simp [crepLoopCovered, crepLeafWork] at covered)

#print axioms crep_loop_executed_work
end InitECandidate.Runtime.FineCost
