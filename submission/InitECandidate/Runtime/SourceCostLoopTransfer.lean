import InitECandidate.Runtime.SourceCostLoopLeaf
import Flapjack.Pancake.CrepToLoop.Proofs.NcompileCorrect
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
extension for which all original simulation conclusions hold. The factor is 7,
not 6: a call that times out at clock zero pays Crep work `1 + crepListWork`,
while its compiled form also moves every argument into a temporary and reads
them back (`6 * crepListWork + 1 + arguments`, with `arguments ≤ crepListWork`). -/
def LoopPaid {F : Type} (context : CrepToLoopContextExact) (live : NumSet)
    (t : CrepSemHOLState 64 F) (u : LoopSemStateFiniteExact 64 F) (p : CrepProgHOL 64)
    (w : Nat) : Prop :=
  ∃ extra wl,
    LoopWork { u with clock := u.clock + extra } (compileHOLExact context live p)
      (evaluate (compileHOLExact context live p) { u with clock := u.clock + extra }) wl ∧
    wl ≤ 7 * w ∧
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
  refine ⟨extra, wl, work, by omega, ?_⟩
  rw [run]
  exact ⟨hs, hm, hg, hc, hr, hl⟩

theorem crepLeafWork_of_rule_skip : crepLeafWork (.skip : CrepProgHOL 64) = some 1 := rfl

theorem rels_of_run {F : Type} {context : CrepToLoopContextExact} {live : NumSet}
    {crepRun : Option (CrepResultHOLExact 64) × CrepSemHOLState 64 F}
    {loopRun : Option (LoopResultExact 64) × LoopSemStateFiniteExact 64 F}
    (rel : LoopRunRel context live crepRun loopRun) (normal : crepRun.1 = none) :
    loopRun.1 = none ∧ CrepLoopRel context live crepRun.2 loopRun.2 := by
  obtain ⟨hs, hm, hg, hc, hr, hl⟩ := rel
  rw [normal] at hr hl
  exact ⟨hr, ⟨hs, hm, hg, hc, hl⟩⟩

#print axioms leaf_loop_paid
#print axioms rels_of_run
end InitECandidate.Runtime.FineCost
