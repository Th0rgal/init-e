import InitECandidate.Runtime.SourceCostGlobalsExprBound
import Flapjack.Pancake.Proofs.PanGlobals.CompileCorrect.Assembly
import Flapjack.Pancake.Proofs.PanGlobals.StateRelationClock
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
variable {fn : Flapjack.Pancake.PanLang.MlS}

/-! State-relation facts for the `pan_globals` run transfer. Every clause of the
original relation except the locals equation is independent of `locals`. -/

theorem globalsRel_setLocals {F : Type} {context : PanGlobalsContextExact 64}
    {s t : PanSemStateFiniteExact 64 F} {b : Bool} (rel : panGlobalsStateRelHOLExact b context s t)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) :
    panGlobalsStateRelHOLExact true context { s with locals := locals } { t with locals := locals } := by
  unfold panGlobalsStateRelHOLExact at rel ⊢
  exact ⟨rel.1, fun _ => rfl, rel.2.2⟩

theorem globalsRel_locals {F : Type} {context : PanGlobalsContextExact 64}
    {s t : PanSemStateFiniteExact 64 F} (rel : panGlobalsStateRelHOLExact true context s t) :
    s.locals = t.locals := by
  unfold panGlobalsStateRelHOLExact at rel
  exact rel.2.1 rfl

theorem globalsRel_clock {F : Type} {context : PanGlobalsContextExact 64}
    {s t : PanSemStateFiniteExact 64 F} {b : Bool} (rel : panGlobalsStateRelHOLExact b context s t) :
    s.clock = t.clock := by
  unfold panGlobalsStateRelHOLExact at rel
  exact rel.2.2.2.2.2.1

theorem globalsRel_eshapes {F : Type} {context : PanGlobalsContextExact 64}
    {s t : PanSemStateFiniteExact 64 F} {b : Bool} (rel : panGlobalsStateRelHOLExact b context s t) :
    s.eshapes = t.eshapes := by
  unfold panGlobalsStateRelHOLExact at rel
  exact rel.2.2.2.2.1

theorem globalsRel_code {F : Type} {context : PanGlobalsContextExact 64}
    {s t : PanSemStateFiniteExact 64 F} {b : Bool} (rel : panGlobalsStateRelHOLExact b context s t)
    {function parameters program returnShape}
    (found : s.code.lookup function = some (parameters, program, returnShape)) :
    t.code.lookup function = some (parameters, compileProgExactHOL context program, returnShape) := by
  unfold panGlobalsStateRelHOLExact at rel
  exact rel.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 function parameters program returnShape found

theorem globalsRel_setVar {F : Type} {context : PanGlobalsContextExact 64}
    {s t : PanSemStateFiniteExact 64 F} (rel : panGlobalsStateRelHOLExact true context s t)
    (name : MlS) (value : ValueHOL 64) :
    panGlobalsStateRelHOLExact true context (setVarHOLFinite name value s) (setVarHOLFinite name value t) := by
  have same := globalsRel_locals rel
  unfold setVarHOLFinite
  rw [← same]
  exact globalsRel_setLocals rel _

theorem globalsRel_callEntry {F : Type} {context : PanGlobalsContextExact 64}
    {s t : PanSemStateFiniteExact 64 F} {b : Bool} (rel : panGlobalsStateRelHOLExact b context s t)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) :
    panGlobalsStateRelHOLExact true context (callEntryStateHOLFinite s callee)
      (callEntryStateHOLFinite t callee) := by
  have clocked := PanGlobalsStateRelationClock.stateRelDecClockHOL context s t b rel
  exact globalsRel_setLocals clocked callee

theorem globalsRel_decClock {F : Type} {context : PanGlobalsContextExact 64}
    {s t : PanSemStateFiniteExact 64 F} {b : Bool} (rel : panGlobalsStateRelHOLExact b context s t) :
    panGlobalsStateRelHOLExact b context (decClockHOLFinite s) (decClockHOLFinite t) :=
  PanGlobalsStateRelationClock.stateRelDecClockHOL context s t b rel

/-- A compiled run from a related state ends with the source result in a
state related at `goodRes`. -/
theorem globals_sub_match {F : Type} {context : PanGlobalsContextExact 64}
    {s t post post' : PanSemStateFiniteExact 64 F} {p : ProgHOL 64}
    {r r' : Option (PanSemResultExact 64)} {ev ev' : List WorkEvent}
    (run : StatementRun fn s p r post ev) (ok : r ≠ some .error)
    (rel : panGlobalsStateRelHOLExact true context s t)
    (target : StatementRun fn t (compileProgExactHOL context p) r' post' ev') :
    r' = r ∧ panGlobalsStateRelHOLExact (goodResHOL r) context post post' := by
  obtain ⟨t2, ev2, rel2⟩ := PanGlobalsCompileCorrectAssembly.compileCorrectHOL p s r context t post
    ⟨rel, run.sound, ok⟩
  have sound := target.sound
  rw [ev2] at sound
  obtain ⟨h1, h2⟩ := Prod.mk.inj sound
  subst h1; subst h2
  exact ⟨rfl, rel2⟩

#print axioms globalsRel_setLocals
#print axioms globalsRel_setVar
#print axioms globalsRel_callEntry
#print axioms globals_sub_match
end InitECandidate.Runtime.FineCost
