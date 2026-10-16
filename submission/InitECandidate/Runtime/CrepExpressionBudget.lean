import InitECandidate.Runtime.LoopExprClock
import Flapjack.Pancake.CrepToLoop.Proofs.CompExpPreservesEval
namespace InitECandidate.Runtime
open Flapjack

/-- A checked static syntax budget bounds the original expression compiler's
extra clock while retaining every original value and state relation. -/
theorem crep_expression_bounded {width : Nat} [NeZero width] {σ : Type} :
    ∀ (s : CrepSemHOLState width σ) (e : CrepExpHOL width)
      (v : HolWordLab width) (t : LoopSemStateFiniteExact width σ)
      (ctxt : CrepToLoopContextExact) (tmp : Nat) (l : NumSet)
      (p : List (HolLoopProg width)) (le : HolLoopExp width) (ntmp : Nat) (nl : NumSet) (budget : Nat)
      (_bounded : loopExprFuel (loopNestedSeqHOL p) = some budget),
      evalCrepSemHOLExp s e = some v ∧
        crepToLoopStateRelExact s t ∧
        crepToLoopMemRelHOLExact s.memory t.memory s.memaddrs ∧
        crepToLoopGlobalsRelHOLExact s.globals t.globals ∧
        crepToLoopCodeRelExact ctxt s.code t.code ∧
        crepToLoopLocalsRelExact ctxt l s.locals t.locals ∧
        compileExpHOLExact ctxt tmp l e = (p, le, ntmp, nl) ∧
        ctxt.vmax < tmp →
      ∃ (ck : Nat), ck ≤ budget ∧ ∃ (st : LoopSemStateFiniteExact width σ),
        LoopSemStateFiniteExact.evaluate (loopNestedSeqHOL p)
            { t with clock := t.clock + ck } = (none, st) ∧
        LoopSemStateFiniteExact.eval st le = some (wlabWlocExact v) ∧
        crepToLoopStateRelExact s st ∧
        crepToLoopMemRelHOLExact s.memory st.memory s.memaddrs ∧
        crepToLoopGlobalsRelHOLExact s.globals st.globals ∧
        crepToLoopCodeRelExact ctxt s.code st.code ∧
        crepToLoopLocalsRelExact ctxt nl s.locals st.locals := by
  intro s e v t ctxt tmp l p le ntmp nl budget bounded hyps
  obtain ⟨clock,final,evaluated,value,related,memory,globals,code,locals⟩ :=
    crepToLoop_comp_exp_preserves_eval s e v t ctxt tmp l p le ntmp nl hyps
  have cost := loopExprFuel_correct (loopNestedSeqHOL p)
    {t with clock := t.clock + clock} budget bounded
  rw [evaluated] at cost
  change t.clock + clock ≤ final.clock + budget at cost
  have initialClock : s.clock = t.clock := hyps.2.1.2.2.1
  have finalClock : s.clock = final.clock := related.2.2.1
  exact ⟨clock,by omega,final,evaluated,value,related,memory,globals,code,locals⟩

#print axioms crep_expression_bounded
end InitECandidate.Runtime
