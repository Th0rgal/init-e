import InitECandidate.Runtime.CrepExpressionSyntax
namespace InitECandidate.Runtime
open Flapjack

/-- Full expression simulation with a source-syntax clock ceiling and no
extra budget-certificate premise. -/
theorem crep_expression_fuel_bounded {width : Nat} [NeZero width] {σ : Type} :
    ∀ (s : CrepSemHOLState width σ) (e : CrepExpHOL width)
      (v : HolWordLab width) (t : LoopSemStateFiniteExact width σ)
      (ctxt : CrepToLoopContextExact) (tmp : Nat) (l : NumSet)
      (p : List (HolLoopProg width)) (le : HolLoopExp width) (ntmp : Nat) (nl : NumSet),
      evalCrepSemHOLExp s e = some v ∧
        crepToLoopStateRelExact s t ∧
        crepToLoopMemRelHOLExact s.memory t.memory s.memaddrs ∧
        crepToLoopGlobalsRelHOLExact s.globals t.globals ∧
        crepToLoopCodeRelExact ctxt s.code t.code ∧
        crepToLoopLocalsRelExact ctxt l s.locals t.locals ∧
        compileExpHOLExact ctxt tmp l e = (p, le, ntmp, nl) ∧
        ctxt.vmax < tmp →
      ∃ (ck : Nat), ck ≤ crepExprFuel e ∧ ∃ (st : LoopSemStateFiniteExact width σ),
        LoopSemStateFiniteExact.evaluate (loopNestedSeqHOL p)
            { t with clock := t.clock + ck } = (none, st) ∧
        LoopSemStateFiniteExact.eval st le = some (wlabWlocExact v) ∧
        crepToLoopStateRelExact s st ∧
        crepToLoopMemRelHOLExact s.memory st.memory s.memaddrs ∧
        crepToLoopGlobalsRelHOLExact s.globals st.globals ∧
        crepToLoopCodeRelExact ctxt s.code st.code ∧
        crepToLoopLocalsRelExact ctxt nl s.locals st.locals := by
  intro s e v t ctxt tmp l p le ntmp nl hyps
  have syntaxBudget := compileExp_fuel ctxt tmp l e
  rw [hyps.2.2.2.2.2.2.1] at syntaxBudget
  exact crep_expression_bounded s e v t ctxt tmp l p le ntmp nl (crepExprFuel e) syntaxBudget hyps

theorem crep_expressions_fuel_bounded {width : Nat} [NeZero width] {σ : Type} :
    ∀ (es : List (CrepExpHOL width)) (s : CrepSemHOLState width σ)
      (vs : List (HolWordLab width)) (t : LoopSemStateFiniteExact width σ)
      (ctxt : CrepToLoopContextExact) (tmp : Nat) (l : NumSet)
      (p : List (HolLoopProg width)) (les : List (HolLoopExp width)) (ntmp : Nat) (nl : NumSet),
      es.mapM (evalCrepSemHOLExp s) = some vs ∧
        crepToLoopStateRelExact s t ∧
        crepToLoopMemRelHOLExact s.memory t.memory s.memaddrs ∧
        crepToLoopGlobalsRelHOLExact s.globals t.globals ∧
        crepToLoopCodeRelExact ctxt s.code t.code ∧
        crepToLoopLocalsRelExact ctxt l s.locals t.locals ∧
        compileExpsHOLExact ctxt tmp l es = (p, les, ntmp, nl) ∧
        ctxt.vmax < tmp →
      ∃ (ck : Nat), ck ≤ crepExpsFuel es ∧ ∃ (st : LoopSemStateFiniteExact width σ),
        LoopSemStateFiniteExact.evaluate (loopNestedSeqHOL p)
            { t with clock := t.clock + ck } = (none, st) ∧
        les.mapM (LoopSemStateFiniteExact.eval st) = some (vs.map wlabWlocExact) ∧
        crepToLoopStateRelExact s st ∧
        crepToLoopMemRelHOLExact s.memory st.memory s.memaddrs ∧
        crepToLoopGlobalsRelHOLExact s.globals st.globals ∧
        crepToLoopCodeRelExact ctxt s.code st.code ∧
        crepToLoopLocalsRelExact ctxt nl s.locals st.locals := by
  intro es s vs t ctxt tmp l p les ntmp nl hyps
  have syntaxBudget := compileExps_fuel ctxt tmp l es
  rw [hyps.2.2.2.2.2.2.1] at syntaxBudget
  obtain ⟨clock,final,evaluated,values,related,memory,globals,code,locals⟩ :=
    crepToLoop_comp_exps_preserves_eval es s vs t ctxt tmp l p les ntmp nl hyps
  have cost := loopExprFuel_correct (loopNestedSeqHOL p)
    {t with clock := t.clock + clock} (crepExpsFuel es) syntaxBudget
  rw [evaluated] at cost
  change t.clock + clock ≤ final.clock + crepExpsFuel es at cost
  have initialClock : s.clock = t.clock := hyps.2.1.2.2.1
  have finalClock : s.clock = final.clock := related.2.2.1
  exact ⟨clock,by omega,final,evaluated,values,related,memory,globals,code,locals⟩

#print axioms crep_expression_fuel_bounded
#print axioms crep_expressions_fuel_bounded
end InitECandidate.Runtime
