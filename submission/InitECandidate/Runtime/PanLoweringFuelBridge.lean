import InitECandidate.Runtime.PanLoweringAllowance
import InitECandidate.Runtime.CrepExpressionFuel
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.PanLang

mutual
  theorem crep_expression_fuel_le_work (e : CrepExpHOL 64) :
      crepExprFuel e ≤ crepNodeWork e := by
    cases e with
    | load child | load32 child | loadByte child =>
      have bound := crep_expression_fuel_le_work child
      simp only [crepExprFuel, crepNodeWork]
      omega
    | op operator args | crepOp operator args =>
      have bound := crep_expressions_fuel_le_work args
      simp only [crepExprFuel, crepNodeWork]
      omega
    | cmp operator left right | shift operator left right =>
      have lhs := crep_expression_fuel_le_work left
      have rhs := crep_expression_fuel_le_work right
      simp only [crepExprFuel, crepNodeWork]
      omega
    | const _ | var _ | loadGlob _ | baseAddr | topAddr =>
      simp [crepExprFuel, crepNodeWork]
  termination_by sizeOf e

  theorem crep_expressions_fuel_le_work (es : List (CrepExpHOL 64)) :
      crepExpsFuel es ≤ crepListWork es := by
    cases es with
    | nil => simp [crepExpsFuel, crepListWork]
    | cons head tail =>
      have first := crep_expression_fuel_le_work head
      have rest := crep_expressions_fuel_le_work tail
      simp only [crepExpsFuel, crepListWork]
      omega
  termination_by sizeOf es
end

/-- The source local allowance also bounds the additional Loop clock used
by the existing exact expression simulation. This clock component alone
omits straight-line work; it must remain paired with expression-node work. -/
theorem pan_lowering_expression_fuel_bound (context : PanToCrepContextExact 64)
    (e : ExpHOL 64) :
    crepExpsFuel (compileExpExactHOLW context e).1 ≤ panLoweringAllowance context e :=
  Nat.le_trans (crep_expressions_fuel_le_work _) (pan_lowering_work_bound context e)

theorem crep_expression_work_bounded {σ : Type} :
    ∀ (s : CrepSemHOLState 64 σ) (e : CrepExpHOL 64)
      (v : HolWordLab 64) (t : LoopSemStateFiniteExact 64 σ)
      (ctxt : CrepToLoopContextExact) (tmp : Nat) (l : NumSet)
      (p : List (HolLoopProg 64)) (le : HolLoopExp 64) (ntmp : Nat) (nl : NumSet),
      evalCrepSemHOLExp s e = some v ∧
        crepToLoopStateRelExact s t ∧
        crepToLoopMemRelHOLExact s.memory t.memory s.memaddrs ∧
        crepToLoopGlobalsRelHOLExact s.globals t.globals ∧
        crepToLoopCodeRelExact ctxt s.code t.code ∧
        crepToLoopLocalsRelExact ctxt l s.locals t.locals ∧
        compileExpHOLExact ctxt tmp l e = (p, le, ntmp, nl) ∧
        ctxt.vmax < tmp →
      ∃ (ck : Nat), ck ≤ crepNodeWork e ∧ ∃ (st : LoopSemStateFiniteExact 64 σ),
        LoopSemStateFiniteExact.evaluate (loopNestedSeqHOL p)
            { t with clock := t.clock + ck } = (none, st) ∧
        LoopSemStateFiniteExact.eval st le = some (wlabWlocExact v) ∧
        crepToLoopStateRelExact s st ∧
        crepToLoopMemRelHOLExact s.memory st.memory s.memaddrs ∧
        crepToLoopGlobalsRelHOLExact s.globals st.globals ∧
        crepToLoopCodeRelExact ctxt s.code st.code ∧
        crepToLoopLocalsRelExact ctxt nl s.locals st.locals := by
  intro s e v t ctxt tmp live code value next out hyps
  obtain ⟨clock, bound, final, simulation⟩ :=
    crep_expression_fuel_bounded s e v t ctxt tmp live code value next out hyps
  exact ⟨clock, Nat.le_trans bound (crep_expression_fuel_le_work e), final, simulation⟩

#print axioms crep_expression_work_bounded

#print axioms pan_lowering_expression_fuel_bound
end InitECandidate.Runtime.FineCost
