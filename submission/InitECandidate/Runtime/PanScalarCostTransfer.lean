import InitECandidate.Runtime.PanScopedCostTransfer
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

theorem scalar_lowering_cost_bound {F : Type} (s : PanSemStateFiniteExact 64 F)
    (context : PanToCrepContextExact 64) (layout : LocalWidthsFit s context) :
    ∀ e : ExpHOL 64, scalarLowering e = true →
      panLoweringAllowance context e ≤ expressionCost scalarLoweringWeights s e := by
  intro e supported
  apply scoped_scalar_lowering_cost_bound s context e _ supported
  intro name member shape names mapped
  exact layout name shape names mapped

/-- Executed Loop expression-code work is bounded directly by source expression
cost, with the native coefficient 160. Variable layout is explicit; multiword loads and
the preprocessing/later backend passes require their own transfer proofs. -/
theorem scalar_source_to_loop_cost {F G : Type}
    (s : PanSemStateFiniteExact 64 F) (panContext : PanToCrepContextExact 64)
    (loopContext : CrepToLoopContextExact) (tmp : Nat) (live : NumSet)
    (expression : ExpHOL 64) (state : LoopSemStateFiniteExact 64 G)
    (layout : LocalWidthsFit s panContext) (supported : scalarLowering expression = true) :
    let expressions := (compileExpExactHOLW panContext expression).1
    let compiled := compileExpsHOLExact loopContext tmp live expressions
    ∃ cost, LoopWorkRun state (loopNestedSeqHOL compiled.1)
        (LoopSemStateFiniteExact.evaluate (loopNestedSeqHOL compiled.1) state) cost ∧
      cost + loopNativeValues compiled.2.1 + 39 * compiled.2.1.length ≤
        160 * expressionCost scalarLoweringWeights s expression := by
  obtain ⟨cost, trace, bound⟩ := compiled_pan_expression_trace
    panContext loopContext tmp live expression state
  exact ⟨cost, trace, Nat.le_trans bound (Nat.mul_le_mul_left 160
    (scalar_lowering_cost_bound s panContext layout expression supported))⟩

#print axioms scalar_source_to_loop_cost

#print axioms scalar_lowering_cost_bound
end InitECandidate.Runtime.FineCost
