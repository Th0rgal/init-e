import InitECandidate.Runtime.LoopToWordExpressionWork
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.LoopToWord

/-- Expression value simulation and local work preservation use the same
actual compiler output and source/target states. No cost multiplier is added
at this pass; native execution of Word expressions still needs later lowering. -/
theorem loop_to_word_value_and_work {C F : Type}
    (source : LoopSemStateFiniteExact 64 F) (target : WordSemStateFiniteExact 64 C F)
    (context : Spt Nat) (expression : HolLoopExp 64) (value : WordLocW 64)
    (evaluated : LoopSemStateFiniteExact.eval source expression = some value)
    (dimension : goodDimindex 64)
    (related : loopToWordStateRelHOLExact source target)
    (locals : localsRelHOL context source.locals target.locals) :
    WordSemStateFiniteExact.wordExp target (compExpHOL context expression) = some value ∧
      wordExpressionWork (compExpHOL context expression) = loopValueWork expression :=
  ⟨compExpPreservesEval source expression value target context
    ⟨evaluated, dimension, related, locals⟩,
    loop_to_word_expression_work context expression⟩

#print axioms loop_to_word_value_and_work
end InitECandidate.Runtime.FineCost
