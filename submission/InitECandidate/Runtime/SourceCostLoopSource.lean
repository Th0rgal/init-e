import InitECandidate.Runtime.SourceCostCrepBasis
import InitECandidate.Runtime.SourceCostLoopPricing
import InitECandidate.Runtime.SourceCostLoopOptimise
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.PanLang Flapjack.LoopSemStateFiniteExact Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect

/-- The pinned Pan-to-Crep result relation never relates a non-error source
result to a Crep `Error`. -/
theorem resultRel_not_error {F : Type} {context : PanToCrepContextExact 64}
    {post : PanSemStateFiniteExact 64 F} {t1 : CrepSemHOLState 64 F}
    {r : Option (PanSemResultExact 64)} {r1 : Option (CrepResultHOLExact 64)}
    (rel : pcCompileCorrectResultRel context post t1 r r1) : r1 ≠ some .error := by
  intro h
  subst h
  rcases r with _ | r
  · simp [pcCompileCorrectResultRel] at rel
  · cases r with
    | exception eid v =>
      simp only [pcCompileCorrectResultRel] at rel
      split at rel
      · exact rel
      · simp at rel
    | _ => simp [pcCompileCorrectResultRel] at rel

/-- The temporary `LoopOptimiseWork` contract, discharged by root's
`loop_optimise_executed_work` (coefficient one). -/
theorem loop_optimise_work : LoopOptimiseWork :=
  fun F q s r post w work nonerror noBreak noContinue =>
    loop_optimise_executed_work F q s r post w work nonerror noBreak noContinue

/-- Unconditional Crep-to-Loop transfer at exact Loop prices, factor one. -/
theorem crep_loop_installed_sharp_work {F : Type} {t : CrepSemHOLState 64 F} {p : CrepProgHOL 64}
    {w : Nat} (work : CrepWorkS t p w) (u : LoopSemStateFiniteExact 64 F)
    (context : CrepToLoopContextExact) (live : NumSet)
    (ok : (evalCrepSemHOLProgExact t p).1 ≠ some .error) (rel : CrepLoopRel context live t u) :
    LoopPaid context live t u p w :=
  crep_loop_sharp_work loop_optimise_work work u context live ok rel

#print axioms loop_optimise_work
#print axioms crep_loop_installed_sharp_work
#print axioms resultRel_not_error
end InitECandidate.Runtime.FineCost
