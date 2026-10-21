import InitECandidate.Runtime.WordIselAll

namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend Flapjack.WordSemStateFiniteExact

/-- Whole instruction-selection cost transfer over the transformed code
table. The guarded callee obligation is discharged here by global induction
on termination depth and clock. No callee run or callee cost is assumed. The
install-free invariant of IselCode supplies eligibility for every actual
looked-up body, including indirect calls. -/
theorem isel_program_cost {C F : Type} (c : Compiler.Encoders.Asm.AsmConfigExact 64)
    (temp : Nat) (program : WordLangProgHOL (BitVec 64)) (noInstall : installFree program = true)
    (source target : WordSemStateFiniteExact 64 C F) (result : Option (WordSemResult 64))
    (post : WordSemStateFiniteExact 64 C F)
    (vars : everyVarHOL (fun x => decide (x < temp)) program = true)
    (related : IselRel c temp source target)
    (run : evaluate program source = (result, post)) (safe : result ≠ some .error) :
    ∃ targetPost, evaluate (WordInst.instSelectExecutable c temp program) target = (result, targetPost) ∧
      IselPost c temp result post targetPost ∧
      wordExecutionCost wordOptimizerLocalPrice (WordInst.instSelectExecutable c temp program) target ≤
        wordExecutionCost (preIselPrice c) program source := by
  apply isel_body_cost c temp program noInstall source target result post ?_ vars related run safe
  intro destination arity tempF body childSource childTarget childResult childPost
    found childVars foundTarget smaller childRelated childRun childSafe
  obtain ⟨_, _, _, childFree⟩ := (childRelated.2.1 destination).2 arity body found
  exact isel_program_cost c tempF body childFree childSource childTarget childResult childPost
    childVars childRelated childRun childSafe
termination_by (source.termdep, source.clock)
decreasing_by exact smaller

#print axioms isel_program_cost
end InitECandidate.Runtime.FineCost
