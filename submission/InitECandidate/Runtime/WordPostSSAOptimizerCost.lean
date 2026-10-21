import InitECandidate.Runtime.WordCseExecutedCorrect
import InitECandidate.Runtime.WordCopyExecutedCorrect
import InitECandidate.Runtime.WordUnreachExecutedCorrect
import InitECandidate.Runtime.WordRemoveDeadCost
import Flapjack.Pancake.Proofs.WordConvs.RemoveDead
import Flapjack.Pancake.Proofs.WordConvs.WordCse
import Flapjack.Pancake.Proofs.WordConvs.CopyProp
import Flapjack.Pancake.Proofs.WordConvs.Unreach

namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend Flapjack.WordSemStateFiniteExact

/-- The pinned RISC-V optimizer fragment after SSA and before colouring.
The three-to-two flag is false in this architecture's executed pipeline. -/
def postSSAOptimize (program : WordLangProgHOL (BitVec 64)) : WordLangProgHOL (BitVec 64) :=
  WordAlloc.removeDeadProg
    (WordUnreach.removeUnreach
      (WordInst.threeToTwoRegProg false
        (WordCopy.copyProp (WordCse.wordCommonSubexpElim (WordAlloc.removeDeadProg program)))))

theorem removeDeadProgPost_trans (result : Option (WordSemResult 64))
    (first middle final : Spt (WordLocW 64))
    (left : RemoveDeadProgPost result first middle)
    (right : RemoveDeadProgPost result middle final) : RemoveDeadProgPost result first final := by
  cases result with
  | none => trivial
  | some outcome => cases outcome <;> simp_all [RemoveDeadProgPost]

/-- Whole local post-SSA optimizer composition, on the exact RISC-V pass
order. All intermediate runs, flat-convention premises and cost comparisons
are derived. The coefficient stays one; no repeated multiplicative envelope
is introduced by optimization. Code-table lifting and colouring are separate
compiler stages. -/
theorem postSSAOptimize_executed_correct {C F : Type}
    (config : Compiler.Encoders.Asm.AsmConfigExact 64)
    (program : WordLangProgHOL (BitVec 64)) (source post : WordSemStateFiniteExact 64 C F)
    (result : Option (WordSemResult 64)) (flat : flatExpConventions program = true)
    (run : evaluate program source = (result, post)) (safe : result ≠ some .error) :
    ∃ locals,
      evaluate (postSSAOptimize program) source = (result, {post with locals := locals}) ∧
      RemoveDeadProgPost result post.locals locals ∧
      wordExecutionCost wordOptimizerLocalPrice (postSSAOptimize program) source ≤
        wordExecutionCost wordOptimizerLocalPrice program source := by
  let p1 := WordAlloc.removeDeadProg program
  let p2 := WordCse.wordCommonSubexpElim p1
  let p3 := WordCopy.copyProp p2
  let p4 := WordUnreach.removeUnreach p3
  obtain ⟨locals1, run1, post1, cost1⟩ := removeDeadProg_run_cost program source post result flat run safe
  have flat1 : flatExpConventions p1 = true :=
    (WordConvs.removeDeadProgConventions (fun _ => true) program config).1 flat
  obtain ⟨run2, cost2⟩ := word_common_subexp_elim_executed_correct p1 source
    {post with locals := locals1} result run1 flat1 safe
  have run2p : evaluate p2 source = (result, {post with locals := locals1}) := run2
  have flat2 : flatExpConventions p2 = true :=
    WordConvs.flat_exp_conventions_word_common_subexp_elim p1 flat1
  obtain ⟨run3Eq, cost3⟩ := copyProp_executed_correct p2 source (by simpa only [run2p] using safe)
  have run3 : evaluate p3 source = (result, {post with locals := locals1}) := run3Eq.trans run2
  have flat3 : flatExpConventions p3 = true := WordConvs.flat_exp_conventions_copy_prop p2 flat2
  obtain ⟨run4Eq, cost4⟩ := optimizer_removeUnreach_executed_correct p3 source
    (by simpa only [run3] using safe)
  have run4 : evaluate p4 source = (result, {post with locals := locals1}) := run4Eq.trans run3
  have flat4 : flatExpConventions p4 = true := WordConvs.flatExpConventions_removeUnreach p3 flat3
  obtain ⟨locals2, run5, post5, cost5⟩ := removeDeadProg_run_cost p4 source
    {post with locals := locals1} result flat4 run4 safe
  refine ⟨locals2, ?_, removeDeadProgPost_trans result post.locals locals1 locals2 post1 post5, ?_⟩
  · exact run5
  · exact cost5.trans (cost4.trans (cost3.trans (cost2.trans cost1)))

#print axioms removeDeadProgPost_trans
#print axioms postSSAOptimize_executed_correct
end InitECandidate.Runtime.FineCost
