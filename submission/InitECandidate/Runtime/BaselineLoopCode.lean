import InitECandidate.Runtime.LoopWordEntry
import InitECandidate.Proofs.FrontendStages.Pass5
import Flapjack.Pancake.CrepToLoop.StateRel
import Flapjack.Pancake.Proofs.PanToWord.StateRelImpSemantics
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace InitECandidate.Runtime
open InitE InitECandidate.Proofs Flapjack
open Flapjack.Compiler.Encoders.RiscV.Target

/-- The actual generated Loop procedures have distinct parameters. -/
theorem baseline_loop_params :
    FrontendStages.pass4.all (fun entry => decide entry.2.1.Nodup) = true := by
  have bounded := crepToLoopCompileProgDistinctParamsHOLExact
    (compileProgDeclsHOLW FrontendStages.pass2) riscvConfig.isa
    (compileProgDeclsHOLW_params_nodup FrontendStages.pass2)
  rw [FrontendStages.pass3_eq,FrontendStages.pass4_eq] at bounded
  exact bounded

/-- Full code relation for the actual checked Loop-to-Word compiler artifacts. -/
theorem baseline_loop_word_codeRel : loopToWordCodeRelHOLExact
    (sptFromAList FrontendStages.pass4) (sptFromAList FrontendStages.pass5) := by
  intro name params body lookup
  constructor
  · rw [← FrontendStages.pass5_eq]
    exact loopToWordLookupProgSomeLookupCompileProg _ name params body lookup
  · apply of_decide_eq_true
    apply (List.all_eq_true.mp baseline_loop_params) (name,params,body)
    apply sptAListLookup_mem name FrontendStages.pass4 (params,body)
    simpa only [sptLookup_sptFromAList] using lookup

#print axioms baseline_loop_params
#print axioms baseline_loop_word_codeRel
end InitECandidate.Runtime
