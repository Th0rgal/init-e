import InitECandidate.Runtime.BaselineCrepLimit
import Flapjack.Pancake.Proofs.PanToWord
namespace InitECandidate.Runtime
open Flapjack InitECandidate.Proofs

/-- The compiler's actual initialized Crep state satisfies the fixed numeric
code-size ceiling, independently of input memory and source clock. -/
theorem baseline_crep_state_bounded {F : Type} (s : PanSemStateFiniteExact 64 F)
    (memory : BitVec 64 → HolWordLab 64) :
    CrepCodeSize baselineCrepLimit (crepStateHOL s FrontendStages.pass2 memory) := by
  apply baseline_crep_code_bounded
  change HolFiniteMapExact.empty.updateList (compileProgDeclsHOLW FrontendStages.pass2).reverse = _
  rw [FrontendStages.pass3_eq]

#print axioms baseline_crep_state_bounded
end InitECandidate.Runtime
