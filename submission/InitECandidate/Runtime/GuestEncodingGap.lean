import InitECandidate.Runtime.LabPositionGapScan
import InitECandidate.Proofs.BackendStages.Final
namespace InitECandidate.Runtime.StackToLab
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 100000000

/-- Kernel-checked local encoding span of the participant guest artifact. -/
theorem guest_gapScan : gapScan 24 0
    (InitECandidate.Proofs.BackendStages.Final.padded0.flatMap (fun sec => sec.lines)) = true := by
  decide_cbv

theorem guest_encodedLineWords : encodedLineWords
    InitECandidate.Proofs.BackendStages.Final.padded0 ≤ 6 :=
  gapScan_encodedLineWords guest_gapScan

#print axioms guest_gapScan
#print axioms guest_encodedLineWords
end InitECandidate.Runtime.StackToLab
