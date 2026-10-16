import InitECandidate.Proofs.BaselineInstallationFacts
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace InitECandidate.Runtime.LabToTarget
open InitE Flapjack Flapjack.Pancake.Proofs.PanToTarget
open Flapjack.Compiler.Encoders.RiscV.Target

/-- Convert the certified artifact to the logical compiler's artifact projection
without reducing the compiler on the concrete guest. -/
theorem baseline_compiler_projection :
    (compileProgMax baselineCompilerConfig baselineMachineConfig sourceDeclarations).1 =
      some (InitECandidate.nativeCode, InitECandidate.bitmaps, baselineConfig) :=
  (congrArg Prod.fst
    (compileProgMaxAsmExecutable_eq baselineCompilerConfig baselineMachineConfig
      sourceDeclarations).symm).trans
    ((compileProgAsmFast_eq_fst baselineCompilerConfig riscvConfig sourceDeclarations).symm.trans
      baseline_compiler_artifact_eq)

#print axioms baseline_compiler_projection
end InitECandidate.Runtime.LabToTarget
