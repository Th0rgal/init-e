import InitECandidate.Runtime.CanonicalSourceLayout
import InitECandidate.Runtime.SelectedInitializerClock
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace InitECandidate.Runtime
open InitE InitECandidate.Proofs Flapjack Flapjack.Compiler.Backend
open Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInitSemantics
open Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInit

theorem entry_frontend_clock_zero {input : Guest.InputBlob} (entry : BaselineRuntimeEntry input) :
    (entryFrontendState entry).clock = 0 := by
  have bound := StackRemove.selected_clock_le (StackToLab.isGenGc baselineCompilerConfig.dataConf.gcKind)
    entryHeapLimit InitECandidate.bitmaps 0 (coracle1 (entryStackOracle entry.cfg))
    baselineCompilerConfig.stackConf.jump riscvConfig.addrOffset entrySp
    (sptFromAList (code1 baselineCompilerConfig.dataConf BackendStages.Native.stack))
    (s2 baselineCompilerConfig.stackConf baselineCompilerConfig.dataConf entryHeapLimit entrySp
      riscvConfig.addrOffset BackendStages.Native.stack
      (LabToTarget.baselineLabState input entry.cfg entry.asm entry.memory entry.bitmapDomain entry.sharedDomain)
      entrySaveRegs (entryStackOracle entry.cfg)) entry.source entry.selection
  change entry.source.clock ≤ 0 at bound
  change entry.source.clock = 0
  exact Nat.le_zero.mp bound

theorem canonical_pan_declaration_clock (input : Guest.InputBlob) :
    (canonicalPanDeclarationState input).clock = (sourceInitialState input).clock :=
  entry_frontend_clock_zero (canonicalRuntimeEntry input)

#print axioms entry_frontend_clock_zero
#print axioms canonical_pan_declaration_clock
end InitECandidate.Runtime
