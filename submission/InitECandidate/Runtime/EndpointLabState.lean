import InitECandidate.Runtime.BaselineLabNativeBudget
namespace InitECandidate.Runtime.LabToTarget
open Flapjack.Compiler.Encoders.RiscV.Target
open InitE InitECandidate.Proofs Flapjack Flapjack.RiscV.L3 Flapjack.Compiler.Backend Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend.LabToTarget
noncomputable def endpointLabState (input : Guest.InputBlob) (endpoint : riscv_state) (ltconf : LabToTarget.Config)
    (t : AsmState 64) (m : BitVec 64 → WordLocW 64)
    (bitmapsDm sdm : BitVec 64 → Bool) : State 64 Config Guest.HostMemory :=
  makeInit baselineMachineConfig (sourceFfi input) t m
    (fun a => (decide
      (t.regs (StackNames.findNameSpt baselineCompilerConfig.stackConf.regNames 2) ≤ a ∧
       a < t.regs (StackNames.findNameSpt baselineCompilerConfig.stackConf.regNames 4)) ||
      bitmapsDm a) && holByteAligned a)
    (fun a => sdm a && holByteAligned a) endpoint BackendStages.Sections.program
    (compile riscvConfig)
    (baselineMachineConfig.target.getPc endpoint +
      BitVec.ofNat 64 InitECandidate.nativeCode.length) 620
    (fun _ => (ltconf, StackToLab.compileNoStubs baselineCompilerConfig.stackConf.regNames
      baselineCompilerConfig.stackConf.jump riscvConfig.addrOffset
      (riscvConfig.regCount - (riscvConfig.avoidRegs.length + 3)) []))


end InitECandidate.Runtime.LabToTarget

#print axioms InitECandidate.Runtime.LabToTarget.endpointLabState
