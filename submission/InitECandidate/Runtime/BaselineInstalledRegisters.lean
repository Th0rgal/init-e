import InitECandidate.Runtime.BaselineWordMemoryActualJoint
import InitECandidate.Proofs.PanInstallationCore
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
namespace InitECandidate.Runtime
open InitE Flapjack Flapjack.Compiler.Backend

/-- Original machine-state installation relation fixes the incoming heap,
stack-boundary and RAM-limit registers to the actual bootstrapped values. -/
theorem baseline_good_init_registers (asm : AsmState 64)
    (memory : BitVec 64 → WordLocW 64) (domain shared : BitVec 64 → Bool)
    (initialized : goodInitState baselineMachineConfig baselineInstalledState InitECandidate.nativeCode
      620 asm memory domain shared) :
    asm.regs 11 = BitVec.ofNat 64 sourceBase ∧
    asm.regs 12 = BitVec.ofNat 64 stackStart ∧
    asm.regs 13 = BitVec.ofNat 64 ramEnd := by
  have heap := initialized.1.2.2.2.1 11 ⟨by decide,by decide⟩
  have stack := initialized.1.2.2.2.1 12 ⟨by decide,by decide⟩
  have limit := initialized.1.2.2.2.1 13 ⟨by decide,by decide⟩
  have concreteHeap : baselineMachineConfig.target.getReg baselineInstalledState 11 = BitVec.ofNat 64 sourceBase := by decide_cbv
  have concreteStack : baselineMachineConfig.target.getReg baselineInstalledState 12 = BitVec.ofNat 64 stackStart := by decide_cbv
  have concreteLimit : baselineMachineConfig.target.getReg baselineInstalledState 13 = BitVec.ofNat 64 ramEnd := by decide_cbv
  exact ⟨heap.symm.trans concreteHeap,stack.symm.trans concreteStack,limit.symm.trans concreteLimit⟩

#print axioms baseline_good_init_registers
end InitECandidate.Runtime
