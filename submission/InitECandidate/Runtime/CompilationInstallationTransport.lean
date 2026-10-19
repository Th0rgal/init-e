import InitECandidate.Runtime.CompiledNativeBudget
import InitECandidate.Proofs.InstallationTransport
namespace InitECandidate.Runtime.LabToTarget
open InitE Flapjack Flapjack.RiscV.L3
open Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.RiscV.Target

/-- Compiler guards survive the concrete installation agreement from bootstrap. -/
theorem compilationInstallation_transport {F : Type}
    (mc : MachineConfig 64 riscv_state RiscVProjection) (ffi : HolFfiState F)
    (before after : riscv_state) (agreement : InstallationAgreement mc before after)
    (code : LabProgHOL 64) (asmConf : AsmConfigExact 64) (c cNext : Config)
    (bytes : List (BitVec 8)) (cbspace i : Nat) (t : AsmState 64)
    (m : BitVec 64 → WordLocW 64) (dm sdm : BitVec 64 → Bool)
    (coracle : Nat → Config × LabProgHOL 64)
    (guards : CompilationInstallationPremises mc ffi before code asmConf c cNext
      bytes cbspace i t m dm sdm coracle) :
    CompilationInstallationPremises mc ffi after code asmConf c cNext
      bytes cbspace i t m dm sdm coracle := by
  rcases guards with ⟨ok, oracle, good, config, labels, pos, compiled, names,
    initialized, entries, mmio, noInstall, index, space, external⟩
  exact ⟨ok, oracle, good, config, labels, pos, compiled, names,
    goodInitState_transport agreement initialized,
    by simpa only [agreement.pc] using entries,
    by simpa only [agreement.pc] using mmio,
    noInstall, index, space, external⟩
end InitECandidate.Runtime.LabToTarget
#print axioms InitECandidate.Runtime.LabToTarget.compilationInstallation_transport
