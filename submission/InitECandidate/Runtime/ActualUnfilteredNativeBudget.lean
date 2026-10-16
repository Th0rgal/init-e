import InitECandidate.Runtime.UnfilteredNativeBudget
import InitECandidate.Runtime.LabFilterBudget
import InitECandidate.Runtime.LabAlignmentBudget
import InitECandidate.Runtime.FilteredSupportedCode
import Flapjack.Compiler.Backend.LabToTarget.SemanticsCompile
namespace InitECandidate.Runtime.LabToTarget
open Flapjack Flapjack.RiscV.L3
open Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend.LabLang
open Flapjack.Compiler.Backend.LabProps Flapjack.Compiler.Backend.LabProps.LabelSets
open Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Encoders.Asm Flapjack.Misc
open Flapjack.Compiler.Backend.LabFilter
open Flapjack.Compiler.Backend.LabToTarget.FilterSkip
open Flapjack.Compiler.Encoders.RiscV.Target


/-- The actual artifact discharges the syntax premise internally. -/
theorem actual_unfiltered_compiled_native_bound {F : Type}
    (mc : MachineConfig 64 riscv_state RiscVProjection) (ffi : HolFfiState F) (ms : riscv_state)
    (asmConf : AsmConfigExact 64) (c cNext : Config)
    (bytes : List (BitVec 8)) (cbspace i : Nat) (t : AsmState 64)
    (m : BitVec 64 → WordLocW 64) (dm sdm : BitVec 64 → Bool)
    (coracle : Nat → Config × LabProgHOL 64) 
    (guards : CompilationInstallationPremises mc ffi ms InitECandidate.Proofs.BackendStages.Sections.program asmConf c cNext bytes cbspace i
      t m dm sdm coracle)
    (fuel : Nat) (post : State 64 Config F) (outcome : HolOutcome)
    (target : mc.target = riscvTarget)
    (evaluated : evaluate {makeInit mc ffi t m dm sdm ms InitECandidate.Proofs.BackendStages.Sections.program (compile mc.target.config)
        (mc.target.getPc ms + BitVec.ofNat 64 bytes.length) cbspace coracle with clock := fuel} = (.halt outcome, post)) :
    ∃ count native, count ≤ (16 * (bytes.length + 1) + 1) * fuel ∧
      evaluateTargetHOL mc ffi count ms = (.halt outcome, native, post.ffi) := by
  exact unfiltered_compiled_native_bound mc ffi ms
    InitECandidate.Proofs.BackendStages.Sections.program asmConf c cNext bytes cbspace i
    t m dm sdm coracle guards fuel post outcome actual_filtered_supported target evaluated

#print axioms actual_unfiltered_compiled_native_bound

/-- The actual artifact discharges the syntax premise internally. -/
theorem actual_aligned_compiled_native_bound {F : Type}
    (mc : MachineConfig 64 riscv_state RiscVProjection) (ffi : HolFfiState F) (ms : riscv_state)
    (asmConf : AsmConfigExact 64) (c cNext : Config)
    (bytes : List (BitVec 8)) (cbspace i : Nat) (t : AsmState 64)
    (m : BitVec 64 → WordLocW 64) (dm sdm : BitVec 64 → Bool)
    (coracle : Nat → Config × LabProgHOL 64) 
    (guards : CompilationInstallationPremises mc ffi ms InitECandidate.Proofs.BackendStages.Sections.program asmConf c cNext bytes cbspace i
      t m dm sdm coracle)
    (fuel : Nat) (post : State 64 Config F) (outcome : HolOutcome)
    (target : mc.target = riscvTarget)
    (evaluated : evaluate {makeInit mc ffi t m (fun a => dm a && holByteAligned a)
        (fun a => sdm a && holByteAligned a) ms InitECandidate.Proofs.BackendStages.Sections.program (compile mc.target.config)
        (mc.target.getPc ms + BitVec.ofNat 64 bytes.length) cbspace coracle with clock := fuel} = (.halt outcome, post)) :
    ∃ count native, count ≤ (16 * (bytes.length + 1) + 1) * fuel ∧
      evaluateTargetHOL mc ffi count ms = (.halt outcome, native, post.ffi) := by
  exact aligned_compiled_native_bound mc ffi ms
    InitECandidate.Proofs.BackendStages.Sections.program asmConf c cNext bytes cbspace i
    t m dm sdm coracle guards fuel post outcome actual_filtered_supported target evaluated

#print axioms actual_aligned_compiled_native_bound
end InitECandidate.Runtime.LabToTarget
