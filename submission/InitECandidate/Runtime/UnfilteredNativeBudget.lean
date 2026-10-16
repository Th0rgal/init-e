import InitECandidate.Runtime.CompiledNativeBudget
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

/-- Compilation to native code preserves the unfiltered source fuel ceiling. -/
theorem unfiltered_compiled_native_bound {F : Type}
    (mc : MachineConfig 64 riscv_state RiscVProjection) (ffi : HolFfiState F) (ms : riscv_state)
    (code : LabProgHOL 64) (asmConf : AsmConfigExact 64) (c cNext : Config)
    (bytes : List (BitVec 8)) (cbspace i : Nat) (t : AsmState 64)
    (m : BitVec 64 → WordLocW 64) (dm sdm : BitVec 64 → Bool)
    (coracle : Nat → Config × LabProgHOL 64) 
    (guards : CompilationInstallationPremises mc ffi ms code asmConf c cNext bytes cbspace i
      t m dm sdm coracle)
    (fuel : Nat) (post : State 64 Config F) (outcome : HolOutcome)
    (supported : SupportedCode (filterSkip code))
    (target : mc.target = riscvTarget)
    (evaluated : evaluate {makeInit mc ffi t m dm sdm ms code (compile mc.target.config)
        (mc.target.getPc ms + BitVec.ofNat 64 bytes.length) cbspace coracle with clock := fuel} = (.halt outcome, post)) :
    ∃ count native, count ≤ (16 * (bytes.length + 1) + 1) * fuel ∧
      evaluateTargetHOL mc ffi count ms = (.halt outcome, native, post.ffi) := by
  let original := {makeInit mc ffi t m dm sdm ms code (compile mc.target.config)
        (mc.target.getPc ms + BitVec.ofNat 64 bytes.length) cbspace coracle with clock := fuel}
  obtain ⟨filteredPost, filteredRun, ffiAgreement⟩ :=
    InitECandidate.Runtime.LabFilter.entry_same_clock original post outcome
      (compileLab mc.target.config) rfl rfl rfl evaluated
  have run : evaluate {makeInit mc ffi t m dm sdm ms (filterSkip code) (compileLab mc.target.config)
        (mc.target.getPc ms + BitVec.ofNat 64 bytes.length) cbspace
        (fun n => ((coracle n).1, filterSkip (coracle n).2)) with clock := fuel} = (.halt outcome, filteredPost) := by
    simpa only [original, makeInit] using filteredRun
  obtain ⟨count, native, bound, nativeRun⟩ := compiled_supported_native_bound mc ffi ms
    code asmConf c cNext bytes cbspace i t m dm sdm coracle guards fuel filteredPost outcome
    supported target run
  exact ⟨count, native, bound, by simpa only [ffiAgreement] using nativeRun⟩

/-- Both aligned domains preserve the same label-fuel ceiling before compilation. -/
theorem aligned_compiled_native_bound {F : Type}
    (mc : MachineConfig 64 riscv_state RiscVProjection) (ffi : HolFfiState F) (ms : riscv_state)
    (code : LabProgHOL 64) (asmConf : AsmConfigExact 64) (c cNext : Config)
    (bytes : List (BitVec 8)) (cbspace i : Nat) (t : AsmState 64)
    (m : BitVec 64 → WordLocW 64) (dm sdm : BitVec 64 → Bool)
    (coracle : Nat → Config × LabProgHOL 64) 
    (guards : CompilationInstallationPremises mc ffi ms code asmConf c cNext bytes cbspace i
      t m dm sdm coracle)
    (fuel : Nat) (post : State 64 Config F) (outcome : HolOutcome)
    (supported : SupportedCode (filterSkip code))
    (target : mc.target = riscvTarget)
    (evaluated : evaluate {makeInit mc ffi t m (fun a => dm a && holByteAligned a)
        (fun a => sdm a && holByteAligned a) ms code (compile mc.target.config)
        (mc.target.getPc ms + BitVec.ofNat 64 bytes.length) cbspace coracle with clock := fuel} = (.halt outcome, post)) :
    ∃ count native, count ≤ (16 * (bytes.length + 1) + 1) * fuel ∧
      evaluateTargetHOL mc ffi count ms = (.halt outcome, native, post.ffi) := by
  let original := {makeInit mc ffi t m dm sdm ms code (compile mc.target.config)
    (mc.target.getPc ms + BitVec.ofNat 64 bytes.length) cbspace coracle with clock := fuel}
  have alignedRun : evaluate (alignDm (alignSdm original)) = (.halt outcome, post) := evaluated
  obtain ⟨unalignedPost, run, ffiAgreement⟩ :=
    unalign_terminating_same_clock (Or.inr rfl) original post outcome alignedRun
  obtain ⟨count, native, bound, nativeRun⟩ := unfiltered_compiled_native_bound mc ffi ms
    code asmConf c cNext bytes cbspace i t m dm sdm coracle guards fuel unalignedPost outcome
    supported target run
  exact ⟨count, native, bound, by simpa only [ffiAgreement] using nativeRun⟩

#print axioms aligned_compiled_native_bound

#print axioms unfiltered_compiled_native_bound
end InitECandidate.Runtime.LabToTarget
