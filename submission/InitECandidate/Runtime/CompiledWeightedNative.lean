import InitECandidate.Runtime.CompiledNativeBudget
import InitECandidate.Runtime.LabWeightedInitialization
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

/-- Actual compilation/installation and successful source evaluation provide
an executed local-expansion budget; no trace or native run is assumed.
The removeLabels equation identifies the cost-bearing compiled program. -/
theorem compiled_supported_weighted_native_bound {F : Type}
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
    (evaluated : evaluate {makeInit mc ffi t m dm sdm ms (filterSkip code) (compileLab mc.target.config)
        (mc.target.getPc ms + BitVec.ofNat 64 bytes.length) cbspace
        (fun n => ((coracle n).1, filterSkip (coracle n).2)) with clock := fuel} = (.halt outcome, post)) :
    ∃ code2 labs work count native,
      bytes = progToBytes code2 ∧
      removeLabels c.initClock mc.target.config 0 .ln (mc.ffiNames.take i) (filterSkip code) =
        some (code2, labs) ∧
      WeightedMixedTrace code2
        {makeInit mc ffi t m dm sdm ms (filterSkip code) (compileLab mc.target.config)
          (mc.target.getPc ms + BitVec.ofNat 64 bytes.length) cbspace
          (fun n => ((coracle n).1, filterSkip (coracle n).2)) with clock := fuel} post work ∧
      count ≤ work + 17 ∧
      evaluateTargetHOL mc ffi count ms = (.halt outcome, native, post.ffi) := by
  obtain ⟨code2, labs, newNames, info, shiftedInfo, bytesEq, initialized⟩ :=
    compile_initialization_premises mc ffi ms code asmConf c cNext bytes cbspace i
      t m dm sdm coracle guards
  have run : evaluate {makeInit mc ffi t m dm sdm ms (filterSkip code)
      (compileLab mc.target.config)
      (mc.target.getPc ms + BitVec.ofNat 64 (progToBytes code2).length) cbspace
      (fun n => ((coracle n).1, filterSkip (coracle n).2)) with clock := fuel} =
      (.halt outcome, post) := by
    simpa only [bytesEq] using evaluated
  obtain ⟨work, count, native, trace, bound, nativeRun⟩ := initialized_supported_weighted_native_bound mc ms ffi
    (filterSkip code) code2 labs c.initClock i cbspace t m dm sdm
    (fun n => ((coracle n).1, filterSkip (coracle n).2)) newNames info shiftedInfo
    initialized fuel post outcome supported target run
  refine ⟨code2, labs, work, count, native, bytesEq, initialized.2.2.2.2.1, ?_, bound, nativeRun⟩
  simpa only [bytesEq] using trace

#print axioms compiled_supported_weighted_native_bound
end InitECandidate.Runtime.LabToTarget
