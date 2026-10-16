import InitECandidate.Runtime.CompileNativeInitialization
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

/-- Original compilation and installation guards; no semantic execution premise. -/
abbrev CompilationInstallationPremises {F : Type}
    (mc : MachineConfig 64 riscv_state RiscVProjection) (_ffi : HolFfiState F) (ms : riscv_state)
    (code : LabProgHOL 64) (asmConf : AsmConfigExact 64) (c cNext : Config)
    (bytes : List (BitVec 8)) (cbspace i : Nat) (t : AsmState 64)
    (m : BitVec 64 → WordLocW 64) (dm sdm : BitVec 64 → Bool)
    (coracle : Nat → Config × LabProgHOL 64) : Prop :=
  mcConfOk mc ∧
    (noShareMemInst code → compilerOracleOk coracle cNext.labels bytes.length asmConf mc.ffiNames) ∧
    goodCode mc.target.config (.ln : Spt (Spt Nat)) code ∧
    asmConf = mc.target.config ∧ c.labels = .ln ∧ c.pos = 0 ∧
    compile asmConf c code = some (bytes,cNext) ∧ cNext.ffiNames = some mc.ffiNames ∧
    goodInitState mc ms bytes cbspace t m dm sdm ∧
    cNext.shmemExtra.map (fun rec => (mc.target.getPc ms).toNat + rec.entryPc) =
      (mc.ffiEntryPcs.map BitVec.toNat).drop i ∧
    mc.mmioInfo = List.zip ((List.range cNext.shmemExtra.length).map (fun index => index+i))
      (cNext.shmemExtra.map (fun rec => (rec.nbytes,
        HolAddr.addr rec.addrReg (BitVec.ofNat 64 rec.addrOff), rec.reg,
        BitVec.ofNat 64 rec.exitPc + mc.target.getPc ms))) ∧
    noInstallOrNoShareMem code mc.ffiNames ∧ mmioPcsMinIndex mc.ffiNames = some i ∧
    cbspace+bytes.length+ffiOffset*(i+3) < 2^64 ∧
    (∀ ffis, c.ffiNames = some ffis → ∀ name ∈ ffis, ∃ s, name = .extCall s)

theorem compiled_supported_native_bound {F : Type}
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
    ∃ count native, count ≤ (16 * (bytes.length + 1) + 1) * fuel ∧
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
  obtain ⟨count, native, bound, nativeRun⟩ := initialized_supported_native_bound mc ms ffi
    (filterSkip code) code2 labs c.initClock i cbspace t m dm sdm
    (fun n => ((coracle n).1, filterSkip (coracle n).2)) newNames info shiftedInfo
    initialized fuel post outcome supported target run
  refine ⟨count, native, ?_, nativeRun⟩
  simpa only [labStepCeiling, bytesEq] using bound

/-- The participant artifact supplies its own filtered syntax certificate. -/
theorem actual_compiled_native_bound {F : Type}
    (mc : MachineConfig 64 riscv_state RiscVProjection) (ffi : HolFfiState F) (ms : riscv_state)
    (asmConf : AsmConfigExact 64) (c cNext : Config)
    (bytes : List (BitVec 8)) (cbspace i : Nat) (t : AsmState 64)
    (m : BitVec 64 → WordLocW 64) (dm sdm : BitVec 64 → Bool)
    (coracle : Nat → Config × LabProgHOL 64) 
    (guards : CompilationInstallationPremises mc ffi ms InitECandidate.Proofs.BackendStages.Sections.program asmConf c cNext bytes cbspace i
      t m dm sdm coracle)
    (fuel : Nat) (post : State 64 Config F) (outcome : HolOutcome)
    (target : mc.target = riscvTarget)
    (evaluated : evaluate {makeInit mc ffi t m dm sdm ms (filterSkip InitECandidate.Proofs.BackendStages.Sections.program) (compileLab mc.target.config)
        (mc.target.getPc ms + BitVec.ofNat 64 bytes.length) cbspace
        (fun n => ((coracle n).1, filterSkip (coracle n).2)) with clock := fuel} = (.halt outcome, post)) :
    ∃ count native, count ≤ (16 * (bytes.length + 1) + 1) * fuel ∧
      evaluateTargetHOL mc ffi count ms = (.halt outcome, native, post.ffi) := by
  exact compiled_supported_native_bound mc ffi ms
    InitECandidate.Proofs.BackendStages.Sections.program asmConf c cNext bytes cbspace i
    t m dm sdm coracle guards fuel post outcome actual_filtered_supported target evaluated

#print axioms actual_compiled_native_bound

#print axioms compiled_supported_native_bound
end InitECandidate.Runtime.LabToTarget
