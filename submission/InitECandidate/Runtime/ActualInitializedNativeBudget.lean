import InitECandidate.Runtime.InitializedLabNativeBudget
import InitECandidate.Runtime.ActualSupportedCode
import Flapjack.Compiler.Backend.LabToTarget.Initialization.InitialStateContracts
import Flapjack.Compiler.Backend.LabToTarget.StateTransport
namespace InitECandidate.Runtime.LabToTarget
open Flapjack Flapjack.RiscV.L3 Flapjack.Misc
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.AsmSem
open Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend.LabProps
open Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Backend.Semantics.TargetProps Flapjack.Compiler.Encoders.RiscV.Target

/-- The actual compiled label program needs no caller-supplied support certificate. -/
theorem actual_initialized_native_bound {F : Type}
    (mc : MachineConfig 64 riscv_state RiscVProjection) (ms : riscv_state) (ffi : HolFfiState F)
    (code2 : LabProgHOL 64) (labs : Spt (Spt Nat))
    (clock i cbspace : Nat) (t : AsmState 64)
    (m : BitVec 64 → WordLocW 64) (dm sdm : BitVec 64 → Bool)
    (coracle : Nat → Config × LabProgHOL 64)
    (newFfiNames : List HolFfiName) (shmemInfo newShmemInfo : List ShmemInfoNum) 
    (premises : NativeInitializationPremises mc ms ffi InitECandidate.Proofs.BackendStages.Sections.program code2 labs clock i cbspace
      t m dm sdm coracle newFfiNames shmemInfo newShmemInfo)
    (fuel : Nat) (post : State 64 Config F) (outcome : HolOutcome)
    (target : mc.target = riscvTarget)
    (evaluated : evaluate {makeInit mc ffi t m dm sdm ms InitECandidate.Proofs.BackendStages.Sections.program (compileLab mc.target.config)
      (mc.target.getPc ms + BitVec.ofNat 64 (progToBytes code2).length) cbspace coracle with clock := fuel} = (.halt outcome, post)) :
    ∃ count native, count ≤ (labStepCeiling code2 + 1) * fuel ∧
      evaluateTargetHOL mc ffi count ms = (.halt outcome, native, post.ffi) := by
  exact initialized_supported_native_bound mc ms ffi InitECandidate.Proofs.BackendStages.Sections.program code2 labs clock i cbspace t m dm sdm coracle newFfiNames shmemInfo newShmemInfo premises fuel post outcome actual_supported target evaluated

#print axioms actual_initialized_native_bound
end InitECandidate.Runtime.LabToTarget
