import InitECandidate.Runtime.LabWeightedExtract
import InitECandidate.Runtime.InitializedLabNativeBudget
import Flapjack.Compiler.Backend.LabToTarget.Initialization.InitialStateContracts
import Flapjack.Compiler.Backend.LabToTarget.StateTransport
namespace InitECandidate.Runtime.LabToTarget
open Flapjack Flapjack.RiscV.L3 Flapjack.Misc
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.AsmSem
open Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend.LabProps
open Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Backend.Semantics.TargetProps Flapjack.Compiler.Encoders.RiscV.Target

/-- Derive the initial relation from the original installation guards and
retain executed local expansion work, rather than a ROM-size factor. -/
theorem initialized_supported_weighted_native_bound {F : Type}
    (mc : MachineConfig 64 riscv_state RiscVProjection) (ms : riscv_state) (ffi : HolFfiState F)
    (code code2 : LabProgHOL 64) (labs : Spt (Spt Nat))
    (clock i cbspace : Nat) (t : AsmState 64)
    (m : BitVec 64 → WordLocW 64) (dm sdm : BitVec 64 → Bool)
    (coracle : Nat → Config × LabProgHOL 64)
    (newFfiNames : List HolFfiName) (shmemInfo newShmemInfo : List ShmemInfoNum) 
    (premises : NativeInitializationPremises mc ms ffi code code2 labs clock i cbspace
      t m dm sdm coracle newFfiNames shmemInfo newShmemInfo)
    (fuel : Nat) (post : State 64 Config F) (outcome : HolOutcome)
    (supported : SupportedCode code)
    (target : mc.target = riscvTarget)
    (evaluated : evaluate {makeInit mc ffi t m dm sdm ms code (compileLab mc.target.config)
      (mc.target.getPc ms + BitVec.ofNat 64 (progToBytes code2).length) cbspace coracle with clock := fuel} = (.halt outcome, post)) :
    ∃ work count native,
      WeightedMixedTrace code2
        {makeInit mc ffi t m dm sdm ms code (compileLab mc.target.config)
          (mc.target.getPc ms + BitVec.ofNat 64 (progToBytes code2).length) cbspace coracle
          with clock := fuel} post work ∧ count ≤ work + 17 ∧
      evaluateTargetHOL mc ffi count ms = (.halt outcome, native, post.ffi) := by
  let initial := makeInit mc ffi t m dm sdm ms code (compileLab mc.target.config)
      (mc.target.getPc ms + BitVec.ofNat 64 (progToBytes code2).length) cbspace coracle
  have related := makeInit_stateRel (G := Nat) mc ms ffi code code2 labs clock i cbspace
    t m dm sdm coracle newFfiNames shmemInfo newShmemInfo premises
  have tie := oracleTie_makeInit mc ffi t m dm sdm ms code (compileLab mc.target.config)
    (mc.target.getPc ms + BitVec.ofNat 64 (progToBytes code2).length) cbspace coracle
  have encoder := premises.2.1.2.1
  exact supported_evaluation_weighted_native_bound {initial with clock := fuel} post outcome supported
    evaluated mc code2 labs (mc.target.getPc ms) t ms target encoder
    (stateRelClock _ initial t ms fuel related) (oracleTie_clock mc ms initial fuel tie)

#print axioms initialized_supported_weighted_native_bound
end InitECandidate.Runtime.LabToTarget
