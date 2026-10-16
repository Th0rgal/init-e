import InitECandidate.Runtime.LabExtract
import Flapjack.Compiler.Backend.LabToTarget.Initialization.InitialStateContracts
import Flapjack.Compiler.Backend.LabToTarget.StateTransport
namespace InitECandidate.Runtime.LabToTarget
open Flapjack Flapjack.RiscV.L3 Flapjack.Misc
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.AsmSem
open Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend.LabProps
open Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Backend.Semantics.TargetProps Flapjack.Compiler.Encoders.RiscV.Target

/-- The original compiler initialization guards, without an assumed state relation. -/
abbrev NativeInitializationPremises {F : Type}
    (mc : MachineConfig 64 riscv_state RiscVProjection) (ms : riscv_state) (_ffi : HolFfiState F)
    (code code2 : LabProgHOL 64) (labs : Spt (Spt Nat))
    (clock i cbspace : Nat) (t : AsmState 64)
    (m : BitVec 64 → WordLocW 64) (dm sdm : BitVec 64 → Bool)
    (coracle : Nat → Config × LabProgHOL 64)
    (newFfiNames : List HolFfiName) (shmemInfo newShmemInfo : List ShmemInfoNum) : Prop :=
  goodCode mc.target.config (.ln : Spt (Spt Nat)) code ∧ mcConfOk mc ∧
    (noShareMemInst code → compilerOracleOk coracle labs (progToBytes code2).length
      mc.target.config mc.ffiNames) ∧
    listSubset ((findFfiNames code).filter (fun x => match x with
      | .extCall _ => true | _ => false)) (mc.ffiNames.take i) = true ∧
    removeLabels clock mc.target.config 0 .ln (mc.ffiNames.take i) code = some (code2,labs) ∧
    goodInitState mc ms (progToBytes code2) cbspace t m dm sdm ∧
    getShmemInfo code2 0 [] [] = (newFfiNames,shmemInfo) ∧
    newShmemInfo = shmemInfo.map (fun rec => { rec with
      entryPc := (mc.target.getPc ms).toNat + rec.entryPc,
      exitPc := (mc.target.getPc ms).toNat + rec.exitPc }) ∧
    mc.ffiNames.drop i = newFfiNames ∧ mmioPcsMinIndex mc.ffiNames = some i ∧
    newShmemInfo.map ShmemInfoNum.entryPc = (mc.ffiEntryPcs.map BitVec.toNat).drop i ∧
    mc.mmioInfo = List.zip ((List.range newShmemInfo.length).map (fun index => index+i))
      (newShmemInfo.map (fun rec => (rec.nbytes,
        HolAddr.addr rec.addrReg (BitVec.ofNat 64 rec.addrOff), rec.reg,
        BitVec.ofNat 64 rec.exitPc))) ∧
    noInstallOrNoShareMem code mc.ffiNames ∧
    (∀ bn, bn < cbspace → BitVec.ofNat 64 bn + BitVec.ofNat 64 (progToBytes code2).length +
      mc.target.getPc ms ∉ mc.ffiEntryPcs.take i)

theorem initialized_supported_native_bound {F : Type}
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
    ∃ count native, count ≤ (labStepCeiling code2 + 1) * fuel ∧
      evaluateTargetHOL mc ffi count ms = (.halt outcome, native, post.ffi) := by
  let initial := makeInit mc ffi t m dm sdm ms code (compileLab mc.target.config)
      (mc.target.getPc ms + BitVec.ofNat 64 (progToBytes code2).length) cbspace coracle
  have related := makeInit_stateRel (G := Nat) mc ms ffi code code2 labs clock i cbspace
    t m dm sdm coracle newFfiNames shmemInfo newShmemInfo premises
  have tie := oracleTie_makeInit mc ffi t m dm sdm ms code (compileLab mc.target.config)
    (mc.target.getPc ms + BitVec.ofNat 64 (progToBytes code2).length) cbspace coracle
  have encoder := premises.2.1.2.1
  exact supported_evaluation_native_bound {initial with clock := fuel} post outcome supported
    evaluated mc code2 labs (mc.target.getPc ms) t ms target encoder
    (stateRelClock _ initial t ms fuel related) (oracleTie_clock mc ms initial fuel tie)

#print axioms initialized_supported_native_bound
end InitECandidate.Runtime.LabToTarget
