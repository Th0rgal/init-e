import InitE
import InitECandidate.Solver.YukonSelfContainedCert
import InitECandidate.Solver.PanToTargetLinearClockAndGasMaster

namespace InitE.Challenge
open Flapjack
open InitECandidate.Proofs
open Flapjack.Compiler.Backend
open Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Pancake.Proofs.PanToTarget

/-- The initial submitted ROM includes its proved bootstrap and data initializer. -/
def submission : InitE.Submission := InitECandidate.Solver.FastEnv.baselineSubmission

def code : List (BitVec 8) := submission.code

/-- The original accelerated compilation claims no uniform finite step ceiling. -/
def claimedScore : InitE.NatE := .infinity

theorem code_size : code.length ≤ InitE.codeSizeLimit :=
  InitECandidate.Solver.FastEnv.baselineSubmission_admitted.code_limit

/-- Infinity requires actual finite termination under the compiler evaluator. -/
theorem machine_termination_iff_infinity {S Q σ : Type}
    (mc : MachineConfig 64 S Q) (ffi : HolFfiState σ) (ms : S) :
    (∃ outcome events, machineSemHOL mc ffi ms (.terminate outcome events)) ↔
      InitE.targetTerminatesWithin claimedScore mc ffi ms :=
  InitE.target_termination_iff_infinity mc ffi ms

/-- Finite step budget `K = 11,029,683,733` from the six-pass reduced master bridge. -/
def finiteK : Nat := InitECandidate.Solver.SelfContainedSixPassMaster.sixPassReducedK

/-- Baseline submission equipped with the finite step budget `finiteK`. -/
def finiteKSubmission : InitE.Submission :=
  InitECandidate.Solver.BoundedCertificate.baselineWithFiniteK finiteK

/-- Claimed score `.finite finiteK`. -/
def finiteKClaimedScore : InitE.NatE := .finite finiteK

/-- Admission certificate for `finiteKSubmission`. -/
theorem finiteK_admitted : finiteKSubmission.Admitted :=
  InitECandidate.Solver.BoundedCertificate.baselineWithFiniteK_admitted finiteK

/-- Self-contained finite-`K` certificate bridge at `finiteK = 11,029,683,733`. -/
theorem finiteK_certificate_of_not_timeOut
    (oracles : List (Option (Spt Nat))) (c : Backend.Config) (depth : Nat)
    (hlab : c.labConf = InitE.baselineLabConfig)
    (compiled : compileProgMaxAsmExecutable (oracleCompilerConfig oracles) riscvConfig
      sourceDeclarations = (some (InitECandidate.nativeCode, InitECandidate.bitmaps, c), some depth))
    (depthBound : depth ≤ 7480)
    (not_timeOut : ∀ input : Guest.InputBlob,
      Guest.GasLimit.declaredGasLimit input ≤ 200000000 →
      ∀ outcome events, sourceBehaviour input = .terminate outcome events →
      coveredOutcome outcome →
      (evaluateTargetHOL InitECandidate.Solver.FastEnv.baselineMachineConfig (sourceFfi input)
        finiteK (InitECandidate.Solver.FastEnv.baselineInitialState input)).1 ≠ .timeOut) :
    InitE.Certificate finiteKSubmission finiteKClaimedScore :=
  InitECandidate.Solver.SelfContainedSixPassMaster.reduced_finite_certificate
    oracles c depth hlab compiled depthBound not_timeOut

/-- Self-contained baseline `.infinity` certificate bridge via `YukonSelfContainedCert`. -/
theorem certificate
    (oracles : List (Option (Spt Nat))) (c : Backend.Config) (depth : Nat)
    (hlab : c.labConf = InitE.baselineLabConfig)
    (compiled : compileProgMaxAsmExecutable (oracleCompilerConfig oracles) riscvConfig
      sourceDeclarations = (some (InitECandidate.nativeCode, InitECandidate.bitmaps, c), some depth))
    (depthBound : depth ≤ 7480) :
    InitE.Certificate submission claimedScore :=
  InitECandidate.Solver.YukonSelfContainedCert.oracle_full_baseline_certificate
    oracles c depth hlab compiled depthBound

end InitE.Challenge

#print axioms InitE.Challenge.certificate
#print axioms InitE.Challenge.finiteK_certificate_of_not_timeOut
#print axioms InitE.Challenge.machine_termination_iff_infinity
