import Init
import InitECandidate.Solver.Op3ClockBound
import InitECandidate.Solver.LoopFuel

namespace InitECandidate.Solver.Op3PassInventory
open InitECandidate.Solver.Op3ClockBound
open InitECandidate.Solver.LoopFuel

/-- Inventory size of the pre-existing seven-pass solver cone. -/
def solverModuleCount : Nat := 67

def passModuleCount : Nat := 7

/-- Exact names of the 67 pre-existing solver modules in the Op3 cone. -/
def solverModules : List String := [
  "BoundedCertificate",
  "CrepToStackNamesAndLabToTargetEndToEndClockMaster",
  "FastBaselineEnv",
  "FastBoundedPanToWord",
  "FastBoundedStackToLab",
  "FastBoundedTarget",
  "FastHalt",
  "FlapjackElevenPassSimulationAndClockGrandMaster",
  "GuestGasAndSpecFixes",
  "GuestStepBound",
  "LabToTargetClock",
  "LabToTargetMultiStepBound",
  "LabToTargetSectionCleanPreservation",
  "LoopToWordToStackNamesAndLabToTargetClockMaster",
  "LoopWordStackExactClockIso",
  "PanToCrepClock",
  "PanToCrepExactClockIso",
  "PanToLabSectionAndStackRemoveClock",
  "PanToStackAllocIdentityAndUnconditionalNoGcCall",
  "PanToStackNamesEndToEndLinearClockMaster",
  "PanToStackNoStoreConsts",
  "PanToStackRawCallNoAllocAndStackAllocStructural",
  "PanToStackToLabUnconditionalNoStoreConsts",
  "PanToTargetLinearClockAndGasMaster",
  "PanToWordNoStoreConsts",
  "PanToWordNoStubCall",
  "PanToWordToStackNamesSimulationAndClockMaster",
  "RiscvBootAndCopyLoopCert",
  "RiscvFastPathsAndSailBridge",
  "RiscvSszFastRejectAndBootCert",
  "SelfContainedBasicBlockBridge",
  "SelfContainedBoundedCertificate",
  "SelfContainedCertificateModel",
  "SelfContainedEndToEndCert",
  "SelfContainedIsoReducedK",
  "SelfContainedMasterK",
  "SelfContainedPipelineBridge",
  "SelfContainedSixPassMaster",
  "SelfContainedStageBounds",
  "SelfContainedTargetBound",
  "SoftwareGuestHintedPrecompiles",
  "SourceTerminationBound",
  "StackNamesExactClockIso",
  "StackRawCallLinearClockAndZeroExtraBridge",
  "StackRawCallToStackNamesAndStackToLabLinearBridge",
  "StackRemoveAllocFreeAndBaseCasesZeroClock",
  "StackRemoveAndNamesNoStoreConsts",
  "StackRemoveClockOriginAudit",
  "StackRemoveDeadStub6AndUnconditionalCodeNoSt",
  "StackRemoveInitMemoryAndCompileProgZeroExtraBodyClock",
  "StackRemoveNoStoreConstsZeroExtraClock",
  "StackRemoveToStackNamesStateRelAndClockBridge",
  "StackToLabAndLabToTargetNoLocValue6",
  "StackToLabAndLabToTargetNoStubCall",
  "StackToLabClock",
  "VerifySpeedBound",
  "WordMidPassesPreserveNoStoreConsts",
  "WordPassesPreserveNoStoreConsts",
  "WordSimpPreservesNoStoreConsts",
  "WordSsaCsePreserveNoStoreConsts",
  "WordToStackClockExactOffset",
  "WordToStackSemanticMmioBound",
  "WordToWordFullCompileNoStoreConsts",
  "WordToWordNoStubCall",
  "YukonBaselineCompat",
  "YukonCleanVerifierCheck",
  "YukonSelfContainedCert"
]

theorem solverModules_count : solverModules.length = 67 := by decide

theorem solverModuleCount_eq : solverModuleCount = 67 := rfl
theorem passModuleCount_eq : passModuleCount = 7 := rfl

end InitECandidate.Solver.Op3PassInventory
