import InitECandidate.Proofs.ArtifactComposition
import InitECandidate.Proofs.BackendStages.Sections
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace InitECandidate.Runtime.LabToTarget
open InitE InitECandidate.Proofs
open Flapjack Flapjack.Compiler.Backend
open Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Pancake.Proofs.PanToTarget

/-- Identify the Word program returned by the proof-side compiler using the
existing kernel-checked frontend and allocation certificates. -/
theorem baseline_word_program : WordToWord.compile baselineCompilerConfig.wordToWordConf
    riscvConfig (panToWordCompileProgHOL riscvConfig.isa sourceDeclarations) =
    ([], BackendStages.Native.programs0) := by
  rw [← WordToWord.compileWith_eq_compile RegAlloc.regAllocExecutable
    (by funext a b c d e f g; exact RegAlloc.regAllocExecutable_eq a b c d e f g),
    FrontendStages.frontend_eq]
  change WordToWord.compileWith RegAlloc.regAllocExecutable WordBackend.config
    riscvConfig WordBackend.inputs = ([], BackendStages.Native.programs0)
  have programsEq : BackendStages.Native.programs0 = StackAnalysis.outputs :=
    BackendStages.Native.programs_eq
  rw [WordBackend.compileWith_eq, WordBackend.StackAgreement.outputs_eq, ← programsEq]

/-- Compiler-result uniqueness identifies the concrete pre-RawCall stack code. -/
theorem baseline_stack_program
    (col : List (Option (Spt Nat))) (word : List (Nat × Nat × WordLangProgHOL (BitVec 64)))
    (bm : List (BitVec 64)) (wc : WordToStack.Native.Config) (fs : List Nat)
    (stack : List (Nat × StackLang.HolProg 64))
    (wordRun : WordToWord.compile baselineCompilerConfig.wordToWordConf riscvConfig
      (panToWordCompileProgHOL riscvConfig.isa sourceDeclarations) = (col, word))
    (stackRun : WordToStack.Native.compileNative riscvConfig false word = (bm, wc, fs, stack)) :
    stack = BackendStages.Native.stack := by
  rw [baseline_word_program] at wordRun
  have wordEq := (Prod.mk.inj wordRun).2
  rw [← wordEq, BackendStages.Native.native_eq] at stackRun
  exact (Prod.mk.inj (Prod.mk.inj (Prod.mk.inj stackRun).2).2).2.symm

/-- The backend label program is the exact artifact whose syntax is certified. -/
theorem baseline_sections_program :
    StackToLab.compile baselineCompilerConfig.stackConf baselineCompilerConfig.dataConf
      (2 * DataToWord.maxHeapLimit 64 baselineCompilerConfig.dataConf - 1)
      (riscvConfig.regCount - (riscvConfig.avoidRegs.length + 3))
      riscvConfig.addrOffset BackendStages.Native.stack = BackendStages.Sections.program :=
  BackendStages.Sections.compile_eq

#print axioms baseline_word_program
#print axioms baseline_stack_program
#print axioms baseline_sections_program
end InitECandidate.Runtime.LabToTarget
