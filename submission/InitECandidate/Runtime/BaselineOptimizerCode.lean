import InitECandidate.Proofs.SourceStackCertificate
import InitECandidate.Proofs.BackendStages.Native
import Flapjack.Compiler.Backend.WordToWord.Proofs.CompileSemantics
import Flapjack.Pancake.Proofs.PanToWord.NoInstallCode
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace InitECandidate.Runtime
open InitE InitECandidate.Proofs Flapjack Flapjack.Compiler.Backend
open Flapjack.Compiler.Encoders.RiscV.Target

/-- The checked allocation tape produces exactly the submitted optimized Word code
under the logical compiler, without reducing the compiler on the closed guest. -/
theorem baseline_word_optimizer_compile :
    WordToWord.compile WordBackend.config riscvConfig FrontendStages.pass5 =
      ([],BackendStages.Native.programs0) := by
  have compiled := WordBackend.compileWith_eq
  rw [WordToWord.compileWith_eq_compile RegAlloc.regAllocExecutable
    RegAlloc.regAlloc_eq_executable.symm] at compiled
  have outputs : WordBackend.outputs = BackendStages.Native.programs0 :=
    WordBackend.StackAgreement.outputs_eq.trans rfl
  rw [outputs] at compiled
  exact compiled

theorem baseline_frontend_noInstall : WordProps.noInstallCode (sptFromAList FrontendStages.pass5) :=
  PanToWord.pan_to_word_compile_prog_no_install_code _ _ _ FrontendStages.frontend_eq

theorem baseline_frontend_noAlloc : WordProps.noAllocCode (sptFromAList FrontendStages.pass5) :=
  PanToWord.pan_to_word_compile_prog_no_alloc_code _ _ _ FrontendStages.frontend_eq

theorem baseline_frontend_noMt : WordProps.noMtCode (sptFromAList FrontendStages.pass5) :=
  PanToWord.pan_to_word_compile_prog_no_mt_code _ _ _ FrontendStages.frontend_eq

/-- Exact actual frontend-to-optimized code relation, including checked allocation. -/
theorem baseline_optimizer_codeRel : WordToWord.codeRel
    (sptFromAList FrontendStages.pass5) (sptFromAList BackendStages.Native.programs0) := by
  apply WordToWord.no_mt_code_rel_ext
  exact ⟨baseline_frontend_noMt,
    WordToWord.code_rel_ext_word_to_word riscvConfig _ _ _ _ baseline_word_optimizer_compile⟩

/-- Key domains are preserved by the logical Word optimizer's zipped map. -/
theorem optimizer_domain_eq {width : Nat} [NeZero width]
    (config : WordToWord.Config) (asm : Compiler.Encoders.Asm.AsmConfigExact width)
    (source output : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (oracles : List (Option (Spt Nat)))
    (compiled : WordToWord.compile config asm source = (oracles,output)) :
    sptDomain (sptFromAList source) = sptDomain (sptFromAList output) := by
  simp only [WordToWord.compile, Prod.mk.injEq] at compiled
  obtain ⟨_,rfl⟩ := compiled
  funext key
  simp only [sptDomain, sptLookup_sptFromAList]
  rw [WordToWord.sptAListLookup_isSome_map_fullCompileSingle _ _ _ _ source _
    (WordToWord.compile_zip_length config source) key]

theorem baseline_optimizer_domain :
    sptDomain (sptFromAList FrontendStages.pass5) =
      sptDomain (sptFromAList BackendStages.Native.programs0) :=
  optimizer_domain_eq _ _ _ _ _ baseline_word_optimizer_compile

#print axioms baseline_word_optimizer_compile
#print axioms baseline_optimizer_codeRel
#print axioms baseline_optimizer_domain
#print axioms baseline_frontend_noInstall
#print axioms baseline_frontend_noAlloc
#print axioms baseline_frontend_noMt
end InitECandidate.Runtime
