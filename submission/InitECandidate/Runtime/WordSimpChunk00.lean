import InitECandidate.Runtime.WordSimpTab
import InitECandidate.Proofs.CompilerStages
import InitECandidate.Proofs.WordStages.Source64
import InitECandidate.Proofs.WordStages.Source65
import InitECandidate.Proofs.WordStages.Source66
import InitECandidate.Proofs.WordStages.Source67
import InitECandidate.Proofs.WordStages.Source68
import InitECandidate.Proofs.WordStages.Source69
import InitECandidate.Proofs.WordStages.Source70
import InitECandidate.Proofs.WordStages.Source71
import InitECandidate.Proofs.WordStages.Source72
import InitECandidate.Proofs.WordStages.Source73
import InitECandidate.Proofs.WordStages.Source74
import InitECandidate.Proofs.WordStages.Source75
import InitECandidate.Proofs.WordStages.Source76
import InitECandidate.Proofs.WordStages.Source77
import InitECandidate.Proofs.WordStages.Source78
import InitECandidate.Proofs.WordStages.Source79
import InitECandidate.Proofs.WordStages.Source80
import InitECandidate.Proofs.WordStages.Source81
import InitECandidate.Proofs.WordStages.Source82
import InitECandidate.Proofs.WordStages.Source83
import InitECandidate.Proofs.WordStages.Source84
import InitECandidate.Proofs.WordStages.Source85
import InitECandidate.Proofs.WordStages.Source86
import InitECandidate.Proofs.WordStages.Source87
import InitECandidate.Proofs.WordStages.Source88
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target

theorem wsCf_64 : cfOkB riscvConfig wsT1 (WordSimp.seqAssoc .skip InitECandidate.Proofs.WordStages.source64.2.2) .ln = true := by decide +kernel
theorem wsSd_64 : sdiOkB riscvConfig wsT2 (constFpF (WordSimp.seqAssoc .skip InitECandidate.Proofs.WordStages.source64.2.2)) = true := by decide +kernel
theorem wsCf_65 : cfOkB riscvConfig wsT1 (WordSimp.seqAssoc .skip InitECandidate.Proofs.WordStages.source65.2.2) .ln = true := by decide +kernel
theorem wsSd_65 : sdiOkB riscvConfig wsT2 (constFpF (WordSimp.seqAssoc .skip InitECandidate.Proofs.WordStages.source65.2.2)) = true := by decide +kernel
theorem wsCf_66 : cfOkB riscvConfig wsT1 (WordSimp.seqAssoc .skip InitECandidate.Proofs.WordStages.source66.2.2) .ln = true := by decide +kernel
theorem wsSd_66 : sdiOkB riscvConfig wsT2 (constFpF (WordSimp.seqAssoc .skip InitECandidate.Proofs.WordStages.source66.2.2)) = true := by decide +kernel
theorem wsCf_67 : cfOkB riscvConfig wsT1 (WordSimp.seqAssoc .skip InitECandidate.Proofs.WordStages.source67.2.2) .ln = true := by decide +kernel
theorem wsSd_67 : sdiOkB riscvConfig wsT2 (constFpF (WordSimp.seqAssoc .skip InitECandidate.Proofs.WordStages.source67.2.2)) = true := by decide +kernel
theorem wsCf_68 : cfOkB riscvConfig wsT1 (WordSimp.seqAssoc .skip InitECandidate.Proofs.WordStages.source68.2.2) .ln = true := by decide +kernel
theorem wsSd_68 : sdiOkB riscvConfig wsT2 (constFpF (WordSimp.seqAssoc .skip InitECandidate.Proofs.WordStages.source68.2.2)) = true := by decide +kernel
theorem wsCf_69 : cfOkB riscvConfig wsT1 (WordSimp.seqAssoc .skip InitECandidate.Proofs.WordStages.source69.2.2) .ln = true := by decide +kernel
theorem wsSd_69 : sdiOkB riscvConfig wsT2 (constFpF (WordSimp.seqAssoc .skip InitECandidate.Proofs.WordStages.source69.2.2)) = true := by decide +kernel
theorem wsCf_70 : cfOkB riscvConfig wsT1 (WordSimp.seqAssoc .skip InitECandidate.Proofs.WordStages.source70.2.2) .ln = true := by decide +kernel
theorem wsSd_70 : sdiOkB riscvConfig wsT2 (constFpF (WordSimp.seqAssoc .skip InitECandidate.Proofs.WordStages.source70.2.2)) = true := by decide +kernel
theorem wsCf_71 : cfOkB riscvConfig wsT1 (WordSimp.seqAssoc .skip InitECandidate.Proofs.WordStages.source71.2.2) .ln = true := by decide +kernel
theorem wsSd_71 : sdiOkB riscvConfig wsT2 (constFpF (WordSimp.seqAssoc .skip InitECandidate.Proofs.WordStages.source71.2.2)) = true := by decide +kernel
theorem wsCf_72 : cfOkB riscvConfig wsT1 (WordSimp.seqAssoc .skip InitECandidate.Proofs.WordStages.source72.2.2) .ln = true := by decide +kernel
theorem wsSd_72 : sdiOkB riscvConfig wsT2 (constFpF (WordSimp.seqAssoc .skip InitECandidate.Proofs.WordStages.source72.2.2)) = true := by decide +kernel
theorem wsCf_73 : cfOkB riscvConfig wsT1 (WordSimp.seqAssoc .skip InitECandidate.Proofs.WordStages.source73.2.2) .ln = true := by decide +kernel
theorem wsSd_73 : sdiOkB riscvConfig wsT2 (constFpF (WordSimp.seqAssoc .skip InitECandidate.Proofs.WordStages.source73.2.2)) = true := by decide +kernel
theorem wsCf_74 : cfOkB riscvConfig wsT1 (WordSimp.seqAssoc .skip InitECandidate.Proofs.WordStages.source74.2.2) .ln = true := by decide +kernel
theorem wsSd_74 : sdiOkB riscvConfig wsT2 (constFpF (WordSimp.seqAssoc .skip InitECandidate.Proofs.WordStages.source74.2.2)) = true := by decide +kernel
theorem wsCf_75 : cfOkB riscvConfig wsT1 (WordSimp.seqAssoc .skip InitECandidate.Proofs.WordStages.source75.2.2) .ln = true := by decide +kernel
theorem wsSd_75 : sdiOkB riscvConfig wsT2 (constFpF (WordSimp.seqAssoc .skip InitECandidate.Proofs.WordStages.source75.2.2)) = true := by decide +kernel
theorem wsCf_76 : cfOkB riscvConfig wsT1 (WordSimp.seqAssoc .skip InitECandidate.Proofs.WordStages.source76.2.2) .ln = true := by decide +kernel
theorem wsSd_76 : sdiOkB riscvConfig wsT2 (constFpF (WordSimp.seqAssoc .skip InitECandidate.Proofs.WordStages.source76.2.2)) = true := by decide +kernel
theorem wsCf_77 : cfOkB riscvConfig wsT1 (WordSimp.seqAssoc .skip InitECandidate.Proofs.WordStages.source77.2.2) .ln = true := by decide +kernel
theorem wsSd_77 : sdiOkB riscvConfig wsT2 (constFpF (WordSimp.seqAssoc .skip InitECandidate.Proofs.WordStages.source77.2.2)) = true := by decide +kernel
theorem wsCf_78 : cfOkB riscvConfig wsT1 (WordSimp.seqAssoc .skip InitECandidate.Proofs.WordStages.source78.2.2) .ln = true := by decide +kernel
theorem wsSd_78 : sdiOkB riscvConfig wsT2 (constFpF (WordSimp.seqAssoc .skip InitECandidate.Proofs.WordStages.source78.2.2)) = true := by decide +kernel
theorem wsCf_79 : cfOkB riscvConfig wsT1 (WordSimp.seqAssoc .skip InitECandidate.Proofs.WordStages.source79.2.2) .ln = true := by decide +kernel
theorem wsSd_79 : sdiOkB riscvConfig wsT2 (constFpF (WordSimp.seqAssoc .skip InitECandidate.Proofs.WordStages.source79.2.2)) = true := by decide +kernel
theorem wsCf_80 : cfOkB riscvConfig wsT1 (WordSimp.seqAssoc .skip InitECandidate.Proofs.WordStages.source80.2.2) .ln = true := by decide +kernel
theorem wsSd_80 : sdiOkB riscvConfig wsT2 (constFpF (WordSimp.seqAssoc .skip InitECandidate.Proofs.WordStages.source80.2.2)) = true := by decide +kernel
theorem wsCf_81 : cfOkB riscvConfig wsT1 (WordSimp.seqAssoc .skip InitECandidate.Proofs.WordStages.source81.2.2) .ln = true := by decide +kernel
theorem wsSd_81 : sdiOkB riscvConfig wsT2 (constFpF (WordSimp.seqAssoc .skip InitECandidate.Proofs.WordStages.source81.2.2)) = true := by decide +kernel
theorem wsCf_82 : cfOkB riscvConfig wsT1 (WordSimp.seqAssoc .skip InitECandidate.Proofs.WordStages.source82.2.2) .ln = true := by decide +kernel
theorem wsSd_82 : sdiOkB riscvConfig wsT2 (constFpF (WordSimp.seqAssoc .skip InitECandidate.Proofs.WordStages.source82.2.2)) = true := by decide +kernel
theorem wsCf_83 : cfOkB riscvConfig wsT1 (WordSimp.seqAssoc .skip InitECandidate.Proofs.WordStages.source83.2.2) .ln = true := by decide +kernel
theorem wsSd_83 : sdiOkB riscvConfig wsT2 (constFpF (WordSimp.seqAssoc .skip InitECandidate.Proofs.WordStages.source83.2.2)) = true := by decide +kernel
theorem wsCf_84 : cfOkB riscvConfig wsT1 (WordSimp.seqAssoc .skip InitECandidate.Proofs.WordStages.source84.2.2) .ln = true := by decide +kernel
theorem wsSd_84 : sdiOkB riscvConfig wsT2 (constFpF (WordSimp.seqAssoc .skip InitECandidate.Proofs.WordStages.source84.2.2)) = true := by decide +kernel
theorem wsCf_85 : cfOkB riscvConfig wsT1 (WordSimp.seqAssoc .skip InitECandidate.Proofs.WordStages.source85.2.2) .ln = true := by decide +kernel
theorem wsSd_85 : sdiOkB riscvConfig wsT2 (constFpF (WordSimp.seqAssoc .skip InitECandidate.Proofs.WordStages.source85.2.2)) = true := by decide +kernel
theorem wsCf_86 : cfOkB riscvConfig wsT1 (WordSimp.seqAssoc .skip InitECandidate.Proofs.WordStages.source86.2.2) .ln = true := by decide +kernel
theorem wsSd_86 : sdiOkB riscvConfig wsT2 (constFpF (WordSimp.seqAssoc .skip InitECandidate.Proofs.WordStages.source86.2.2)) = true := by decide +kernel
theorem wsCf_87 : cfOkB riscvConfig wsT1 (WordSimp.seqAssoc .skip InitECandidate.Proofs.WordStages.source87.2.2) .ln = true := by decide +kernel
theorem wsSd_87 : sdiOkB riscvConfig wsT2 (constFpF (WordSimp.seqAssoc .skip InitECandidate.Proofs.WordStages.source87.2.2)) = true := by decide +kernel
theorem wsCf_88 : cfOkB riscvConfig wsT1 (WordSimp.seqAssoc .skip InitECandidate.Proofs.WordStages.source88.2.2) .ln = true := by decide +kernel
theorem wsSd_88 : sdiOkB riscvConfig wsT2 (constFpF (WordSimp.seqAssoc .skip InitECandidate.Proofs.WordStages.source88.2.2)) = true := by decide +kernel

def wsChunk0 : List (Nat × Nat × WordLangProgHOL (BitVec 64)) := [InitECandidate.Proofs.WordStages.source64, InitECandidate.Proofs.WordStages.source65, InitECandidate.Proofs.WordStages.source66, InitECandidate.Proofs.WordStages.source67, InitECandidate.Proofs.WordStages.source68, InitECandidate.Proofs.WordStages.source69, InitECandidate.Proofs.WordStages.source70, InitECandidate.Proofs.WordStages.source71, InitECandidate.Proofs.WordStages.source72, InitECandidate.Proofs.WordStages.source73, InitECandidate.Proofs.WordStages.source74, InitECandidate.Proofs.WordStages.source75, InitECandidate.Proofs.WordStages.source76, InitECandidate.Proofs.WordStages.source77, InitECandidate.Proofs.WordStages.source78, InitECandidate.Proofs.WordStages.source79, InitECandidate.Proofs.WordStages.source80, InitECandidate.Proofs.WordStages.source81, InitECandidate.Proofs.WordStages.source82, InitECandidate.Proofs.WordStages.source83, InitECandidate.Proofs.WordStages.source84, InitECandidate.Proofs.WordStages.source85, InitECandidate.Proofs.WordStages.source86, InitECandidate.Proofs.WordStages.source87, InitECandidate.Proofs.WordStages.source88]

theorem wsChunk0_ok : ∀ x ∈ wsChunk0,
    cfOkB riscvConfig wsT1 (WordSimp.seqAssoc .skip x.2.2) .ln = true ∧
      sdiOkB riscvConfig wsT2 (constFpF (WordSimp.seqAssoc .skip x.2.2)) = true := by
  simp only [wsChunk0, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, imp_true_iff, and_true]
  exact ⟨⟨wsCf_64, wsSd_64⟩, ⟨wsCf_65, wsSd_65⟩, ⟨wsCf_66, wsSd_66⟩, ⟨wsCf_67, wsSd_67⟩, ⟨wsCf_68, wsSd_68⟩, ⟨wsCf_69, wsSd_69⟩, ⟨wsCf_70, wsSd_70⟩, ⟨wsCf_71, wsSd_71⟩, ⟨wsCf_72, wsSd_72⟩, ⟨wsCf_73, wsSd_73⟩, ⟨wsCf_74, wsSd_74⟩, ⟨wsCf_75, wsSd_75⟩, ⟨wsCf_76, wsSd_76⟩, ⟨wsCf_77, wsSd_77⟩, ⟨wsCf_78, wsSd_78⟩, ⟨wsCf_79, wsSd_79⟩, ⟨wsCf_80, wsSd_80⟩, ⟨wsCf_81, wsSd_81⟩, ⟨wsCf_82, wsSd_82⟩, ⟨wsCf_83, wsSd_83⟩, ⟨wsCf_84, wsSd_84⟩, ⟨wsCf_85, wsSd_85⟩, ⟨wsCf_86, wsSd_86⟩, ⟨wsCf_87, wsSd_87⟩, ⟨wsCf_88, wsSd_88⟩⟩

#print axioms wsChunk0_ok
end InitECandidate.Runtime.FineCost
