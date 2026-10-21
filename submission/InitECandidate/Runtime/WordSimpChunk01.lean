import InitECandidate.Runtime.WordSimpTab
import InitECandidate.Proofs.CompilerStages
import InitECandidate.Proofs.WordStages.Source89
import InitECandidate.Proofs.WordStages.Source90
import InitECandidate.Proofs.WordStages.Source91
import InitECandidate.Proofs.WordStages.Source92
import InitECandidate.Proofs.WordStages.Source93
import InitECandidate.Proofs.WordStages.Source94
import InitECandidate.Proofs.WordStages.Source95
import InitECandidate.Proofs.WordStages.Source96
import InitECandidate.Proofs.WordStages.Source97
import InitECandidate.Proofs.WordStages.Source98
import InitECandidate.Proofs.WordStages.Source99
import InitECandidate.Proofs.WordStages.Source100
import InitECandidate.Proofs.WordStages.Source101
import InitECandidate.Proofs.WordStages.Source102
import InitECandidate.Proofs.WordStages.Source103
import InitECandidate.Proofs.WordStages.Source104
import InitECandidate.Proofs.WordStages.Source105
import InitECandidate.Proofs.WordStages.Source106
import InitECandidate.Proofs.WordStages.Source107
import InitECandidate.Proofs.WordStages.Source108
import InitECandidate.Proofs.WordStages.Source109
import InitECandidate.Proofs.WordStages.Source110
import InitECandidate.Proofs.WordStages.Source111
import InitECandidate.Proofs.WordStages.Source112
import InitECandidate.Proofs.WordStages.Source113
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target

theorem wsCf_89 : cfOkB riscvConfig wsT1 (WordSimp.seqAssoc .skip InitECandidate.Proofs.WordStages.source89.2.2) .ln = true := by decide +kernel
theorem wsSd_89 : sdiOkB riscvConfig wsT2 (constFpF (WordSimp.seqAssoc .skip InitECandidate.Proofs.WordStages.source89.2.2)) = true := by decide +kernel
theorem wsCf_90 : cfOkB riscvConfig wsT1 (WordSimp.seqAssoc .skip InitECandidate.Proofs.WordStages.source90.2.2) .ln = true := by decide +kernel
theorem wsSd_90 : sdiOkB riscvConfig wsT2 (constFpF (WordSimp.seqAssoc .skip InitECandidate.Proofs.WordStages.source90.2.2)) = true := by decide +kernel
theorem wsCf_91 : cfOkB riscvConfig wsT1 (WordSimp.seqAssoc .skip InitECandidate.Proofs.WordStages.source91.2.2) .ln = true := by decide +kernel
theorem wsSd_91 : sdiOkB riscvConfig wsT2 (constFpF (WordSimp.seqAssoc .skip InitECandidate.Proofs.WordStages.source91.2.2)) = true := by decide +kernel
theorem wsCf_92 : cfOkB riscvConfig wsT1 (WordSimp.seqAssoc .skip InitECandidate.Proofs.WordStages.source92.2.2) .ln = true := by decide +kernel
theorem wsSd_92 : sdiOkB riscvConfig wsT2 (constFpF (WordSimp.seqAssoc .skip InitECandidate.Proofs.WordStages.source92.2.2)) = true := by decide +kernel
theorem wsCf_93 : cfOkB riscvConfig wsT1 (WordSimp.seqAssoc .skip InitECandidate.Proofs.WordStages.source93.2.2) .ln = true := by decide +kernel
theorem wsSd_93 : sdiOkB riscvConfig wsT2 (constFpF (WordSimp.seqAssoc .skip InitECandidate.Proofs.WordStages.source93.2.2)) = true := by decide +kernel
theorem wsCf_94 : cfOkB riscvConfig wsT1 (WordSimp.seqAssoc .skip InitECandidate.Proofs.WordStages.source94.2.2) .ln = true := by decide +kernel
theorem wsSd_94 : sdiOkB riscvConfig wsT2 (constFpF (WordSimp.seqAssoc .skip InitECandidate.Proofs.WordStages.source94.2.2)) = true := by decide +kernel
theorem wsCf_95 : cfOkB riscvConfig wsT1 (WordSimp.seqAssoc .skip InitECandidate.Proofs.WordStages.source95.2.2) .ln = true := by decide +kernel
theorem wsSd_95 : sdiOkB riscvConfig wsT2 (constFpF (WordSimp.seqAssoc .skip InitECandidate.Proofs.WordStages.source95.2.2)) = true := by decide +kernel
theorem wsCf_96 : cfOkB riscvConfig wsT1 (WordSimp.seqAssoc .skip InitECandidate.Proofs.WordStages.source96.2.2) .ln = true := by decide +kernel
theorem wsSd_96 : sdiOkB riscvConfig wsT2 (constFpF (WordSimp.seqAssoc .skip InitECandidate.Proofs.WordStages.source96.2.2)) = true := by decide +kernel
theorem wsCf_97 : cfOkB riscvConfig wsT1 (WordSimp.seqAssoc .skip InitECandidate.Proofs.WordStages.source97.2.2) .ln = true := by decide +kernel
theorem wsSd_97 : sdiOkB riscvConfig wsT2 (constFpF (WordSimp.seqAssoc .skip InitECandidate.Proofs.WordStages.source97.2.2)) = true := by decide +kernel
theorem wsCf_98 : cfOkB riscvConfig wsT1 (WordSimp.seqAssoc .skip InitECandidate.Proofs.WordStages.source98.2.2) .ln = true := by decide +kernel
theorem wsSd_98 : sdiOkB riscvConfig wsT2 (constFpF (WordSimp.seqAssoc .skip InitECandidate.Proofs.WordStages.source98.2.2)) = true := by decide +kernel
theorem wsCf_99 : cfOkB riscvConfig wsT1 (WordSimp.seqAssoc .skip InitECandidate.Proofs.WordStages.source99.2.2) .ln = true := by decide +kernel
theorem wsSd_99 : sdiOkB riscvConfig wsT2 (constFpF (WordSimp.seqAssoc .skip InitECandidate.Proofs.WordStages.source99.2.2)) = true := by decide +kernel
theorem wsCf_100 : cfOkB riscvConfig wsT1 (WordSimp.seqAssoc .skip InitECandidate.Proofs.WordStages.source100.2.2) .ln = true := by decide +kernel
theorem wsSd_100 : sdiOkB riscvConfig wsT2 (constFpF (WordSimp.seqAssoc .skip InitECandidate.Proofs.WordStages.source100.2.2)) = true := by decide +kernel
theorem wsCf_101 : cfOkB riscvConfig wsT1 (WordSimp.seqAssoc .skip InitECandidate.Proofs.WordStages.source101.2.2) .ln = true := by decide +kernel
theorem wsSd_101 : sdiOkB riscvConfig wsT2 (constFpF (WordSimp.seqAssoc .skip InitECandidate.Proofs.WordStages.source101.2.2)) = true := by decide +kernel
theorem wsCf_102 : cfOkB riscvConfig wsT1 (WordSimp.seqAssoc .skip InitECandidate.Proofs.WordStages.source102.2.2) .ln = true := by decide +kernel
theorem wsSd_102 : sdiOkB riscvConfig wsT2 (constFpF (WordSimp.seqAssoc .skip InitECandidate.Proofs.WordStages.source102.2.2)) = true := by decide +kernel
theorem wsCf_103 : cfOkB riscvConfig wsT1 (WordSimp.seqAssoc .skip InitECandidate.Proofs.WordStages.source103.2.2) .ln = true := by decide +kernel
theorem wsSd_103 : sdiOkB riscvConfig wsT2 (constFpF (WordSimp.seqAssoc .skip InitECandidate.Proofs.WordStages.source103.2.2)) = true := by decide +kernel
theorem wsCf_104 : cfOkB riscvConfig wsT1 (WordSimp.seqAssoc .skip InitECandidate.Proofs.WordStages.source104.2.2) .ln = true := by decide +kernel
theorem wsSd_104 : sdiOkB riscvConfig wsT2 (constFpF (WordSimp.seqAssoc .skip InitECandidate.Proofs.WordStages.source104.2.2)) = true := by decide +kernel
theorem wsCf_105 : cfOkB riscvConfig wsT1 (WordSimp.seqAssoc .skip InitECandidate.Proofs.WordStages.source105.2.2) .ln = true := by decide +kernel
theorem wsSd_105 : sdiOkB riscvConfig wsT2 (constFpF (WordSimp.seqAssoc .skip InitECandidate.Proofs.WordStages.source105.2.2)) = true := by decide +kernel
theorem wsCf_106 : cfOkB riscvConfig wsT1 (WordSimp.seqAssoc .skip InitECandidate.Proofs.WordStages.source106.2.2) .ln = true := by decide +kernel
theorem wsSd_106 : sdiOkB riscvConfig wsT2 (constFpF (WordSimp.seqAssoc .skip InitECandidate.Proofs.WordStages.source106.2.2)) = true := by decide +kernel
theorem wsCf_107 : cfOkB riscvConfig wsT1 (WordSimp.seqAssoc .skip InitECandidate.Proofs.WordStages.source107.2.2) .ln = true := by decide +kernel
theorem wsSd_107 : sdiOkB riscvConfig wsT2 (constFpF (WordSimp.seqAssoc .skip InitECandidate.Proofs.WordStages.source107.2.2)) = true := by decide +kernel
theorem wsCf_108 : cfOkB riscvConfig wsT1 (WordSimp.seqAssoc .skip InitECandidate.Proofs.WordStages.source108.2.2) .ln = true := by decide +kernel
theorem wsSd_108 : sdiOkB riscvConfig wsT2 (constFpF (WordSimp.seqAssoc .skip InitECandidate.Proofs.WordStages.source108.2.2)) = true := by decide +kernel
theorem wsCf_109 : cfOkB riscvConfig wsT1 (WordSimp.seqAssoc .skip InitECandidate.Proofs.WordStages.source109.2.2) .ln = true := by decide +kernel
theorem wsSd_109 : sdiOkB riscvConfig wsT2 (constFpF (WordSimp.seqAssoc .skip InitECandidate.Proofs.WordStages.source109.2.2)) = true := by decide +kernel
theorem wsCf_110 : cfOkB riscvConfig wsT1 (WordSimp.seqAssoc .skip InitECandidate.Proofs.WordStages.source110.2.2) .ln = true := by decide +kernel
theorem wsSd_110 : sdiOkB riscvConfig wsT2 (constFpF (WordSimp.seqAssoc .skip InitECandidate.Proofs.WordStages.source110.2.2)) = true := by decide +kernel
theorem wsCf_111 : cfOkB riscvConfig wsT1 (WordSimp.seqAssoc .skip InitECandidate.Proofs.WordStages.source111.2.2) .ln = true := by decide +kernel
theorem wsSd_111 : sdiOkB riscvConfig wsT2 (constFpF (WordSimp.seqAssoc .skip InitECandidate.Proofs.WordStages.source111.2.2)) = true := by decide +kernel
theorem wsCf_112 : cfOkB riscvConfig wsT1 (WordSimp.seqAssoc .skip InitECandidate.Proofs.WordStages.source112.2.2) .ln = true := by decide +kernel
theorem wsSd_112 : sdiOkB riscvConfig wsT2 (constFpF (WordSimp.seqAssoc .skip InitECandidate.Proofs.WordStages.source112.2.2)) = true := by decide +kernel
theorem wsCf_113 : cfOkB riscvConfig wsT1 (WordSimp.seqAssoc .skip InitECandidate.Proofs.WordStages.source113.2.2) .ln = true := by decide +kernel
theorem wsSd_113 : sdiOkB riscvConfig wsT2 (constFpF (WordSimp.seqAssoc .skip InitECandidate.Proofs.WordStages.source113.2.2)) = true := by decide +kernel

def wsChunk1 : List (Nat × Nat × WordLangProgHOL (BitVec 64)) := [InitECandidate.Proofs.WordStages.source89, InitECandidate.Proofs.WordStages.source90, InitECandidate.Proofs.WordStages.source91, InitECandidate.Proofs.WordStages.source92, InitECandidate.Proofs.WordStages.source93, InitECandidate.Proofs.WordStages.source94, InitECandidate.Proofs.WordStages.source95, InitECandidate.Proofs.WordStages.source96, InitECandidate.Proofs.WordStages.source97, InitECandidate.Proofs.WordStages.source98, InitECandidate.Proofs.WordStages.source99, InitECandidate.Proofs.WordStages.source100, InitECandidate.Proofs.WordStages.source101, InitECandidate.Proofs.WordStages.source102, InitECandidate.Proofs.WordStages.source103, InitECandidate.Proofs.WordStages.source104, InitECandidate.Proofs.WordStages.source105, InitECandidate.Proofs.WordStages.source106, InitECandidate.Proofs.WordStages.source107, InitECandidate.Proofs.WordStages.source108, InitECandidate.Proofs.WordStages.source109, InitECandidate.Proofs.WordStages.source110, InitECandidate.Proofs.WordStages.source111, InitECandidate.Proofs.WordStages.source112, InitECandidate.Proofs.WordStages.source113]

theorem wsChunk1_ok : ∀ x ∈ wsChunk1,
    cfOkB riscvConfig wsT1 (WordSimp.seqAssoc .skip x.2.2) .ln = true ∧
      sdiOkB riscvConfig wsT2 (constFpF (WordSimp.seqAssoc .skip x.2.2)) = true := by
  simp only [wsChunk1, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, imp_true_iff, and_true]
  exact ⟨⟨wsCf_89, wsSd_89⟩, ⟨wsCf_90, wsSd_90⟩, ⟨wsCf_91, wsSd_91⟩, ⟨wsCf_92, wsSd_92⟩, ⟨wsCf_93, wsSd_93⟩, ⟨wsCf_94, wsSd_94⟩, ⟨wsCf_95, wsSd_95⟩, ⟨wsCf_96, wsSd_96⟩, ⟨wsCf_97, wsSd_97⟩, ⟨wsCf_98, wsSd_98⟩, ⟨wsCf_99, wsSd_99⟩, ⟨wsCf_100, wsSd_100⟩, ⟨wsCf_101, wsSd_101⟩, ⟨wsCf_102, wsSd_102⟩, ⟨wsCf_103, wsSd_103⟩, ⟨wsCf_104, wsSd_104⟩, ⟨wsCf_105, wsSd_105⟩, ⟨wsCf_106, wsSd_106⟩, ⟨wsCf_107, wsSd_107⟩, ⟨wsCf_108, wsSd_108⟩, ⟨wsCf_109, wsSd_109⟩, ⟨wsCf_110, wsSd_110⟩, ⟨wsCf_111, wsSd_111⟩, ⟨wsCf_112, wsSd_112⟩, ⟨wsCf_113, wsSd_113⟩⟩

#print axioms wsChunk1_ok
end InitECandidate.Runtime.FineCost
