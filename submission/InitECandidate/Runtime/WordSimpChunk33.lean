import InitECandidate.Runtime.WordSimpTab
import InitECandidate.Proofs.CompilerStages
import InitECandidate.Proofs.WordStages.Source889
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target

theorem wsCf_889 : cfOkB riscvConfig wsT1 (WordSimp.seqAssoc .skip InitECandidate.Proofs.WordStages.source889.2.2) .ln = true := by decide +kernel
theorem wsSd_889 : sdiOkB riscvConfig wsT2 (constFpF (WordSimp.seqAssoc .skip InitECandidate.Proofs.WordStages.source889.2.2)) = true := by decide +kernel

def wsChunk33 : List (Nat × Nat × WordLangProgHOL (BitVec 64)) := [InitECandidate.Proofs.WordStages.source889]

theorem wsChunk33_ok : ∀ x ∈ wsChunk33,
    cfOkB riscvConfig wsT1 (WordSimp.seqAssoc .skip x.2.2) .ln = true ∧
      sdiOkB riscvConfig wsT2 (constFpF (WordSimp.seqAssoc .skip x.2.2)) = true := by
  simp only [wsChunk33, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, imp_true_iff, and_true]
  exact ⟨wsCf_889, wsSd_889⟩

#print axioms wsChunk33_ok
end InitECandidate.Runtime.FineCost
