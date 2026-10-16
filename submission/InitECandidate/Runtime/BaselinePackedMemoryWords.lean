import InitECandidate.Proofs.PanInstallationCore
import Flapjack.Pancake.Proofs.PanToWord
namespace InitECandidate.Runtime
open InitE Flapjack

/-- The concrete abstract memory used by the installation constructor contains
words at every address, including cells outside the source ordinary domain. -/
theorem baseline_packed_memory_words (address : BitVec 64) :
    ∃ word, packedWordMemory installedMemory address = WordLocW.word word := by
  exact ⟨_,rfl⟩

theorem baseline_packed_memory_noLabels (domain : BitVec 64 → Prop) :
    noLabelsHOL (packedWordMemory installedMemory) domain := by
  intro address _
  exact baseline_packed_memory_words address

#print axioms baseline_packed_memory_words
#print axioms baseline_packed_memory_noLabels
end InitECandidate.Runtime
