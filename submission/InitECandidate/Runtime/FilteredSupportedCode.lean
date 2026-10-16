import InitECandidate.Runtime.ActualSupportedCode
import Flapjack.Compiler.Backend.LabFilter.Map
namespace InitECandidate.Runtime.LabToTarget
open Flapjack.Compiler.Backend.LabFilter
open Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem

/-- Removing skip instructions preserves the checked syntax of every remaining line. -/
theorem checkedSections_filterSkip (code : LabProgHOL 64)
    (checked : checkedSections code = true) : checkedSections (filterSkip code) = true := by
  rw [filterSkipMap]
  simp only [checkedSections, List.all_eq_true] at checked ⊢
  intro sec member
  obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
  intro line lineMember
  exact checked original originalMember line
    (List.mem_filter.mp lineMember).1

/-- The exact code consumed by the native initializer has a checked support certificate. -/
theorem actual_filtered_supported :
    SupportedCode (filterSkip InitECandidate.Proofs.BackendStages.Sections.program) :=
  checkedSections_supported _ (checkedSections_filterSkip _ actual_checked)

#print axioms checkedSections_filterSkip
#print axioms actual_filtered_supported
end InitECandidate.Runtime.LabToTarget
