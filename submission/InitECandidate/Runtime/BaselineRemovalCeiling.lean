import InitECandidate.Runtime.SelectedStackFields
import InitECandidate.Runtime.StackRemoveScale
import InitECandidate.Runtime.BaselineRuntimeEntry
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace InitECandidate.Runtime
open InitE InitECandidate.Proofs Flapjack Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInitSemantics

/-- Fixed code-size ceiling at the actual allocated Stack removal entry. -/
noncomputable def baselineRemovalLimit : Nat := max
  (sizeOf (.call none (.inl BvlToBvi.initGlobalsLocation) none : HolProg 64))
  (StackToLab.codeSizeLimit (code1 baselineCompilerConfig.dataConf BackendStages.Native.stack))

def baselineBitmapScale : Nat := 1 + (2 ^ 64 + 1) * InitECandidate.bitmaps.length

theorem baseline_selected_fields {input : Guest.InputBlob} (entry : BaselineRuntimeEntry input) :
    entry.source.code = sptFromAList (code1 baselineCompilerConfig.dataConf BackendStages.Native.stack) ∧
    entry.source.bitmaps = InitECandidate.bitmaps ∧
    entry.source.compileOracle = coracle1 (entryStackOracle entry.cfg) := by
  exact StackRemove.selected_fields _ _ _ _ _ _ _ _ _ _ _ entry.selection

theorem baseline_source_code_bounded {input : Guest.InputBlob}
    (entry : BaselineRuntimeEntry input) (fuel : Nat) :
    StackToLab.CodeSizeState baselineRemovalLimit {entry.source with clock := fuel} := by
  apply StackToLab.CodeSizeState.of_lists baselineRemovalLimit {entry.source with clock := fuel}
    (code1 baselineCompilerConfig.dataConf BackendStages.Native.stack)
    (baseline_selected_fields entry).1 (Nat.le_max_right _ _)
  intro n
  change StackToLab.codeSizeLimit (entry.source.compileOracle n).2.1 ≤ _
  rw [(baseline_selected_fields entry).2.2]
  change 0 ≤ baselineRemovalLimit
  exact Nat.zero_le _

theorem baseline_source_bitmap_bounded {input : Guest.InputBlob}
    (entry : BaselineRuntimeEntry input) (fuel : Nat) :
    StackRemove.BitmapBudget baselineBitmapScale {entry.source with clock := fuel} := by
  constructor
  · constructor
    intro n
    change (entry.source.compileOracle n).2.2 = []
    rw [(baseline_selected_fields entry).2.2]
    rfl
  · change 2 + (2 ^ 64 + 1) * entry.source.bitmaps.length ≤ 2 * baselineBitmapScale
    rw [(baseline_selected_fields entry).2.1]
    unfold baselineBitmapScale
    omega

/-- Actual baseline removal overhead is bounded by fixed program constants and
initial fuel, with all code and bitmap premises discharged internally. -/
theorem baseline_removeWork_ceiling {input : Guest.InputBlob}
    (entry : BaselineRuntimeEntry input) (fuel : Nat) :
    StackRemove.removeWork (.call none (.inl BvlToBvi.initGlobalsLocation) none)
      {entry.source with clock := fuel} ≤
      baselineBitmapScale * workCeiling baselineRemovalLimit fuel
        (sizeOf (.call none (.inl BvlToBvi.initGlobalsLocation) none : HolProg 64)) := by
  exact StackRemove.removeWork_ceiling baselineRemovalLimit baselineBitmapScale _ _
    (Nat.le_max_left _ _) (baseline_source_code_bounded entry fuel)
    (baseline_source_bitmap_bounded entry fuel)

#print axioms baseline_selected_fields
#print axioms baseline_source_code_bounded
#print axioms baseline_source_bitmap_bounded
#print axioms baseline_removeWork_ceiling
end InitECandidate.Runtime
