import InitECandidate.Runtime.ActualWordNoInstall
import InitECandidate.Runtime.WordWorkCeiling
import InitECandidate.Runtime.BaselineRuntimeEntry
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace InitECandidate.Runtime
open InitE InitECandidate.Proofs Flapjack Flapjack.Compiler.Backend

/-- A fixed size ceiling for the actual optimized Word code and its entry call. -/
noncomputable def baselineWordLimit : Nat := max
  (sizeOf (.call none (some BvlToBvi.initGlobalsLocation) [0] none : WordLangProgHOL (BitVec 64)))
  (WordToStack.wordCodeSizeLimit BackendStages.Native.programs0)

theorem entryWordState_bounded {input : Guest.InputBlob}
    (entry : BaselineRuntimeEntry input) (fuel : Nat) :
    WordToStack.WordCodeSize baselineWordLimit
      {entryWordState entry.cfg entry.source with clock := fuel} := by
  exact WordToStack.WordCodeSize.of_lists baselineWordLimit
    {entryWordState entry.cfg entry.source with clock := fuel}
    BackendStages.Native.programs0 rfl (Nat.le_max_right _ _) WordToStack.baseline_word_noInstall

/-- Uniform Word work ceiling at the concrete baseline entry. All static
code-size and no-install obligations are discharged internally. -/
theorem baseline_wordWork_ceiling {input : Guest.InputBlob}
    (entry : BaselineRuntimeEntry input) (fuel : Nat) :
    WordToStack.wordWork (.call none (some BvlToBvi.initGlobalsLocation) [0] none)
      {entryWordState entry.cfg entry.source with clock := fuel} ≤
      workCeiling baselineWordLimit fuel
        (sizeOf (.call none (some BvlToBvi.initGlobalsLocation) [0] none : WordLangProgHOL (BitVec 64))) := by
  exact WordToStack.wordWork_ceiling baselineWordLimit _ _ (Nat.le_max_left _ _)
    (entryWordState_bounded entry fuel) rfl

#print axioms entryWordState_bounded
#print axioms baseline_wordWork_ceiling
end InitECandidate.Runtime
