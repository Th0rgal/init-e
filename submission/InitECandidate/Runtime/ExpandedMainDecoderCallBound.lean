import InitECandidate.Runtime.MainDecoderEntryCallBound
import InitECandidate.Runtime.ExpandedMainDecoderEntry
namespace InitECandidate.Runtime
open InitE Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- The uniform handled-decoder bound applies to every normal decoder-entry
state reached from the enlarged-domain proof entry. -/
theorem expanded_main_decoder_call_bounded (input : Guest.InputBlob) (fuel : Nat)
    (ready : PanSemStateFiniteExact 64 Guest.HostMemory)
    (valid : MainDecoderEntry {expandedRuntimeEntry input with clock := fuel} ready)
    (budget : canonicalStatelessCallCost ≤ ready.clock) :
    let evaluated := evaluateHOLFiniteState ready mainStatelessCall
    ready.clock ≤ evaluated.2.clock + canonicalStatelessCallCost ∧
      evaluated.2.clock ≤ ready.clock ∧ evaluated.1 ≠ some .timeOut := by
  apply main_decoder_entry_stateless_call_bounded
    {expandedRuntimeEntry input with clock := fuel} ready
  · exact canonical_original_source_code input
  · intro address aligned lower upper;trivial
  · exact valid
  · exact budget

#print axioms expanded_main_decoder_call_bounded
end InitECandidate.Runtime
