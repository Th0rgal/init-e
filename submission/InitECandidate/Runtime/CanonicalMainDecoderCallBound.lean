import InitECandidate.Runtime.MainDecoderEntryCallBound
namespace InitECandidate.Runtime
open InitE Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- The uniform handled-decoder bound applies to every normal decoder-entry
state reached from the authoritative challenge entry. -/
theorem canonical_main_decoder_call_bounded (input : Guest.InputBlob) (fuel : Nat)
    (ready : PanSemStateFiniteExact 64 Guest.HostMemory)
    (valid : MainDecoderEntry {canonicalOriginalSourceEntry input with clock := fuel} ready)
    (budget : canonicalStatelessCallCost ≤ ready.clock) :
    let evaluated := evaluateHOLFiniteState ready mainStatelessCall
    ready.clock ≤ evaluated.2.clock + canonicalStatelessCallCost ∧
      evaluated.2.clock ≤ ready.clock ∧ evaluated.1 ≠ some .timeOut := by
  apply main_decoder_entry_stateless_call_bounded
    {canonicalOriginalSourceEntry input with clock := fuel} ready
  · exact canonical_original_source_code input
  · exact canonical_original_aligned_arena input
  · exact valid
  · exact budget

#print axioms canonical_main_decoder_call_bounded
end InitECandidate.Runtime
