import InitECandidate.Runtime.ExpandedMainDecoderCallBound
import InitECandidate.Runtime.ReachesRunBounded
namespace InitECandidate.Runtime
open InitE Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

def expandedMainDecoderPrefixCost : Nat := ((1893+(inputBlobBodyCost+1))+4)+33

/-- The checked main prefix and decoder leave only the actual normal decoder
continuation at mainAt 21 to bound. Terminal decoder outcomes are covered. -/
theorem expanded_main_runBounded_of_decoder_tail (input : Guest.InputBlob) (fuel tailCost : Nat)
    (budget : expandedMainDecoderPrefixCost+canonicalStatelessCallCost+tailCost≤fuel)
    (tailBound : ∀ ready decoded,
      MainDecoderEntry {expandedRuntimeEntry input with clock:=fuel} ready→
      evaluateHOLFiniteState ready mainStatelessCall=(none,decoded)→
      tailCost≤decoded.clock→RunBounded decoded (mainAt 21) tailCost) :
    RunBounded {expandedRuntimeEntry input with clock:=fuel} (mainAt 0)
      (expandedMainDecoderPrefixCost+canonicalStatelessCallCost+tailCost) := by
  have reached := expanded_main_decoder_entry input fuel (by change expandedMainDecoderPrefixCost≤fuel; omega)
  have closed := runBounded_of_reaches {expandedRuntimeEntry input with clock:=fuel}
    (mainAt 0) (mainAt 20) (MainDecoderEntry {expandedRuntimeEntry input with clock:=fuel})
    expandedMainDecoderPrefixCost (canonicalStatelessCallCost+tailCost) reached
    (by change expandedMainDecoderPrefixCost+(canonicalStatelessCallCost+tailCost)≤fuel; omega) ?_
  · simpa only [Nat.add_assoc] using closed
  · intro ready valid remaining
    rw [source_main_stateless_call_head]
    apply RunBounded.seq
      (expanded_main_decoder_call_bounded input fuel ready valid (by omega)) remaining
    intro decoded run code enough
    exact tailBound ready decoded valid run enough

#print axioms expanded_main_runBounded_of_decoder_tail
end InitECandidate.Runtime
