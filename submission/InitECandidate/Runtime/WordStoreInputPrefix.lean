import InitECandidate.Runtime.WordStoreMemoryFrame
import InitECandidate.Runtime.RlpSliceInputPrefixBelow
import InitECandidate.Runtime.PanEvaluationMetadata
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- A word store beyond a slice array preserves its input-prefix invariant. -/
theorem wordStore_input_prefix {F : Type} (state : PanSemStateFiniteExact 64 F)
    (destination value : ExpHOL 64) (address word array count input inputLength : BitVec 64)
    (addressEval : @evalHOLExact 64 F _ state.toExact
      (fun a => Classical.propDecidable (state.memaddrs a)) destination = some (.val (.word address)))
    (valueEval : @evalHOLExact 64 F _ state.toExact
      (fun a => Classical.propDecidable (state.memaddrs a)) value = some (.val (.word word)))
    (valid : RlpSliceInputPrefix state array input inputLength count.toNat)
    (before : array.toNat + count.toNat * 16 ≤ address.toNat) :
    RlpSliceInputPrefix (evaluateHOLFiniteState state (.store destination value)).2 array input inputLength count.toNat := by
  apply RlpSliceInputPrefix.after_memory_below state _ array count input inputLength address valid before
    (evaluateHOLFiniteState_metadata state (.store destination value)).2.1
  intro watched below
  apply evaluate_wordStore_memory_frame state destination value address watched addressEval
  · intro parsed evaluated
    rw [valueEval] at evaluated
    exact ⟨word,(Option.some.inj evaluated).symm⟩
  · intro same
    have equal := congrArg BitVec.toNat same
    omega

#print axioms wordStore_input_prefix
end InitECandidate.Runtime
