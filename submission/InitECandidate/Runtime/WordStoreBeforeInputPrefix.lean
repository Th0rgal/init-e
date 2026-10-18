import InitECandidate.Runtime.WordStoreMemoryFrame
import InitECandidate.Runtime.RlpSliceInputPrefixAbove
import InitECandidate.Runtime.PanEvaluationMetadata
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- A record word below a later allocated slice array retains its input prefix. -/
theorem wordStore_before_input_prefix {F : Type} (state : PanSemStateFiniteExact 64 F)
    (destination value : ExpHOL 64) (address word array count input inputLength : BitVec 64)
    (addressEval : @evalHOLExact 64 F _ state.toExact
      (fun a => Classical.propDecidable (state.memaddrs a)) destination = some (.val (.word address)))
    (valueEval : @evalHOLExact 64 F _ state.toExact
      (fun a => Classical.propDecidable (state.memaddrs a)) value = some (.val (.word word)))
    (valid : RlpSliceInputPrefix state array input inputLength count.toNat)
    (fits : array.toNat + count.toNat * 16 ≤ 2^64) (before : address.toNat < array.toNat) :
    RlpSliceInputPrefix (evaluateHOLFiniteState state (.store destination value)).2 array input inputLength count.toNat := by
  apply RlpSliceInputPrefix.after_memory_above state _ array count input inputLength valid fits
    (evaluateHOLFiniteState_metadata state (.store destination value)).2.1
  intro watched above
  apply evaluate_wordStore_memory_frame state destination value address watched addressEval
  · intro parsed evaluated
    rw [valueEval] at evaluated
    exact ⟨word,(Option.some.inj evaluated).symm⟩
  · intro same
    have equal := congrArg BitVec.toNat same
    omega

#print axioms wordStore_before_input_prefix
end InitECandidate.Runtime
