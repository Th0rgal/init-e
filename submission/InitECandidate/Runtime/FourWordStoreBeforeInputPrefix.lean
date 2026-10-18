import InitECandidate.Runtime.FourWordStoreMemoryFrame
import InitECandidate.Runtime.RlpSliceInputPrefixAbove
import InitECandidate.Runtime.PanEvaluationMetadata
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- All four record limbs below a later slice array retain its input prefix. -/
theorem fourWordStore_before_input_prefix {F : Type} (state : PanSemStateFiniteExact 64 F)
    (destination value : ExpHOL 64) (address first second third fourth array count input inputLength : BitVec 64)
    (addressEval : @evalHOLExact 64 F _ state.toExact
      (fun a => Classical.propDecidable (state.memaddrs a)) destination = some (.val (.word address)))
    (valueEval : @evalHOLExact 64 F _ state.toExact
      (fun a => Classical.propDecidable (state.memaddrs a)) value =
        some (.rStruct [.val (.word first),.val (.word second),.val (.word third),.val (.word fourth)]))
    (valid : RlpSliceInputPrefix state array input inputLength count.toNat)
    (arrayFits : array.toNat + count.toNat * 16 ≤ 2^64)
    (before : address.toNat + 24 < array.toNat) :
    RlpSliceInputPrefix (evaluateHOLFiniteState state (.store destination value)).2 array input inputLength count.toNat := by
  have fits : address.toNat + 24 < 2^64 := Nat.lt_trans before array.isLt
  have n8 : (address + 8#64).toNat = address.toNat + 8 := by
    rw [BitVec.toNat_add_of_lt (by change address.toNat + 8 < 2^64; omega)]
    rfl
  have n16 : (address + 16#64).toNat = address.toNat + 16 := by
    rw [BitVec.toNat_add_of_lt (by change address.toNat + 16 < 2^64; omega)]
    rfl
  have n24 : (address + 24#64).toNat = address.toNat + 24 := by
    rw [BitVec.toNat_add_of_lt (by change address.toNat + 24 < 2^64; omega)]
    rfl
  apply RlpSliceInputPrefix.after_memory_above state _ array count input inputLength valid arrayFits
    (evaluateHOLFiniteState_metadata state (.store destination value)).2.1
  intro watched above
  apply evaluate_fourWordStore_memory_frame state destination value address first second third fourth watched addressEval valueEval
  · intro same
    have equal := congrArg BitVec.toNat same
    omega
  · intro same
    have equal := congrArg BitVec.toNat same
    rw [n8] at equal
    omega
  · intro same
    have equal := congrArg BitVec.toNat same
    rw [n16] at equal
    omega
  · intro same
    have equal := congrArg BitVec.toNat same
    rw [n24] at equal
    omega

#print axioms fourWordStore_before_input_prefix
end InitECandidate.Runtime
