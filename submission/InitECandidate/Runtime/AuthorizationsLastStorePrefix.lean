import InitECandidate.Runtime.AuthorizationsLastStoreFrame
import InitECandidate.Runtime.RlpSliceInputPrefixBelow
import InitECandidate.Runtime.PanEvaluationMetadata
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A nonwrapping authorization record lies beyond the slice array, so its
final four-limb store and index increment retain the input-prefix invariant. -/
theorem authorization_last_store_input_prefix {F : Type} (state : PanSemStateFiniteExact 64 F)
    (record first second third fourth array count input inputLength : BitVec 64)
    (atRecord : state.locals.lookup (ofString "a") = some (.val (.word record)))
    (atValue : state.locals.lookup (ofString "s") =
      some (.rStruct [.val (.word first),.val (.word second),.val (.word third),.val (.word fourth)]))
    (valid : RlpSliceInputPrefix state array input inputLength count.toNat)
    (before : array.toNat + count.toNat * 16 ≤ record.toNat)
    (fits : record.toNat + 120 < 2^64) :
    RlpSliceInputPrefix (evaluateHOLFiniteState state authorizationLastStore).2 array input inputLength count.toNat := by
  have n88 : (record + 88#64).toNat = record.toNat + 88 := by
    rw [BitVec.toNat_add_of_lt (by change record.toNat + 88 < 2^64; omega)]
    rfl
  have n96 : (record + 88#64 + 8#64).toNat = record.toNat + 96 := by
    rw [BitVec.toNat_add_of_lt (by rw [n88]; change record.toNat + 88 + 8 < 2^64; omega),n88]
    simp [Nat.add_assoc]
  have n104 : (record + 88#64 + 16#64).toNat = record.toNat + 104 := by
    rw [BitVec.toNat_add_of_lt (by rw [n88]; change record.toNat + 88 + 16 < 2^64; omega),n88]
    simp [Nat.add_assoc]
  have n112 : (record + 88#64 + 24#64).toNat = record.toNat + 112 := by
    rw [BitVec.toNat_add_of_lt (by rw [n88]; change record.toNat + 88 + 24 < 2^64; omega),n88]
    simp [Nat.add_assoc]
  apply RlpSliceInputPrefix.after_memory_below state _ array count input inputLength record valid before
    (evaluateHOLFiniteState_metadata state authorizationLastStore).2.1
  intro watched below
  apply evaluate_authorization_last_store_frame state record first second third fourth watched atRecord atValue
  · intro same
    have equal := congrArg BitVec.toNat same
    rw [n88] at equal
    omega
  · intro same
    have equal := congrArg BitVec.toNat same
    rw [n96] at equal
    omega
  · intro same
    have equal := congrArg BitVec.toNat same
    rw [n104] at equal
    omega
  · intro same
    have equal := congrArg BitVec.toNat same
    rw [n112] at equal
    omega

#print axioms authorization_last_store_input_prefix
end InitECandidate.Runtime
