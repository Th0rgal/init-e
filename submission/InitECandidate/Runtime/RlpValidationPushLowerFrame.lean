import InitECandidate.Runtime.RlpValidationPushExecution
import InitECandidate.Runtime.ScratchAllocationFields
import InitECandidate.Runtime.TransactionMemzeroLowerFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- Writing an actual validator continuation record preserves all words below
its base, the region containing the guest input and transaction-slice arrays. -/
theorem rlpValidation_push_memory_below {F : Type} (state : PanSemStateFiniteExact 64 F)
    (record after stop top payload watched : BitVec 64)
    (fits : record.toNat + 24 ≤ 2^64) (below : watched.toNat < record.toNat) :
    (rlpValidationPushPost state record after stop top payload).memory watched = state.memory watched := by
  have nat8 : (record + 8#64).toNat = record.toNat + 8 := by
    rw [BitVec.toNat_add_of_lt (by change record.toNat + 8 < 2^64; omega)]
    rfl
  have nat16 : (record + 16#64).toNat = record.toNat + 16 := by
    rw [BitVec.toNat_add_of_lt (by change record.toNat + 16 < 2^64; omega)]
    rfl
  have separate0 : watched ≠ record := by intro same; subst watched; omega
  have separate8 : watched ≠ record + 8#64 := by
    intro same
    have equal := congrArg BitVec.toNat same
    rw [nat8] at equal
    omega
  have separate16 : watched ≠ record + 16#64 := by
    intro same
    have equal := congrArg BitVec.toNat same
    rw [nat16] at equal
    omega
  simp [rlpValidationPushPost,setVarHOLFinite,sourceWriteWord,separate0,separate8,separate16]

/-- A validator push retains all earlier input-bounded transaction slices. -/
theorem rlpValidation_push_input_prefix {F : Type} (state : PanSemStateFiniteExact 64 F)
    (record after stop top payload array count input inputLength : BitVec 64)
    (fits : record.toNat + 24 ≤ 2^64)
    (before : array.toNat + count.toNat * 16 ≤ record.toNat)
    (valid : RlpSliceInputPrefix state array input inputLength count.toNat) :
    RlpSliceInputPrefix (rlpValidationPushPost state record after stop top payload) array input inputLength count.toNat := by
  exact rlp_slice_input_prefix_after_lower_frame state _ array count input inputLength record valid before rfl
    (fun watched below => rlpValidation_push_memory_below state record after stop top payload watched fits below)

/-- A successful descending scratch allocation stays above the frame boundary;
therefore its validator push preserves all lower guest data. -/
theorem rlpValidation_scratch_push_memory_below_frame {F : Type} (state : PanSemStateFiniteExact 64 F)
    (scratch frame after stop top payload watched : BitVec 64)
    (fits : 24 ≤ scratch.toNat)
    (allocated : frame.toNat ≤ (scratchAllocationEnd scratch 24).toNat)
    (below : watched.toNat < frame.toNat) :
    (rlpValidationPushPost state (scratchAllocationEnd scratch 24) after stop top payload).memory watched = state.memory watched := by
  apply rlpValidation_push_memory_below
  · have within := scratchAllocationEnd_before scratch 24 fits
    change (scratchAllocationEnd scratch 24).toNat + 24 ≤ scratch.toNat at within
    have limit := scratch.isLt
    change (scratchAllocationEnd scratch 24).toNat + 24 ≤ 2^64
    omega
  · omega

#print axioms rlpValidation_scratch_push_memory_below_frame
#print axioms rlpValidation_push_memory_below
#print axioms rlpValidation_push_input_prefix
end InitECandidate.Runtime
