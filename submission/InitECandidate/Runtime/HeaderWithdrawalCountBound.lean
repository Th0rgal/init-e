import InitECandidate.Runtime.HeaderWithdrawalHeapChain
import InitECandidate.Runtime.TxFixedBytesArguments
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The source's signed fixed-list-count limit is `2^63 - 1`, so a count the decoder accepted under
that limit is a machine-safe positive value. This is the arithmetic content of the actual
`ssz_fixed_list_count` guard (see `payload_withdrawals_suffix_returned`), exposed for the stored
payload field. -/
theorem wd_signed_count_bound (count withdrawals balance : BitVec 64)
    (countVal : count = (balance - withdrawals) / 44)
    (within : ¬ (9223372036854775807 : BitVec 64) < count) :
    count.toNat < 2^63 := by
  have limVal : (9223372036854775807 : BitVec 64).toNat = 9223372036854775807 := by decide
  have bound := BitVec.le_def.mp (BitVec.not_lt.mp within)
  rw [limVal] at bound
  omega

/-- The withdrawal-count cell of the decoded payload struct: statement 43's load address `pl + 56`
holds the withdrawn-list count exported by the actual decoder. -/
theorem wd_slice_count_cell {F : Type} (post : PanSemStateFiniteExact 64 F)
    (array input wd count : BitVec 64)
    (entry : RlpSliceEntry post array (3#64) (input + wd) count) :
    post.memory (array + 56#64) = HolWordLab.word count ∧ post.memaddrs (array + 56#64) := by
  have h3 : (3#64 : BitVec 64) * (16#64) = 48#64 := by decide
  have h8 : (48#64 : BitVec 64) + (8#64) = 56#64 := by decide
  have cellAt : array + (3#64) * (16#64) + (8#64) = array + 56#64 := by
    rw [h3, BitVec.add_assoc, h8]
  refine ⟨?_,?_⟩
  · simpa only [cellAt] using entry.lengthCell
  · simpa only [cellAt] using entry.lengthDomain

/-- The withdrawals-array cell of the decoded payload struct: statement 43's earlier sibling read
`pl + 48` holds the array pointer `input + wd`, so the loop's `read = pl + 48` watches it. -/
theorem wd_slice_array_cell {F : Type} (post : PanSemStateFiniteExact 64 F)
    (array input wd count : BitVec 64)
    (entry : RlpSliceEntry post array (3#64) (input + wd) count) :
    post.memory (array + 48#64) = HolWordLab.word (input + wd) ∧ post.memaddrs (array + 48#64) := by
  have h3 : (3#64 : BitVec 64) * (16#64) = 48#64 := by decide
  have cellAt : array + (3#64) * (16#64) = array + 48#64 := by
    rw [h3]
  refine ⟨?_,?_⟩
  · simpa only [cellAt] using entry.pointerCell
  · simpa only [cellAt] using entry.pointerDomain

#print axioms wd_signed_count_bound
#print axioms wd_slice_count_cell
#print axioms wd_slice_array_cell
end InitECandidate.Runtime
