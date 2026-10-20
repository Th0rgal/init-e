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

/-- Statement 46's window with every decoder-side input discharged: the withdrawal count bound comes
from the source's signed count limit, and both watched cells (`pl + 48` array pointer, `pl + 56` count)
come from the payload struct's actual slice entry. Only the heap geometry and the state bindings remain
as inputs. -/
theorem payloadHeader46_window_from_decoder {F : Type} (t : PanSemStateFiniteExact 64 F)
    (nwd pl slices heapBase w input wd size : BitVec 64) (withdrawals balance : BitVec 64)
    (entry : RlpSliceEntry t pl (3#64) (input + wd) nwd)
    (countVal : nwd = (balance - withdrawals) / 44)
    (within : ¬ (9223372036854775807 : BitVec 64) < nwd)
    (endEq : heapBase.toNat = slices.toNat + size.toNat)
    (sizeEq : size.toNat = 16 * nwd.toNat + 16)
    (alSlices : slices.toNat % 8 = 0) (alSize : size.toNat % 8 = 0)
    (cap : slices.toNat + 80 * nwd.toNat + 80 ≤ 33806089496)
    (atCounter : t.locals.lookup (ofString "i") = some (ValueHOL.val (HolWordLab.word 0#64)))
    (atNwd : t.locals.lookup (ofString "nwd") = some (ValueHOL.val (HolWordLab.word nwd)))
    (atPl : t.locals.lookup (ofString "pl") = some (ValueHOL.val (HolWordLab.word pl)))
    (freshE : t.locals.lookup (ofString "e") = none)
    (atSlices : t.globals.lookup (ofString "wd_rlp_slices") =
      some (ValueHOL.val (HolWordLab.word slices)))
    (atHeap : t.globals.lookup (ofString "heap_ptr") = some (ValueHOL.val (HolWordLab.word heapBase)))
    (code : t.code = originalRuntimeCode)
    (slicesAbove : slices.toNat ≤ heapBase.toNat)
    (prologue : pl.toNat + 136 ≤ slices.toNat)
    (inHeader : w.toNat < pl.toNat + 136)
    (tail : (evaluateHOLFiniteState (evaluateHOLFiniteState t wdSliceLoop).2
        (actualPayloadHeaderAt 47)).2.memory w = (evaluateHOLFiniteState t wdSliceLoop).2.memory w) :
    (evaluateHOLFiniteState t (actualPayloadHeaderAt 46)).2.memory w = t.memory w := by
  have arrayCell := wd_slice_array_cell t pl input wd nwd entry
  have countBound := wd_signed_count_bound nwd withdrawals balance countVal within
  exact payloadHeader46_window_geometry_budget t nwd pl slices heapBase w (pl + 48#64) (input + wd) size
    rfl endEq sizeEq alSlices alSize cap atCounter atNwd atPl freshE atSlices atHeap code countBound
    slicesAbove (wd_read_below_arena pl slices (pl + 48#64) prologue rfl)
    (wd_watched_below_arena pl slices w prologue inHeader) arrayCell.2 arrayCell.1 tail

#print axioms payloadHeader46_window_from_decoder
#print axioms wd_signed_count_bound
#print axioms wd_slice_count_cell
#print axioms wd_slice_array_cell
end InitECandidate.Runtime
