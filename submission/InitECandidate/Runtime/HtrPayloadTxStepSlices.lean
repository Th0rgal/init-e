import InitECandidate.Runtime.HtrPayloadTxStepMemory
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem htrPayload_tx_step_preserves_slices {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer accelerator zeroHashes chunk array index roots heap input inputLength : BitVec 64) (count : Nat)
    (arrayLocal : state.locals.lookup (ofString "txs") = some (.val (.word array)))
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (rootsLocal : state.locals.lookup (ofString "roots") = some (.val (.word roots)))
    (slices : RlpSliceInputPrefix state array input inputLength count)
    (inside : index.toNat < count) (small : inputLength.toNat ≤ 134217712)
    (arrayRoots : array.toNat + count * 16 ≤ roots.toNat)
    (arrayHeap : array.toNat + count * 16 ≤ heap.toNat)
    (rootsAligned : roots.toNat % 8 = 0) (rootsFits : roots.toNat + count * 32 ≤ 33806089496)
    (atPointer : state.globals.lookup (ofString "sha_st") = some (.val (.word pointer)))
    (atAccel : state.globals.lookup (ofString "sha_accel") = some (.val (.word accelerator)))
    (atChunk : state.globals.lookup (ofString "ssz_len_chunk") = some (.val (.word chunk)))
    (chunkAligned : chunk.toNat % 8 = 0) (chunkFits : chunk.toNat + 32 ≤ array.toNat)
    (atZero : state.globals.lookup (ofString "zero_hashes") = some (.val (.word zeroHashes)))
    (hh : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (heapAligned : heap.toNat % 8 = 0) (heapFits : heap.toNat ≤ 33806089496)
    (accelAligned : accelerator.toNat % 8 = 0)
    (accelFits : accelerator.toNat + 96 ≤ array.toNat) (pointerFits : pointer.toNat + 64 ≤ array.toNat)
    (code : state.code = originalRuntimeCode) (budget : htrPbytesBodyCost + 1 ≤ state.clock)
    (run : evaluateHOLFiniteState state htrPayloadTxStep = (none,post)) :
    RlpSliceInputPrefix post array input inputLength count := by
  obtain ⟨p,n,current⟩ := slices index inside
  have lengthBound := (current.length_bound state array index p n input inputLength).trans small
  have cellFrame (address : BitVec 64) (lo : array.toNat ≤ address.toNat)
      (hi : address.toNat < array.toNat + count * 16) : post.memory address = state.memory address := by
    exact htrPayload_tx_step_normal_memory state post pointer accelerator zeroHashes chunk array index p n roots heap address count
      arrayLocal indexLocal rootsLocal current.readable inside rootsAligned rootsFits (Nat.lt_of_lt_of_le hi arrayRoots)
      atPointer atAccel atChunk chunkAligned (by omega) (Or.inr (by omega)) atZero hh lengthBound
      heapAligned heapFits (Nat.lt_of_lt_of_le hi arrayHeap) accelAligned (by omega) (by omega)
      (Or.inr (by omega)) (Or.inr (by omega)) code budget run
  have metadata := evaluateHOLFiniteState_metadata state htrPayloadTxStep
  rw [run] at metadata
  intro slot slotInside
  obtain ⟨oldPointer,oldLength,entry⟩ := slices slot slotInside
  have offset : (slot * (16#64)).toNat = slot.toNat * 16 := by
    apply BitVec.toNat_mul_of_lt
    change slot.toNat * 16 < 2 ^ 64
    have := roots.isLt
    omega
  have base : (array + slot * (16#64)).toNat = array.toNat + slot.toNat * 16 := by
    rw [BitVec.toNat_add_of_lt (by rw [offset]; have := roots.isLt; omega),offset]
  have last : (array + slot * (16#64) + (8#64)).toNat = array.toNat + slot.toNat * 16 + 8 := by
    rw [BitVec.toNat_add_of_lt (by rw [base]; have := roots.isLt; change _ + 8 < _; omega),base]
    rfl
  exact ⟨oldPointer,oldLength,entry.after_frame state post array slot oldPointer oldLength input inputLength metadata.2.1
    (cellFrame _ (by rw [base]; omega) (by rw [base]; omega))
    (cellFrame _ (by rw [last]; omega) (by rw [last]; omega))⟩

#print axioms htrPayload_tx_step_preserves_slices
end InitECandidate.Runtime
