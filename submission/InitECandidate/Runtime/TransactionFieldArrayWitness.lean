import InitECandidate.Runtime.TransactionFieldArrayGeometry
import InitECandidate.Runtime.TransactionDecodeWitness
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Reconstruct the shared field-decoder premises from the concrete header and
field-array allocations, without assuming an unexplained heap endpoint. -/
theorem transaction_field_array_decode_witness {F : Type} (state : PanSemStateFiniteExact 64 F)
    (tx count kind index input inputLength scratch frame : BitVec 64) (ceiling : Nat)
    (arrayLocal : state.locals.lookup (ofString "arr") = some (.val (.word (allocationEnd tx 400))))
    (txLocal : state.locals.lookup (ofString "tx") = some (.val (.word tx)))
    (typeLocal : state.locals.lookup (ofString "t") = some (.val (.word kind)))
    (indexLocal : state.locals.lookup (ofString "k") = some (.val (.word index)))
    (inside : index.toNat ≤ count.toNat)
    (slices : RlpSliceInputPrefix state (allocationEnd tx 400) input inputLength count.toNat)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (heapGlobal : state.globals.lookup (ofString "heap_ptr") = some (.val (.word (allocationEnd (allocationEnd tx 400) (count * 16)))))
    (code : state.code = originalRuntimeCode)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (heapArena : ∀ address : BitVec 64, tx.toNat ≤ address.toNat → address.toNat < 33806089496 → state.memaddrs address)
    (space : tx.toNat + 400 + count.toNat * 16 ≤ 33806089496)
    (aligned : tx.toNat % 8 = 0)
    (inputBeforeTx : input.toNat + inputLength.toNat ≤ tx.toNat) :
    ∃ valid : TransactionDecodeWitness state (allocationEnd tx 400) count tx kind input inputLength scratch frame ceiling,
      valid.index = index ∧ valid.heap = allocationEnd (allocationEnd tx 400) (count * 16) ∧
      valid.heap.toNat = tx.toNat + 400 + count.toNat * 16 := by
  obtain ⟨header,_,endpoint,heapAligned,heapBound⟩ := transaction_field_array_heap_geometry tx count space aligned
  let valid : TransactionDecodeWitness state (allocationEnd tx 400) count tx kind input inputLength scratch frame ceiling :=
    { index := index
      heap := allocationEnd (allocationEnd tx 400) (count * 16)
      arrayLocal := arrayLocal
      txLocal := txLocal
      typeLocal := typeLocal
      indexLocal := indexLocal
      indexBound := inside
      slices := slices
      scratchGlobal := scratchGlobal
      frameGlobal := frameGlobal
      heapGlobal := heapGlobal
      code := code
      arena := arena
      heapArena := by
        intro address low high
        apply heapArena address _ high
        rw [endpoint] at low
        omega
      heapBound := heapBound
      heapAligned := heapAligned
      inputBeforeHeap := by rw [endpoint]; omega
      arrayBeforeHeap := by rw [header,endpoint] }
  exact ⟨valid,rfl,rfl,endpoint⟩

#print axioms transaction_field_array_decode_witness
end InitECandidate.Runtime
