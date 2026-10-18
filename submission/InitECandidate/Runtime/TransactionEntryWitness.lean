import InitECandidate.Runtime.TransactionDecodeWitness
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Decoder entry needs no existing array or index local: these are installed
by the source declarations before the first transaction field. -/
def transaction_decode_entry_witness {F : Type} (state : PanSemStateFiniteExact 64 F)
    (array count tx kind input inputLength scratch frame heap : BitVec 64) (ceiling : Nat)
    (txLocal : state.locals.lookup (ofString "tx") = some (.val (.word tx)))
    (typeLocal : state.locals.lookup (ofString "t") = some (.val (.word kind)))
    (slices : RlpSliceInputPrefix state array input inputLength count.toNat)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (heapGlobal : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (code : state.code = originalRuntimeCode)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (heapArena : ∀ address : BitVec 64, heap.toNat ≤ address.toNat → address.toNat < 33806089496 → state.memaddrs address)
    (heapBound : heap.toNat ≤ 33806089496) (heapAligned : heap.toNat % 8 = 0)
    (inputBeforeHeap : input.toNat + inputLength.toNat ≤ heap.toNat)
    (arrayBeforeHeap : array.toNat + count.toNat * 16 ≤ heap.toNat) :
    TransactionDecodeWitness
      (setVarHOLFinite (ofString "k") (.val (.word 0)) (setVarHOLFinite (ofString "arr") (.val (.word array)) state))
      array count tx kind input inputLength scratch frame ceiling := by
  refine ⟨0,heap,?_,?_,?_,?_,Nat.zero_le _,?_,scratchGlobal,frameGlobal,heapGlobal,code,
    arena,heapArena,heapBound,heapAligned,inputBeforeHeap,arrayBeforeHeap⟩
  · simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "k" ≠ ofString "arr" by decide]
  · simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "k" ≠ ofString "tx" by decide,
      show ofString "arr" ≠ ofString "tx" by decide] using txLocal
  · simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "k" ≠ ofString "t" by decide,
      show ofString "arr" ≠ ofString "t" by decide] using typeLocal
  · simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  · intro slot bounded
    obtain ⟨p,n,item⟩ := slices slot bounded
    exact ⟨p,n,item.after_frame state _ array slot p n input inputLength rfl rfl rfl⟩

#print axioms transaction_decode_entry_witness
end InitECandidate.Runtime
