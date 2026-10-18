import InitECandidate.Runtime.VersionedHashesEntryLoads
import InitECandidate.Runtime.VersionedHashesInitializedBound
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem evaluate_versioned_hashes_body_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (count array vh input inputLength scratch frame heap : BitVec 64) (ceiling : Nat)
    (si payload hashCount : BitVec 64)
    (siLocal : state.locals.lookup (ofString "si") = some (.val (.word si)))
    (payloadDomain : state.memaddrs (si + 0)) (payloadCell : state.memory (si + 0) = .word payload)
    (arrayDomain : state.memaddrs (payload + 32)) (arrayCell : state.memory (payload + 32) = .word array)
    (countDomain : state.memaddrs (payload + 40)) (countCell : state.memory (payload + 40) = .word count)
    (vhDomain : state.memaddrs (si + 8)) (vhCell : state.memory (si + 8) = .word vh)
    (hashCountDomain : state.memaddrs (si + 16)) (hashCountCell : state.memory (si + 16) = .word hashCount)
    (small : count.toNat < 2^63) (code : state.code = originalRuntimeCode)
    (slices : RlpSliceInputPrefix state array input inputLength count.toNat)
    (heapGlobal : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (aligned : heap.toNat % 8 = 0) (heapBound : heap.toNat ≤ 33806089496)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (heapArena : ∀ address : BitVec 64, heap.toNat ≤ address.toNat → address.toNat < 33806089496 → state.memaddrs address)
    (inputBeforeHeap : input.toNat + inputLength.toNat ≤ heap.toNat)
    (arrayBeforeHeap : array.toNat + count.toNat * 16 ≤ heap.toNat)
    (frameReserve : heap.toNat + count.toNat * transactionHeapGrowth inputLength.toNat + transactionHeapWorkspace inputLength.toNat ≤ frame.toNat)
    (capReserve : heap.toNat + count.toNat * transactionHeapGrowth inputLength.toNat + transactionHeapWorkspace inputLength.toNat ≤ 33806089496)
    (inputLimit : Nat) (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat) (scratchBelow : scratch.toNat ≤ ceiling)
    (countLimit : inputLimit * 120 < 2^64)
    (budget : count.toNat * (versionedHashesTransactionStepCost inputLength.toNat + 1) ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_is_valid_versioned_hashes)
    state.clock ≤ evaluated.2.clock + count.toNat * (versionedHashesTransactionStepCost inputLength.toNat + 1) ∧
      evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  let ready := versionedHashesLoadedState state payload array count vh hashCount
  have atntx : ready.locals.lookup (ofString "ntx") = some (.val (.word count)) := by
    simp [ready,versionedHashesLoadedState,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "nvh" ≠ ofString "ntx" by decide,show ofString "vh" ≠ ofString "ntx" by decide]
  have attxs : ready.locals.lookup (ofString "txs") = some (.val (.word array)) := by
    simp [ready,versionedHashesLoadedState,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "nvh" ≠ ofString "txs" by decide,show ofString "vh" ≠ ofString "txs" by decide,show ofString "ntx" ≠ ofString "txs" by decide]
  have atvh : ready.locals.lookup (ofString "vh") = some (.val (.word vh)) := by
    simp [ready,versionedHashesLoadedState,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "nvh" ≠ ofString "vh" by decide]
  have readySlices : RlpSliceInputPrefix ready array input inputLength count.toNat := by
    intro slot inside
    obtain ⟨p,n,item⟩ := slices slot inside
    exact ⟨p,n,item.after_frame state ready array slot p n input inputLength rfl rfl rfl⟩
  have bounded := evaluate_versioned_hashes_initialized_bounded ready count array vh input inputLength scratch frame heap ceiling
    atntx attxs atvh small code readySlices heapGlobal scratchGlobal frameGlobal aligned heapBound arena heapArena
    inputBeforeHeap arrayBeforeHeap frameReserve capReserve inputLimit inputBound limitBound orderedFrame framePositive scratchBelow countLimit budget
  have entry := versioned_hashes_entry_loads_clock state si payload array count vh hashCount siLocal payloadDomain payloadCell
    arrayDomain arrayCell countDomain countCell vhDomain vhCell hashCountDomain hashCountCell
  dsimp only at bounded ⊢
  rw [entry.1,entry.2]
  exact bounded

#print axioms evaluate_versioned_hashes_body_bounded
end InitECandidate.Runtime
