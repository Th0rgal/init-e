import InitECandidate.Runtime.VersionedHashesRuntimeLoopBound
set_option maxRecDepth 100000
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem source_versioned_hashes_initialization : versionedHashesAt 5 =
    .dec (ofString "k") .one (.const 0) (.dec (ofString "i") .one (.const 0) (versionedHashesAt 7)) := by
  simp only [versionedHashesAt,authorizationNext,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

def versionedHashesInitialState {F : Type} (state : PanSemStateFiniteExact 64 F) : PanSemStateFiniteExact 64 F :=
  setVarHOLFinite (ofString "i") (.val (.word 0)) (setVarHOLFinite (ofString "k") (.val (.word 0)) state)

def versioned_hashes_initial_runtime_invariant {F : Type} (state : PanSemStateFiniteExact 64 F)
    (count array vh input inputLength scratch frame heap : BitVec 64) (ceiling : Nat)
    (countLocal : state.locals.lookup (ofString "ntx") = some (.val (.word count)))
    (arrayLocal : state.locals.lookup (ofString "txs") = some (.val (.word array)))
    (vhLocal : state.locals.lookup (ofString "vh") = some (.val (.word vh)))
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
    (capReserve : heap.toNat + count.toNat * transactionHeapGrowth inputLength.toNat + transactionHeapWorkspace inputLength.toNat ≤ 33806089496) :
    VersionedHashesRuntimeInvariant (versionedHashesInitialState state) count array vh input inputLength scratch frame ceiling := by
  let ready := versionedHashesInitialState state
  have other : ∀ name, name ≠ ofString "i" → name ≠ ofString "k" → ready.locals.lookup name = state.locals.lookup name := by
    intro name notI notK
    simp [ready,versionedHashesInitialState,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm notI,Ne.symm notK]
  have atIndex : ready.locals.lookup (ofString "i") = some (.val (.word 0)) := by
    simp [ready,versionedHashesInitialState,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have atCursor : ready.locals.lookup (ofString "k") = some (.val (.word 0)) := by
    simp [ready,versionedHashesInitialState,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "i" ≠ ofString "k" by decide]
  have locals : VersionedHashesLocalsInvariant ready count array vh :=
    ⟨⟨0,atIndex,(other _ (by decide) (by decide)).trans countLocal,by simp,small⟩,
      0,atCursor,(other _ (by decide) (by decide)).trans arrayLocal,(other _ (by decide) (by decide)).trans vhLocal,code⟩
  have rank : versionedHashesRank count ready = count.toNat := by simp [versionedHashesRank,atIndex]
  refine ⟨locals,?_,heap,heapGlobal,scratchGlobal,frameGlobal,aligned,heapBound,arena,heapArena,inputBeforeHeap,arrayBeforeHeap,?_,?_⟩
  · intro slot inside
    obtain ⟨p,n,item⟩ := slices slot inside
    exact ⟨p,n,item.after_frame state ready array slot p n input inputLength rfl rfl rfl⟩
  · rw [rank]; exact frameReserve
  · rw [rank]; exact capReserve

#print axioms versioned_hashes_initial_runtime_invariant
end InitECandidate.Runtime
