import InitECandidate.Runtime.VersionedHashesLocalsInvariant
import InitECandidate.Runtime.TransactionHeapBudget
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Concrete slices and actual heap-cap invariants, without future allocation reserves. -/
structure VersionedHashesGuardedRuntimeInvariant {F : Type} (state : PanSemStateFiniteExact 64 F)
    (count array vh input inputLength scratch frame : BitVec 64) (ceiling : Nat) where
  locals : VersionedHashesLocalsInvariant state count array vh
  slices : RlpSliceInputPrefix state array input inputLength count.toNat
  heap : BitVec 64
  heapGlobal : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap))
  scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch))
  frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame))
  heapAligned : heap.toNat % 8 = 0
  heapBound : heap.toNat ≤ 33806089496
  arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address
  heapArena : ∀ address : BitVec 64, heap.toNat ≤ address.toNat → address.toNat < 33806089496 → state.memaddrs address
  inputBeforeHeap : input.toNat + inputLength.toNat ≤ heap.toNat
  arrayBeforeHeap : array.toNat + count.toNat * 16 ≤ heap.toNat
  heapAbove : ceiling ≤ heap.toNat

def VersionedHashesGuardedRuntimeInvariant.decClock {F : Type} (state : PanSemStateFiniteExact 64 F)
    (count array vh input inputLength scratch frame : BitVec 64) (ceiling : Nat)
    (valid : VersionedHashesGuardedRuntimeInvariant state count array vh input inputLength scratch frame ceiling) :
    VersionedHashesGuardedRuntimeInvariant (decClockHOLFinite state) count array vh input inputLength scratch frame ceiling := by
  refine {valid with locals := valid.locals.decClock state count array vh, slices := ?_}
  intro slot inside
  obtain ⟨p,n,item⟩ := valid.slices slot inside
  exact ⟨p,n,item.after_frame state _ array slot p n input inputLength rfl rfl rfl⟩

#print axioms VersionedHashesGuardedRuntimeInvariant.decClock
end InitECandidate.Runtime
