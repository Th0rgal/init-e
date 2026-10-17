import InitECandidate.Runtime.HashTableReady
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- The generic mixed-operation invariant specializes exactly to the checked 32-byte invariant. -/
theorem hashTableReady_32_iff {F : Type}
    (table keys stride capacity used values order orderPos items pointer : BitVec 64) (bits : Nat)
    (state : PanSemStateFiniteExact 64 F) :
    HashTableReady 32 table keys stride capacity used values order orderPos items bits pointer state ↔
    HashTableReady32 table keys stride capacity used values order orderPos items bits pointer state := by
  constructor
  · intro ready
    exact ⟨⟨(hashTableArraysInvariant_32_iff table keys stride capacity used values order orderPos items bits state).mp ready.live.arrays,
      ready.live.entries,ready.live.frontier⟩,ready.valuesWord,ready.reverse,ready.linked,ready.ordering⟩
  · intro ready
    exact ⟨⟨(hashTableArraysInvariant_32_iff table keys stride capacity used values order orderPos items bits state).mpr ready.live.arrays,
      ready.live.entries,ready.live.frontier⟩,ready.valuesWord,ready.reverse,ready.linked,ready.ordering⟩

#print axioms hashTableReady_32_iff
end InitECandidate.Runtime
