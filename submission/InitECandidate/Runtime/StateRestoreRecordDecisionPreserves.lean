import InitECandidate.Runtime.StateRestoreRecordSetPreserves
import InitECandidate.Runtime.StateRestoreRecordDeletePreserves
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Both original undo branches preserve a complete table and the journal rank. -/
theorem HashTableReady.restore_record_decision_preserves {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keyLength table pointer keys stride capacity used values order orderPos items key record present value : BitVec 64) (bits : Nat)
    (supported : keyLength = 20 ∨ keyLength = 32 ∨ keyLength = 52)
    (ready : HashTableReady keyLength table keys stride capacity used values order orderPos items bits pointer state)
    (strideBound : stride.toNat ≤ 56) (capacityLarge : 1 < capacity.toNat)
    (safePlan : AllocationPlanSafe pointer (htabGrowAllocationSizes capacity stride))
    (ticks : 2 ^ 72 ≤ state.clock)
    (domain : ∀ address : BitVec 64, table.toNat ≤ address.toNat → address.toNat < 33806089496 → state.memaddrs address)
    (t : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (k : state.locals.lookup (ofString "key") = some (.val (.word key)))
    (r : state.locals.lookup (ofString "r") = some (.val (.word record)))
    (presentDomain : state.memaddrs (record + 16)) (presentCell : state.memory (record + 16) = .word present)
    (valueDomain : state.memaddrs (record + 24)) (valueCell : state.memory (record + 24) = .word value)
    (keyAligned : key.toNat % 8 = 0)
    (keyWords : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (keyBytes : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset))) :
    ∃ post, evaluateHOLFiniteState state stateRestoreRecordDecision = (none,post) ∧
      (∃ nextPointer nextKeys nextCapacity nextUsed nextValues nextOrder nextOrderPos nextItems nextBits,
        HashTableReady keyLength table nextKeys stride nextCapacity nextUsed nextValues nextOrder nextOrderPos nextItems nextBits nextPointer post) ∧
      stateRestoreRank post = stateRestoreRank state ∧
      state.clock ≤ post.clock + 2 ^ 72 ∧ post.clock ≤ state.clock := by
  classical
  by_cases zero : present = 0
  · have cell : state.memory (record + 16) = .word 0 := by simpa [zero] using presentCell
    obtain ⟨post,run,⟨remaining,_,postReady⟩,rank,cost,clock⟩ := ready.restore_record_delete_preserves state keyLength table pointer keys stride capacity used values order orderPos items key record bits supported
      strideBound capacityLarge ticks domain t k r presentDomain cell keyAligned keyWords keyBytes
    exact ⟨post,run,⟨pointer,keys,capacity,used,values,order,orderPos,remaining,bits,postReady⟩,rank,cost,clock⟩
  · have capacityBound : capacity.toNat ≤ 33806089496 := by
      have := ready.live.arrays.usedBefore
      have := ready.live.arrays.orderBefore
      have := ready.live.arrays.endBound
      omega
    have headerBefore : table.toNat + 72 ≤ pointer.toNat := by
      have := ready.live.arrays.headerKeys
      have := ready.live.arrays.keysBefore
      have := ready.live.arrays.usedBefore
      have := ready.live.arrays.orderBefore
      have := ready.live.frontier.allocated
      omega
    obtain ⟨_,_,_,_,_,_,_,_,_,_,_,limit⟩ := htabGrow_array_layout_from_safe_plan table pointer capacity stride strideBound ready.live.frontier.aligned headerBefore ready.live.frontier.bounded capacityBound safePlan
    have growthDomain : ∀ address : BitVec 64, table.toNat ≤ address.toNat → address.toNat < (htabGrowOrderPos pointer capacity stride).toNat + (capacity * 2).toNat * 8 → state.memaddrs address := by
      intro address lower upper
      exact domain address lower (by omega)
    obtain ⟨post,run,cases,rank,cost,clock⟩ := ready.restore_record_set_preserves state keyLength table pointer keys stride capacity used values order orderPos items key record present value bits supported
      strideBound capacityLarge ticks growthDomain t k r presentDomain presentCell zero valueDomain valueCell safePlan keyAligned keyWords keyBytes
    refine ⟨post,run,?_,rank,cost,clock⟩
    rcases cases with original | grown
    · obtain ⟨remaining,_,postReady⟩ := original
      exact ⟨pointer,keys,capacity,used,values,order,orderPos,remaining,bits,postReady⟩
    · exact ⟨_,_,_,_,_,_,_,_,_,grown⟩

#print axioms HashTableReady.restore_record_decision_preserves
end InitECandidate.Runtime
