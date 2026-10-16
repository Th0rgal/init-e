import InitECandidate.Runtime.HashOrderEntriesBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- Stable old-array facts retained while growth reinserts into fresh arrays.
The order-entry bound is a memory invariant, not an evaluator assumption. -/
structure HashGrowOldArrays {F : Type} (table keys stride values order capacity items : BitVec 64)
    (frontier : Nat) (state : PanSemStateFiniteExact 64 F) : Prop where
  keysAligned : keys.toNat % 8 = 0
  valuesAligned : values.toNat % 8 = 0
  orderAligned : order.toNat % 8 = 0
  keyBound : keys.toNat + capacity.toNat * stride.toNat ≤ 33806089496
  valueBound : values.toNat + capacity.toNat * 8 ≤ 33806089496
  orderBound : order.toNat + capacity.toNat * 8 ≤ 33806089496
  headerOrder : table.toNat + 72 ≤ order.toNat
  orderEnd : order.toNat + capacity.toNat * 8 ≤ frontier
  frontierBound : frontier ≤ 33806089496
  itemsBound : items.toNat ≤ capacity.toNat
  keyDomain : ∀ address : BitVec 64, keys.toNat ≤ address.toNat →
    address.toNat < keys.toNat + capacity.toNat * stride.toNat → state.memaddrs address
  valueDomain : ∀ address : BitVec 64, values.toNat ≤ address.toNat →
    address.toNat < values.toNat + capacity.toNat * 8 → state.memaddrs address
  orderDomain : ∀ address : BitVec 64, order.toNat ≤ address.toNat →
    address.toNat < order.toNat + capacity.toNat * 8 → state.memaddrs address
  entries : HashOrderEntriesBound order capacity items state

/-- The actual rehash body's earlier-region memory guarantee preserves every
old order entry; unchanged domains retain all old key/value reads. -/
theorem HashGrowOldArrays.preserved {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (table keys stride values order capacity items : BitVec 64) (frontier : Nat)
    (old : HashGrowOldArrays table keys stride values order capacity items frontier state)
    (addresses : post.memaddrs = state.memaddrs)
    (frame : ∀ watched : BitVec 64, table.toNat + 72 ≤ watched.toNat → watched.toNat < frontier →
      post.memory watched = state.memory watched) :
    HashGrowOldArrays table keys stride values order capacity items frontier post := by
  exact {
    keysAligned := old.keysAligned
    valuesAligned := old.valuesAligned
    orderAligned := old.orderAligned
    keyBound := old.keyBound
    valueBound := old.valueBound
    orderBound := old.orderBound
    headerOrder := old.headerOrder
    orderEnd := old.orderEnd
    frontierBound := old.frontierBound
    itemsBound := old.itemsBound
    keyDomain := by rw [addresses]; exact old.keyDomain
    valueDomain := by rw [addresses]; exact old.valueDomain
    orderDomain := by rw [addresses]; exact old.orderDomain
    entries := old.entries.preserved state post table order capacity items frontier old.orderAligned old.headerOrder
      old.orderEnd old.frontierBound old.itemsBound frame
  }

#print axioms HashGrowOldArrays.preserved
end InitECandidate.Runtime
