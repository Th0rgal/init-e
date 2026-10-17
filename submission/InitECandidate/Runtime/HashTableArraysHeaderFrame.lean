import InitECandidate.Runtime.HashTableArraysInvariant
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- Header and occupancy frames retain arbitrary-key-width table geometry. -/
theorem HashTableArraysInvariant.framed {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (keyLength table keys stride capacity used values order orderPos count : BitVec 64) (bits : Nat)
    (invariant : HashTableArraysInvariant keyLength table keys stride capacity used values order orderPos count bits state)
    (header : ∀ offset ∈ ([0,8,16,24,32,40,48,56,64] : List Nat),
      post.memory (table + BitVec.ofNat 64 offset) = state.memory (table + BitVec.ofNat 64 offset))
    (reads : ∀ slot : BitVec 64, slot.toNat < capacity.toNat → hashOccupancyRead post used slot = hashOccupancyRead state used slot)
    (code : post.code = state.code)
    (addresses : post.memaddrs = state.memaddrs) :
    HashTableArraysInvariant keyLength table keys stride capacity used values order orderPos count bits post := by
  exact {
    code := code.trans invariant.code
    power := invariant.power
    keysAligned := invariant.keysAligned
    strideAligned := invariant.strideAligned
    valuesAligned := invariant.valuesAligned
    usedAligned := invariant.usedAligned
    orderAligned := invariant.orderAligned
    orderPosAligned := invariant.orderPosAligned
    headerKeys := invariant.headerKeys
    headerValues := invariant.headerValues
    keysBefore := invariant.keysBefore
    valuesBefore := invariant.valuesBefore
    usedBefore := invariant.usedBefore
    orderBefore := invariant.orderBefore
    endBound := invariant.endBound
    fits := invariant.fits
    domain := by rw [addresses]; exact invariant.domain
    cell0 := (header 0 (by simp)).trans invariant.cell0
    cell8 := (header 8 (by simp)).trans invariant.cell8
    cell16 := (header 16 (by simp)).trans invariant.cell16
    cell24 := (header 24 (by simp)).trans invariant.cell24
    cell32 := (header 32 (by simp)).trans invariant.cell32
    cell40 := (header 40 (by simp)).trans invariant.cell40
    cell48 := (header 48 (by simp)).trans invariant.cell48
    cell56 := (header 56 (by simp)).trans invariant.cell56
    cell64 := (header 64 (by simp)).trans invariant.cell64
    agreement := by rw [hashOccupiedCount_congr capacity _ _ reads]; exact invariant.agreement
    room := invariant.room
  }


#print axioms HashTableArraysInvariant.framed
end InitECandidate.Runtime
