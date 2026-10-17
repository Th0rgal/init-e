import InitECandidate.Runtime.HashTableArraysHeaderFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- The count may change while the allocation layout and other headers remain fixed. -/
theorem HashTableArraysInvariant.recounted_width {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (keyLength table keys stride capacity used values order orderPos count newCount : BitVec 64) (bits : Nat)
    (invariant : HashTableArraysInvariant keyLength table keys stride capacity used values order orderPos count bits state)
    (header : ∀ offset ∈ ([0,8,16,32,40,48,56,64] : List Nat),
      post.memory (table + BitVec.ofNat 64 offset) = state.memory (table + BitVec.ofNat 64 offset))
    (countCell : post.memory (table + 24) = .word newCount)
    (agreement : newCount.toNat = hashOccupiedCount capacity (hashOccupancyRead post used))
    (room : newCount.toNat < capacity.toNat)
    (code : post.code = state.code)
    (addresses : post.memaddrs = state.memaddrs) :
    HashTableArraysInvariant keyLength table keys stride capacity used values order orderPos newCount bits post := by
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
    cell24 := countCell
    cell32 := (header 32 (by simp)).trans invariant.cell32
    cell40 := (header 40 (by simp)).trans invariant.cell40
    cell48 := (header 48 (by simp)).trans invariant.cell48
    cell56 := (header 56 (by simp)).trans invariant.cell56
    cell64 := (header 64 (by simp)).trans invariant.cell64
    agreement := agreement
    room := room
  }

/-- A one-entry occupancy decrease restores the complete table invariant
once the count header is decremented and all other headers are framed. -/
theorem HashTableArraysInvariant.deleted_frame_width {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (keyLength table keys stride capacity used values order orderPos count : BitVec 64) (bits : Nat)
    (invariant : HashTableArraysInvariant keyLength table keys stride capacity used values order orderPos count bits state)
    (header : ∀ offset ∈ ([0,8,16,32,40,48,56,64] : List Nat),
      post.memory (table + BitVec.ofNat 64 offset) = state.memory (table + BitVec.ofNat 64 offset))
    (countCell : post.memory (table + 24) = .word (count - 1))
    (removed : hashOccupiedCount capacity (hashOccupancyRead post used) + 1 = count.toNat)
    (code : post.code = state.code) (addresses : post.memaddrs = state.memaddrs) :
    HashTableArraysInvariant keyLength table keys stride capacity used values order orderPos (count - 1) bits post := by
  have positive : 0 < count.toNat := by omega
  have subtraction : (count - (1 : BitVec 64)).toNat = count.toNat - 1 := by
    rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by change 1 ≤ count.toNat; omega))]
    rfl
  have room := invariant.room
  exact invariant.recounted_width state post keyLength table keys stride capacity used values order orderPos count (count - 1) bits
    header countCell (by omega) (by omega) code addresses

#print axioms HashTableArraysInvariant.deleted_frame_width
#print axioms HashTableArraysInvariant.recounted_width
end InitECandidate.Runtime
