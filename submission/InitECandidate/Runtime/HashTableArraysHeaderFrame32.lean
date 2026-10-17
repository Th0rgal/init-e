import InitECandidate.Runtime.HashDeleteCopyBounds32
import InitECandidate.Runtime.MemcpyIntervalFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- Header and occupancy frames suffice to retain the table layout even when key/value arrays change. -/
theorem HashTableArraysInvariant32.framed {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (table keys stride capacity used values order orderPos count : BitVec 64) (bits : Nat)
    (invariant : HashTableArraysInvariant32 table keys stride capacity used values order orderPos count bits state)
    (header : ∀ offset ∈ ([0,8,16,24,32,40,48,56,64] : List Nat),
      post.memory (table + BitVec.ofNat 64 offset) = state.memory (table + BitVec.ofNat 64 offset))
    (reads : hashOccupancyRead post used = hashOccupancyRead state used)
    (code : post.code = state.code)
    (addresses : post.memaddrs = state.memaddrs) :
    HashTableArraysInvariant32 table keys stride capacity used values order orderPos count bits post := by
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
    agreement := by rw [reads]; exact invariant.agreement
    room := invariant.room
  }

/-- All header cells precede the copied key interval, including byte-aligned writes. -/
theorem HashTableArraysInvariant32.key_copy_header_separate {F : Type}
    (state : PanSemStateFiniteExact 64 F)
    (table keys stride capacity used values order orderPos count hole : BitVec 64) (bits : Nat)
    (invariant : HashTableArraysInvariant32 table keys stride capacity used values order orderPos count bits state)
    (inside : hole.toNat < capacity.toNat) :
    ∀ headerOffset : Nat, headerOffset ≤ 64 → ∀ offset : Nat, offset < 32 →
      table + BitVec.ofNat 64 headerOffset ≠ keys + hole * stride + BitVec.ofNat 64 offset ∧
      table + BitVec.ofNat 64 headerOffset ≠ panByteAlignHOL (keys + hole * stride + BitVec.ofNat 64 offset) := by
  have bounds := invariant.delete_copy_bounds state table keys stride capacity used values order orderPos count hole hole bits inside inside
  have hk := invariant.headerKeys
  have ku := invariant.keysBefore
  have uo := invariant.usedBefore
  have oo := invariant.orderBefore
  have bounded := invariant.endBound
  have keyAddress := (hashFind_slot_address keys hole stride capacity inside (by omega) invariant.keysAligned invariant.strideAligned).1
  intro headerOffset small offset inRange
  have natural : (BitVec.ofNat 64 headerOffset).toNat = headerOffset := by
    change headerOffset % 2 ^ 64 = headerOffset
    exact Nat.mod_eq_of_lt (by omega)
  have headerAddress : (table + BitVec.ofNat 64 headerOffset).toNat = table.toNat + headerOffset := by
    rw [BitVec.toNat_add_of_lt (by rw [natural]; omega),natural]
  exact memcpy_interval_separate (keys + hole * stride) 32 (table + BitVec.ofNat 64 headerOffset)
    bounds.aligned bounds.small (Or.inl (by rw [headerAddress,keyAddress]; omega)) offset inRange

#print axioms HashTableArraysInvariant32.key_copy_header_separate

#print axioms HashTableArraysInvariant32.framed
end InitECandidate.Runtime
